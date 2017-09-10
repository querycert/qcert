(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Section NRA.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.

  (** Nested Relational Algebra *)

  (** By convention, "static" parameters come first, followed by
     dependent operators. This allows for instanciation on those
     parameters *)

  Context {fruntime:foreign_runtime}.
  
  Inductive nra : Set :=
  | AID : nra
  | AConst : data -> nra
  | ABinop : binary_op -> nra -> nra -> nra
  | AUnop : unary_op -> nra -> nra
  | AMap : nra -> nra -> nra
  | AMapConcat : nra -> nra -> nra
  | AProduct : nra -> nra -> nra
  | ASelect : nra -> nra -> nra
  | ADefault : nra -> nra -> nra
  | AEither : nra -> nra -> nra
  | AEitherConcat : nra -> nra -> nra
  | AApp : nra -> nra -> nra
  | AGetConstant : string -> nra
  .

  Global Instance nra_eqdec : EqDec nra eq.
  Proof.
    change (forall x y : nra,  {x = y} + {x <> y}).
    decide equality;
    try solve [apply binary_op_eqdec | apply unary_op_eqdec | apply data_eqdec | apply string_eqdec].
  Qed.

  (** NRA Semantics *)

  Context (h:list(string*string)).
  Section Semantics.
    Context (constant_env:list (string*data)).
  
    Fixpoint nra_eval (op:nra) (x:data) : option data :=
      match op with
      | AID => Some x
      | AConst rd => Some (normalize_data h rd)
      | ABinop bop op1 op2 =>
        olift2 (fun d1 d2 => binary_op_eval h bop d1 d2) (nra_eval op1 x) (nra_eval op2 x)
      | AUnop uop op1 =>
        olift (fun d1 => unary_op_eval h uop d1) (nra_eval op1 x)
      | AMap op1 op2 =>
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (nra_eval op1) c1)) d
        in olift aux_map (nra_eval op2 x)
      | AMapConcat op1 op2 =>
        let aux_mapconcat d :=
            lift_oncoll (fun c1 => lift dcoll (rmap_concat (nra_eval op1) c1)) d
        in olift aux_mapconcat (nra_eval op2 x)
      | AProduct op1 op2 =>
        (* Note: (fun y => nra_eval op2 x) does not depend on input,
           but we still use a nested loop and delay op2 evaluation so it does not
           fail in case the op1 operand is an empty collection -- this makes sure
           to align the semantics with the NNRC version. - Jerome *)
        let aux_product d :=
            lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => nra_eval op2 x) c1)) d
        in olift aux_product (nra_eval op1 x)
      | ASelect op1 op2 =>
        let pred x' :=
            match nra_eval op1 x' with
              | Some (dbool b) => Some b
              | _ => None
            end
        in
        let aux_select d :=
            lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
        in
        olift aux_select (nra_eval op2 x)
      | ADefault op1 op2 =>
        olift (fun d1 => match d1 with
                           | dcoll nil => nra_eval op2 x
                           | _ => Some d1
                         end) (nra_eval op1 x)
      | AEither opl opr =>
        match x with
          | dleft dl => nra_eval opl dl
          | dright dr => nra_eval opr dr
          | _ => None
        end
      | AEitherConcat op1 op2 =>
        match nra_eval op1 x, nra_eval op2 x with
          | Some (dleft (drec l)), Some (drec t)  =>
            Some (dleft (drec (rec_concat_sort l t)))
          | Some (dright (drec r)), Some (drec t)  =>
            Some (dright (drec (rec_concat_sort r t)))
          | _, _ => None
        end
      | AApp op1 op2 =>
        olift (fun d => (nra_eval op1 d)) (nra_eval op2 x)
      | AGetConstant s => edot constant_env s
    end.

    Lemma data_normalized_orecconcat {x y z}:
      orecconcat x y = Some z ->
      data_normalized h x -> data_normalized h y ->
      data_normalized h z.
    Proof.
      destruct x; simpl; try discriminate.
      destruct y; simpl; try discriminate.
      inversion 1; subst.
      apply data_normalized_rec_concat_sort; trivial.
    Qed.

    (* evaluation preserves normalization *)
    Lemma nra_eval_normalized {op:nra} {d:data} {o} :
      Forall (fun x => data_normalized h (snd x)) constant_env ->
      nra_eval op d = Some o ->
      data_normalized h d ->
      data_normalized h o.
    Proof.
      intro HconstNorm.
      revert d o.
      induction op; simpl.
      - inversion 1; subst; trivial.
      - inversion 1; subst; intros.
        apply normalize_normalizes.
      - intros.
        specialize (IHop1 d).
        specialize (IHop2 d).
        destruct (nra_eval op1 d); simpl in *; try discriminate.
        destruct (nra_eval op2 d); simpl in *; try discriminate.
        apply (binary_op_eval_normalized h) in H; eauto.
      - intros.
        specialize (IHop d).
        destruct (nra_eval op d); simpl in *; try discriminate.
        apply unary_op_eval_normalized in H; eauto.
      - intros;
          specialize (IHop2 d);
          destruct (nra_eval op2 d); simpl in *; try discriminate;
            specialize (IHop2 _ (eq_refl _) H0).
        destruct d0; simpl in *; try discriminate.
        apply some_lift in H; destruct H; subst.
        constructor.
        inversion IHop2; subst.
        apply (rmap_Forall e H1); eauto.
      - intros;
          specialize (IHop2 d);
          destruct (nra_eval op2 d); simpl in *; try discriminate;
            specialize (IHop2 _ (eq_refl _) H0).
        destruct d0; simpl in *; try discriminate.
        apply some_lift in H; destruct H; subst.
        constructor.
        inversion IHop2; subst.
        unfold rmap_concat in *.
        apply (oflat_map_Forall e H1); intros.
        specialize (IHop1 x0).
        unfold oomap_concat in H.
        match_destr_in H.
        specialize (IHop1 _ (eq_refl _) H2).
        unfold omap_concat in H.
        match_destr_in H.
        inversion IHop1; subst.
        apply (rmap_Forall H H4); intros.
        eapply (data_normalized_orecconcat H3); trivial.
      -  intros;
           specialize (IHop1 d);
           destruct (nra_eval op1 d); simpl in *; try discriminate.
         specialize (IHop1 _ (eq_refl _) H0).
         destruct d0; simpl in *; try discriminate.
         apply some_lift in H; destruct H; subst.
         constructor.
         inversion IHop1; subst.
         unfold rmap_concat in *.
         apply (oflat_map_Forall e H1); intros.
         specialize (IHop2 d).
         unfold oomap_concat in H.
         match_destr_in H.
         specialize (IHop2 _ (eq_refl _) H0).
         unfold omap_concat in H.
         match_destr_in H.
         inversion IHop2; subst.
         apply (rmap_Forall H H4); intros.
         eapply (data_normalized_orecconcat H3); trivial.
      - intros;
          specialize (IHop2 d);
          destruct (nra_eval op2 d); simpl in *; try discriminate;
            specialize (IHop2 _ (eq_refl _) H0).
        destruct d0; simpl in *; try discriminate.
        apply some_lift in H; destruct H; subst.      
        constructor.
        inversion IHop2; subst.
        unfold rmap_concat in *.
        apply (lift_filter_Forall e H1).
      - intros;
          specialize (IHop1 d);
          destruct (nra_eval op1 d); simpl in *; try discriminate.
        specialize (IHop1 _ (eq_refl _) H0).
        destruct d0; simpl in *; try solve [inversion H; subst; trivial].
        destruct l; simpl; eauto 3.
        inversion H; subst; trivial.
      - intros.
        destruct d; try discriminate; inversion H0; subst; eauto.
      - intros.
        specialize (IHop1 d).
        specialize (IHop2 d).
        destruct (nra_eval op1 d); simpl in *; try discriminate.
        destruct (nra_eval op2 d); simpl in *; try discriminate.
        specialize (IHop1 _ (eq_refl _) H0).
        specialize (IHop2 _ (eq_refl _) H0).
        destruct d0; try discriminate.
        + destruct d0; try discriminate.
          destruct d1; try discriminate.
          inversion IHop1; subst.
          inversion H; subst.
          constructor.
          apply data_normalized_rec_concat_sort; trivial.
        + destruct d0; try discriminate.
          destruct d1; try discriminate.
          inversion IHop1; subst.
          inversion H; subst.
          constructor.
          apply data_normalized_rec_concat_sort; trivial.
        + repeat (destruct d0; try discriminate).
      - intros. specialize (IHop2 d).
        destruct (nra_eval op2 d); simpl in *; try discriminate.
        eauto.
      - intros.
        unfold edot in H.
        apply assoc_lookupr_in in H.
        rewrite Forall_forall in HconstNorm.
        specialize (HconstNorm (s,o)); simpl in *.
        auto.
    Qed.
  End Semantics.
  
  Section Top.
    Definition nra_eval_top (q:nra) (cenv:bindings) : option data :=
      nra_eval (rec_sort cenv) q dunit.
  End Top.

  Section FreeVars.
    Fixpoint nra_free_variables (q:nra) : list string :=
      match q with
      | AID => nil
      | AConst _ => nil
      | ABinop _ q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | AUnop _ q1 =>
        (nra_free_variables q1)
      | AMap q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | AMapConcat q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | AProduct q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | ASelect q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | ADefault q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | AEither ql qr =>
        app (nra_free_variables ql) (nra_free_variables qr)
      | AEitherConcat q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | AApp q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | AGetConstant s => s :: nil
    end.
  End FreeVars.

End NRA.

(* Some notations for the paper and readability *)

(** Nraebraic plan application *)

Notation "h ⊢ Op @ₐ x ⊣ c" := (nra_eval h c Op x) (at level 10). (* \vdash *)

(* As much as possible, notations are aligned with those of [CM93]
   S. Cluet and G. Moerkotte. Nested queries in object bases. In
   Proc. Int.  Workshop on Database Programming Languages , pages
   226-242, 1993.

   See also chapter 7.2 in:
   http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf
 *)

(* begin hide *)
Delimit Scope nra_scope with nra.

Notation "'ID'" := (AID)  (at level 50) : nra_scope.
Notation "CGET⟨ s ⟩" := (AGetConstant s) (at level 50) : nra_core_scope.

Notation "‵‵ c" := (AConst (dconst c))  (at level 0) : nra_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (AConst c)  (at level 0) : nra_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (AConst (dcoll nil))  (at level 0) : nra_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (AConst (drec nil)) (at level 50) : nra_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (ABinop OpAnd r1 r2) (right associativity, at level 65): nra_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (ABinop OpOr r1 r2) (right associativity, at level 70): nra_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (ABinop OpEqual r1 r2) (right associativity, at level 70): nra_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (ABinop OpLt r1 r2) (no associativity, at level 70): nra_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (ABinop OpBagUnion r1 r2) (right associativity, at level 70): nra_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (ABinop OpBagDiff r1 r2) (right associativity, at level 70): nra_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (ABinop OpBagMin r1 r2) (right associativity, at level 70): nra_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (ABinop OpBagMax r1 r2) (right associativity, at level 70): nra_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((ABinop OpRecConcat) p r) (at level 70) : nra_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((ABinop OpRecMerge) p r) (at level 70) : nra_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (AUnop OpNeg r1) (right associativity, at level 70): nra_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (AUnop OpDistinct r1) (right associativity, at level 70): nra_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (AUnop OpCount r1) (right associativity, at level 70): nra_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (AUnop OpFlatten d) (at level 50) : nra_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((AUnop OpBag) d)  (at level 50) : nra_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((AUnop (OpRec s)) r) (at level 50) : nra_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((AUnop (OpRecRemove s1)) r) (at level 50) : nra_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((AUnop (OpRecProject s1)) r) (at level 50) : nra_scope.          (* π = \pi *)
Notation "p · r" := ((AUnop (OpDot r)) p) (left associativity, at level 40): nra_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (AMap p r) (at level 70) : nra_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (AMapConcat e2 e1) (at level 70) : nra_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (AProduct r1 r2) (right associativity, at level 70): nra_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (ASelect p r) (at level 70) : nra_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (ADefault r1 r2) (right associativity, at level 70): nra_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (AApp r1 r2) (right associativity, at level 60): nra_scope.           (* ◯ = \bigcirc *)

Hint Resolve nra_eval_normalized.

Local Open Scope string_scope.
Tactic Notation "nra_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AID"
  | Case_aux c "AConst"
  | Case_aux c "ABinop"
  | Case_aux c "AUnop"
  | Case_aux c "AMap"
  | Case_aux c "AMapConcat"
  | Case_aux c "AProduct"
  | Case_aux c "ASelect"
  | Case_aux c "ADefault"
  | Case_aux c "AEither"
  | Case_aux c "AEitherConcat"
  | Case_aux c "AApp"
  | Case_aux c "AGetConstant" ].

(* end hide *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
