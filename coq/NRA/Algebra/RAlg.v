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

Section RAlg.
  Require Import String List Compare_dec.
  Require Import EquivDec.
  
  Require Import Utils BasicRuntime.

  (** Nested Relational Algebra *)

  (** By convention, "static" parameters come first, followed by
     dependent operators. This allows for instanciation on those
     parameters *)

  Context {fruntime:foreign_runtime}.
  
  Inductive alg : Set :=
  | AID : alg
  | AConst : data -> alg
  | ABinop : binOp -> alg -> alg -> alg
  | AUnop : unaryOp -> alg -> alg
  | AMap : alg -> alg -> alg
  | AMapConcat : alg -> alg -> alg
  | AProduct : alg -> alg -> alg
  | ASelect : alg -> alg -> alg
  | ADefault : alg -> alg -> alg
  | AEither : alg -> alg -> alg
  | AEitherConcat : alg -> alg -> alg
  | AApp : alg -> alg -> alg
  .

  Global Instance alg_eqdec : EqDec alg eq.
  Proof.
    change (forall x y : alg,  {x = y} + {x <> y}).
    decide equality;
    try solve [apply binOp_eqdec | apply unaryOp_eqdec | apply data_eqdec | apply string_eqdec].
  Qed.

  (** NRA Semantics *)

  Context (h:list(string*string)).
  
  Fixpoint fun_of_alg (op:alg) (x:data) : option data :=
    match op with
      | AID => Some x
      | AConst rd => Some (normalize_data h rd)
      | ABinop bop op1 op2 =>
        olift2 (fun d1 d2 => fun_of_binop h bop d1 d2) (fun_of_alg op1 x) (fun_of_alg op2 x)
      | AUnop uop op1 =>
        olift (fun d1 => fun_of_unaryop h uop d1) (fun_of_alg op1 x)
      | AMap op1 op2 =>
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (fun_of_alg op1) c1)) d
        in olift aux_map (fun_of_alg op2 x)
      | AMapConcat op1 op2 =>
        let aux_mapconcat d :=
            lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun_of_alg op1) c1)) d
        in olift aux_mapconcat (fun_of_alg op2 x)
      | AProduct op1 op2 =>
        (* Note: (fun y => fun_of_alg op2 x) does not depend on input,
           but we still use a nested loop and delay op2 evaluation so it does not
           fail in case the op1 operand is an empty collection -- this makes sure
           to align the semantics with the NNRC version. - Jerome *)
        let aux_product d :=
            lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => fun_of_alg op2 x) c1)) d
        in olift aux_product (fun_of_alg op1 x)
      | ASelect op1 op2 =>
        let pred x' :=
            match fun_of_alg op1 x' with
              | Some (dbool b) => Some b
              | _ => None
            end
        in
        let aux_select d :=
            lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
        in
        olift aux_select (fun_of_alg op2 x)
      | ADefault op1 op2 =>
        olift (fun d1 => match d1 with
                           | dcoll nil => fun_of_alg op2 x
                           | _ => Some d1
                         end) (fun_of_alg op1 x)
      | AEither opl opr =>
        match x with
          | dleft dl => fun_of_alg opl dl
          | dright dr => fun_of_alg opr dr
          | _ => None
        end
      | AEitherConcat op1 op2 =>
        match fun_of_alg op1 x, fun_of_alg op2 x with
          | Some (dleft (drec l)), Some (drec t)  =>
            Some (dleft (drec (rec_concat_sort l t)))
          | Some (dright (drec r)), Some (drec t)  =>
            Some (dright (drec (rec_concat_sort r t)))
          | _, _ => None
        end
      | AApp op1 op2 =>
        olift (fun d => (fun_of_alg op1 d)) (fun_of_alg op2 x)
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
  Lemma fun_of_alg_normalized {op:alg} {d:data} {o} :
    fun_of_alg op d = Some o ->
    data_normalized h d ->
    data_normalized h o.
  Proof.
    revert d o.
    induction op; simpl.
    - inversion 1; subst; trivial.
    - inversion 1; subst; intros.
      apply normalize_normalizes.
    - intros.
      specialize (IHop1 d).
      specialize (IHop2 d).
      destruct (fun_of_alg op1 d); simpl in *; try discriminate.
      destruct (fun_of_alg op2 d); simpl in *; try discriminate.
      apply (fun_of_binop_normalized h) in H; eauto.
    - intros.
      specialize (IHop d).
      destruct (fun_of_alg op d); simpl in *; try discriminate.
      apply fun_of_unaryop_normalized in H; eauto.
    - intros;
      specialize (IHop2 d);
      destruct (fun_of_alg op2 d); simpl in *; try discriminate;
      specialize (IHop2 _ (eq_refl _) H0).
      destruct d0; simpl in *; try discriminate.
      apply some_lift in H; destruct H; subst.
      constructor.
      inversion IHop2; subst.
      apply (rmap_Forall e H1); eauto.
    - intros;
      specialize (IHop2 d);
      destruct (fun_of_alg op2 d); simpl in *; try discriminate;
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
      destruct (fun_of_alg op1 d); simpl in *; try discriminate.
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
      destruct (fun_of_alg op2 d); simpl in *; try discriminate;
      specialize (IHop2 _ (eq_refl _) H0).
      destruct d0; simpl in *; try discriminate.
      apply some_lift in H; destruct H; subst.      
      constructor.
      inversion IHop2; subst.
      unfold rmap_concat in *.
      apply (lift_filter_Forall e H1).
    - intros;
      specialize (IHop1 d);
      destruct (fun_of_alg op1 d); simpl in *; try discriminate.
      specialize (IHop1 _ (eq_refl _) H0).
      destruct d0; simpl in *; try solve [inversion H; subst; trivial].
      destruct l; simpl; eauto 3.
      inversion H; subst; trivial.
    - intros.
      destruct d; try discriminate; inversion H0; subst; eauto.
    - intros.
      specialize (IHop1 d).
      specialize (IHop2 d).
      destruct (fun_of_alg op1 d); simpl in *; try discriminate.
      destruct (fun_of_alg op2 d); simpl in *; try discriminate.
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
      destruct (fun_of_alg op2 d); simpl in *; try discriminate.
      eauto. 
  Qed.
    
End RAlg.

(* Some notations for the paper and readability *)

(** Algebraic plan application *)

Notation "h ⊢ Op @ₐ x" := (fun_of_alg h Op x) (at level 10). (* \vdash *)

(* As much as possible, notations are aligned with those of [CM93]
   S. Cluet and G. Moerkotte. Nested queries in object bases. In
   Proc. Int.  Workshop on Database Programming Languages , pages
   226-242, 1993.

   See also chapter 7.2 in:
   http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf
 *)

(* begin hide *)
Delimit Scope alg_scope with alg.

Notation "'ID'" := (AID)  (at level 50) : alg_scope.

Notation "‵‵ c" := (AConst (dconst c))  (at level 0) : alg_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (AConst c)  (at level 0) : alg_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (AConst (dcoll nil))  (at level 0) : alg_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (AConst (drec nil)) (at level 50) : alg_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (ABinop AAnd r1 r2) (right associativity, at level 65): alg_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (ABinop AOr r1 r2) (right associativity, at level 70): alg_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (ABinop AEq r1 r2) (right associativity, at level 70): alg_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (ABinop ALt r1 r2) (no associativity, at level 70): alg_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (ABinop AUnion r1 r2) (right associativity, at level 70): alg_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (ABinop AMinus r1 r2) (right associativity, at level 70): alg_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (ABinop AMin r1 r2) (right associativity, at level 70): alg_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (ABinop AMax r1 r2) (right associativity, at level 70): alg_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((ABinop AConcat) p r) (at level 70) : alg_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((ABinop AMergeConcat) p r) (at level 70) : alg_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (AUnop ANeg r1) (right associativity, at level 70): alg_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (AUnop ADistinct r1) (right associativity, at level 70): alg_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (AUnop ACount r1) (right associativity, at level 70): alg_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (AUnop AFlatten d) (at level 50) : alg_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((AUnop AColl) d)  (at level 50) : alg_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((AUnop (ARec s)) r) (at level 50) : alg_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((AUnop (ARecRemove s1)) r) (at level 50) : alg_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((AUnop (ARecProject s1)) r) (at level 50) : alg_scope.          (* π = \pi *)
Notation "p · r" := ((AUnop (ADot r)) p) (left associativity, at level 40): alg_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (AMap p r) (at level 70) : alg_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (AMapConcat e2 e1) (at level 70) : alg_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (AProduct r1 r2) (right associativity, at level 70): alg_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (ASelect p r) (at level 70) : alg_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (ADefault r1 r2) (right associativity, at level 70): alg_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (AApp r1 r2) (right associativity, at level 60): alg_scope.           (* ◯ = \bigcirc *)

Hint Resolve fun_of_alg_normalized.

Local Open Scope string_scope.
Tactic Notation "alg_cases" tactic(first) ident(c) :=
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
  | Case_aux c "AApp"].

(* end hide *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
