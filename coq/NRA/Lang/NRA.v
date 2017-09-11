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

(** NRA is the Nested Relational Algebra. Although it is not directly
in use in the compiler, replaced instead by NRAEnv, which extends it
with a separate notion of environment, it is kept in the compiler as a
reference. *)

(** NRA is a small pure language without functions based on
combinators (i.e., with no environment). Expressions in NRA take a
single value as input. *)

(** Summary:
- Language: NRA (Nested Relational Algebra)
- Based on: "Nested queries in object bases." Sophie Cluet and Guido
  Moerkotte. Database Programming Languages (DBPL-4). Springer,
  London, 1994. 226-242.
- A more complete and recent treatment can be found in: "Building
  Query Compilers", Chapter 7: An Algebra for Sets, Bags, and
  Sequences. Guido Moerkotte, 2014.
  http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf
- translating to NRA: CAMP, cNRAEnv
- translating from NRA: cNNRC, cNRAEnv *)

(** Compared to the version from Cluet and Moerkotte:
- We focus on a 'core' version of the algebra, suitable for semantics
  and reasoning purposes. A number of important operators important
  for optimization (e.g., GroupBy, Joins) are not considered, but can
  be defined in terms of this 'core'.
- We assume the existence of a global record containing global values
  (in a database context those would be the input tables).
- We add a [Default] operators which allows to test, and continue,
  when a result is the empty bag.
- We add two operators for matching against either values ([Either]
  and [EitherConcat]).
*)

Section NRA.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.

  Context {fruntime:foreign_runtime}.
  
  (** * Abstract Syntax *)

  Section Syntax.
  
  (** By convention, "static" parameters come first, followed by
     so-called dependent operators. This allows for easy instanciation
     on those parameters *)

    Inductive nra : Set :=
    | NRAGetConstant : string -> nra
    | NRAID : nra
    | NRAConst : data -> nra
    | NRABinop : binary_op -> nra -> nra -> nra
    | NRAUnop : unary_op -> nra -> nra
    | NRAMap : nra -> nra -> nra
    | NRAMapProduct : nra -> nra -> nra
    | NRAProduct : nra -> nra -> nra
    | NRASelect : nra -> nra -> nra
    | NRADefault : nra -> nra -> nra
    | NRAEither : nra -> nra -> nra
    | NRAEitherConcat : nra -> nra -> nra
    | NRAApp : nra -> nra -> nra.

    (** Equality between two NRA expressions is decidable. *)
  
    Global Instance nra_eqdec : EqDec nra eq.
    Proof.
      change (forall x y : nra,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec | apply data_eqdec | apply string_eqdec].
    Qed.

  End Syntax.

  (** * Semantics *)
  
  Section Semantics.
    (** Part of the context is fixed for the rest of the development:
- [h] is the brand relation
- [constant_env] is the global environment *)

    Context (h:list(string*string)).
    Context (constant_env:list (string*data)).

    Section Denotation.
      Inductive rec_concat_sem: data -> data -> data -> Prop :=
      | sem_rec_concat:
          forall r1 r2,
            rec_concat_sem (drec r1) (drec r2)
                           (drec (rec_concat_sort r1 r2)).

      Lemma orecconcat_correct : forall d d1 d2,
          orecconcat d d1 = Some d2 ->
          rec_concat_sem d d1 d2.
      Proof.
        intros.
        destruct d; destruct d1; simpl in *; try congruence.
        inversion H; econstructor; reflexivity.
      Qed.

      Lemma orecconcat_complete : forall d d1 d2,
          rec_concat_sem d d1 d2 ->
          orecconcat d d1 = Some d2.
      Proof.
        intros.
        inversion H; subst.
        reflexivity.
      Qed.

      Lemma orecconcat_correct_and_complete : forall d d1 d2,
          orecconcat d d1 = Some d2 <->
          rec_concat_sem d d1 d2.
      Proof.
        split.
        apply orecconcat_correct.
        apply orecconcat_complete.
      Qed.
        
      Inductive map_concat_sem: data -> list data -> list data -> Prop :=
      | sem_map_concat_empty : forall d,
          map_concat_sem d nil nil                     (**r   d χ⊕ {} ⇓ {} *)
      | sem_map_concat_cons : forall d d1 d2 c1 c2,
          rec_concat_sem d d1 d2 ->                    (**r   d ⊕ d₁ ⇓ d₂ *)
          map_concat_sem d c1 c2 ->                    (**r ∧ d χ⊕ {c₁} ⇓ {c₂} *)
          map_concat_sem d (d1::c1) (d2::c2).          (**r ⇒ d χ⊕ {d₁::c₁} ⇓ {d₂::c₂} *)

      Lemma omap_concat_correct d c1 c2:
        omap_concat d c1 = Some c2 ->
        map_concat_sem d c1 c2.
      Proof.
        unfold omap_concat.
        revert c2.
        induction c1; simpl; intros.
        - inversion H; subst; econstructor.
        - case_eq (orecconcat d a); intros; rewrite H0 in *; [|congruence].
          rewrite orecconcat_correct_and_complete in H0.
          unfold lift in H.
          case_eq (rmap (fun x : data => orecconcat d x) c1); intros;
            rewrite H1 in *; clear H1; [|congruence].
          inversion H; subst; clear H.
          specialize (IHc1 l eq_refl).
          econstructor; eauto.
      Qed.
      
      Lemma omap_concat_complete d c1 c2:
        map_concat_sem d c1 c2 ->
        omap_concat d c1 = Some c2.
      Proof.
        unfold omap_concat.
        revert c2.
        induction c1; simpl; intros.
        - inversion H; reflexivity.
        - inversion H; subst; simpl in *.
          rewrite <- orecconcat_correct_and_complete in H3.
          rewrite H3; simpl.
          unfold lift.
          rewrite (IHc1 c3 H5); reflexivity.
      Qed.
      
      Lemma omap_concat_correct_and_complete d c1 c2:
        omap_concat d c1 = Some c2 <->
        map_concat_sem d c1 c2.
      Proof.
        split.
        apply omap_concat_correct.
        apply omap_concat_complete.
      Qed.

      Inductive product_sem: list data -> list data -> list data -> Prop :=
      | sem_product_empty : forall c,
          product_sem nil c nil                   (**r   [{c} × {} ⇓ {}] *)
      | sem_product_cons : forall d1 c1 c2 c3 c4,
          map_concat_sem d1 c2 c3 ->              (**r ∧ d1 χ× {c₂} ⇓ {c₃} *)
          product_sem c1 c2 c4 ->                 (**r ∧ [{c₁} × {c₂} ⇓ {c₄}] *)
          product_sem (d1::c1) c2 (c3 ++ c4).     (**r ⇒ [{d₁::c₁} × {c₂} ⇓ {c₃}∪{c₄}] *)

      Lemma rproduct_correct c1 c2 c3:
        rproduct c1 c2 = Some c3 ->
        product_sem c1 c2 c3.
      Proof.
        unfold rproduct.
        revert c2 c3.
        induction c1; simpl; intros.
        - inversion H; econstructor.
        - case_eq (omap_concat a c2); intros; rewrite H0 in *; [|congruence].
          unfold lift in H.
          case_eq (oflat_map (fun x : data => omap_concat x c2) c1);
            intros; rewrite H1 in *; [|congruence].
          inversion H; subst; clear H.
          specialize (IHc1 c2 l0 H1).
          econstructor;[|assumption].
          rewrite omap_concat_correct_and_complete in H0;assumption.
      Qed.

      Lemma rproduct_complete c1 c2 c3:
        product_sem c1 c2 c3 ->
        rproduct c1 c2 = Some c3.
      Proof.
        unfold rproduct.
        revert c2 c3.
        induction c1; simpl; intros.
        - inversion H; subst; reflexivity.
        - inversion H; subst.
          rewrite <- omap_concat_correct_and_complete in H2.
          rewrite H2.
          unfold lift; rewrite (IHc1 c2 c6 H5).
          reflexivity.
      Qed.

      Lemma rproduct_correct_and_complete c1 c2 c3:
        rproduct c1 c2 = Some c3 <->
        product_sem c1 c2 c3.
      Proof.
        split.
        apply rproduct_correct.
        apply rproduct_complete.
      Qed.

      Inductive nra_sem: nra -> data -> data -> Prop :=
      | sem_NRAGetConstant : forall v din d,
          edot constant_env v = Some d ->             (**r   [Γc(v) = d] *)
          nra_sem (NRAGetConstant v) din d            (**r ⇒ [Γc ; Γ ⊢〚$$v〛⇓ d] *)
      | sem_NRAID : forall din,
          nra_sem NRAID din din
      | sem_NRAConst : forall din d d1,
          normalize_data h d = d1 ->
          nra_sem (NRAConst d) din d1
      | sem_NRABinop : forall bop e1 e2 din d1 d2 d3,
          nra_sem e1 din d1 ->
          nra_sem e2 din d2 ->
          binary_op_eval h bop d1 d2 = Some d3 ->
          nra_sem (NRABinop bop e1 e2) din d3
      | sem_NRAUnop : forall uop e din d1 d2,
          nra_sem e din d1 ->
          unary_op_eval h uop d1 = Some d2 ->
          nra_sem (NRAUnop uop e) din d2
      | sem_NRAMap : forall e1 e2 din c1 c2,
          nra_sem e1 din (dcoll c1) ->
          nra_sem_map e2 c1 c2 ->
          nra_sem (NRAMap e2 e1) din (dcoll c2)
      | sem_NRAMapProduct : forall e1 e2 din c1 c2,
          nra_sem e1 din (dcoll c1) ->
          nra_sem_map_product e2 c1 c2 ->
          nra_sem (NRAMapProduct e2 e1) din (dcoll c2)
      | sem_NRAProduct : forall e1 e2 din c1 c2 c3,
          nra_sem e1 din (dcoll c1) ->
          nra_sem e2 din (dcoll c2) ->
          product_sem c1 c2 c3 ->
          nra_sem (NRAProduct e1 e2) din (dcoll c3)
      | sem_NRASelect : forall e1 e2 din c1 c2,
          nra_sem e1 din (dcoll c1) ->
          nra_sem_select e2 c1 c2 ->
          nra_sem (NRASelect e2 e1) din (dcoll c2)
      | sem_NRADefault_empty : forall e1 e2 din d2,
          nra_sem e1 din (dcoll nil) ->
          nra_sem e2 din d2 ->
          nra_sem (NRADefault e1 e2) din d2
      | sem_NRADefault_not_empty : forall e1 e2 din d1,
          d1 <> dcoll nil ->
          nra_sem e1 din d1 ->
          nra_sem (NRADefault e1 e2) din d1
      | sem_NRAEither_left : forall e1 e2 d1 d3,
          nra_sem e1 d1 d3 ->
          nra_sem (NRAEither e1 e2) (dleft d1) d3
      | sem_NRAEither_right : forall e1 e2 d1 d3,
          nra_sem e2 d1 d3 ->
          nra_sem (NRAEither e1 e2) (dright d1) d3
      | sem_NRAEitherConcat_left : forall e1 e2 d r1 r2,
          nra_sem e1 d (dleft (drec r1)) ->
          nra_sem e2 d (drec r2) ->
          nra_sem (NRAEitherConcat e1 e2) d (dleft (drec (rec_concat_sort r1 r2)))
      | sem_NRAEitherConcat_right : forall e1 e2 d r1 r2,
          nra_sem e1 d (dright (drec r1)) ->
          nra_sem e2 d (drec r2) ->
          nra_sem (NRAEitherConcat e1 e2) d (dright (drec (rec_concat_sort r1 r2)))
      | sem_NRAApp : forall e1 e2 din d1 d2,
          nra_sem e1 din d1 ->
          nra_sem e2 d1 d2 ->
          nra_sem (NRAApp e2 e1) din d2
      with nra_sem_map: nra -> list data -> list data -> Prop :=
      | sem_NRAMMap_empty : forall e,
          nra_sem_map e nil nil                       (**r   [Γc ; {} ⊢〚e〛χ ⇓ {}] *)
      | sem_NRAMap_cons : forall e d1 c1 d2 c2,
          nra_sem e d1 d2 ->                          (**r   [Γc ; d₁ ⊢〚e〛⇓ d₂]  *)
          nra_sem_map e c1 c2 ->                      (**r ∧ [Γc ; {c₁} ⊢〚e〛χ ⇓ {c₂}] *)
          nra_sem_map e (d1::c1) (d2::c2)             (**r ⇒ [Γc ; {d₁::c₁} ⊢〚e〛χ ⇓ {d₂::c₂}] *)
      with nra_sem_map_product: nra -> list data -> list data -> Prop :=
      | sem_NRAMapProduct_empty : forall e,
          nra_sem_map_product e nil nil               (**r   [Γc ; {} ⊢〚e〛⋈ᵈ ⇓ {}] *)
      | sem_NRAMapProduct_cons : forall e d1 c1 c2 c3 c4,
          nra_sem e d1 (dcoll c3) ->                  (**r   [Γc ; d₁ ⊢〚e〛⋈ᵈ ⇓ {c₃}]  *)
          map_concat_sem d1 c3 c4 ->                  (**r ∧ d₁ χ⊕ c₃ ⇓ c₄ *)
          nra_sem_map_product e c1 c2 ->              (**r ∧ [Γc ; {c₁} ⊢〚e〛⋈ᵈ ⇓ {c₂}] *)
          nra_sem_map_product e (d1::c1) (c4 ++ c2)   (**r ⇒ [Γc ; {d₁::c₁} ⊢〚e〛⋈ᵈ ⇓ {c₄}∪{c₂}] *)
      with nra_sem_select: nra -> list data -> list data -> Prop :=
      | sem_NRASelect_empty : forall e,
          nra_sem_select e nil nil                    (**r   [Γc ; {} ⊢〚e〛σ ⇓ {}] *)
      | sem_NRASelect_true : forall e d1 c1 c2,
          nra_sem e d1 (dbool true) ->                (**r   [Γc ; d₁ ⊢〚e〛σ ⇓ true]  *)
          nra_sem_select e c1 c2 ->                   (**r ∧ [Γc ; {c₁} ⊢〚e〛σ ⇓ {c₂}] *)
          nra_sem_select e (d1::c1) (d1::c2)          (**r ⇒ [Γc ; {d₁::c₁} ⊢〚e〛σ ⇓ {d₁::c₂}] *)
      | sem_NRASelect_false : forall e d1 c1 c2,
          nra_sem e d1 (dbool false) ->               (**r   [Γc ; d₁ ⊢〚e〛σ ⇓ false]  *)
          nra_sem_select e c1 c2 ->                   (**r ∧ [Γc ; {c₁} ⊢〚e〛σ ⇓ {c₂}] *)
          nra_sem_select e (d1::c1) c2                (**r ⇒ [Γc ; {d₁::c₁} ⊢〚e〛σ ⇓ {c₂}] *)
      .

    (** Note that there is (resp is not) a call to [nra_sem] inside
    the [nra_sem_map] (resp [nra_sem_map_concat]) judgment, which
    shows the distinction between so-called dependent product and a
    regular Cartesian product. *)

    End Denotation.

    Section Evaluation.
      
      Fixpoint nra_eval (e:nra) (din:data) : option data :=
        match e with
        | NRAGetConstant s =>
          edot constant_env s
        | NRAID =>
          Some din
        | NRAConst d =>
          Some (normalize_data h d)
        | NRABinop bop e1 e2 =>
          olift2
            (fun d1 d2 => binary_op_eval h bop d1 d2)
            (nra_eval e1 din) (nra_eval e2 din)
        | NRAUnop uop e =>
          olift (fun d1 => unary_op_eval h uop d1) (nra_eval e din)
        | NRAMap e2 e1 =>
          let aux_map c1 :=
              lift_oncoll (fun d1 => lift dcoll (rmap (nra_eval e2) d1)) c1
          in olift aux_map (nra_eval e1 din)
        | NRAMapProduct e2 e1 =>
          let aux_mapconcat c1 :=
              lift_oncoll (fun d1 => lift dcoll (rmap_product (nra_eval e2) d1)) c1
          in olift aux_mapconcat (nra_eval e1 din)
        | NRAProduct e1 e2 =>
          (* Note: (fun y => nra_eval op2 x) does not depend on input,
             but we still use a nested loop and delay op2 evaluation
             so it does not fail in case the op1 operand is an empty
             collection -- this makes sure to align the semantics with
             the NNRC version. - Jerome *)
          let aux_product d :=
              lift_oncoll (fun c1 => lift dcoll (rmap_product (fun _ => nra_eval e2 din) c1)) d
          in olift aux_product (nra_eval e1 din)
        | NRASelect e2 e1 =>
          let pred d1 :=
              match nra_eval e2 d1 with
              | Some (dbool b) => Some b
              | _ => None
              end
          in
          let aux_select c1 :=
              lift_oncoll (fun d1 => lift dcoll (lift_filter pred d1)) c1
          in
          olift aux_select (nra_eval e1 din)
        | NRADefault e1 e2 =>
          olift (fun d1 =>
                   match d1 with
                   | dcoll nil => nra_eval e2 din
                   | _ => Some d1
                   end)
                (nra_eval e1 din)
        | NRAEither e1 e2 =>
          match din with
          | dleft d1 => nra_eval e1 d1
          | dright d2 => nra_eval e2 d2
          | _ => None
          end
        | NRAEitherConcat e1 e2 =>
          match nra_eval e1 din, nra_eval e2 din with
          | Some (dleft (drec l)), Some (drec t)  =>
            Some (dleft (drec (rec_concat_sort l t)))
          | Some (dright (drec r)), Some (drec t)  =>
            Some (dright (drec (rec_concat_sort r t)))
          | _, _ => None
          end
        | NRAApp e2 e1 =>
          olift (fun d1 => (nra_eval e2 d1)) (nra_eval e1 din)
        end.
    End Evaluation.

    Section EvalCorrect.
      Lemma nra_eval_map_correct : forall e l1 l2,
        (forall d1 d2 : data, nra_eval e d1 = Some d2 -> nra_sem e d1 d2) ->
        rmap (nra_eval e) l1 = Some l2 ->
        nra_sem_map e l1 l2.
      Proof.
        intros.
        revert l2 H0.
        induction l1; simpl in *; intros.
        - inversion H0; econstructor.
        - case_eq (nra_eval e a); intros; rewrite H1 in *; [|congruence].
          unfold lift in H0.
          case_eq (rmap (nra_eval e) l1); intros; rewrite H2 in *; [|congruence].
          specialize (IHl1 l eq_refl).
          inversion H0.
          econstructor; eauto.
      Qed.

          
      Lemma nra_eval_map_product_correct : forall e l1 l2,
        (forall d1 d2 : data, nra_eval e d1 = Some d2 -> nra_sem e d1 d2) ->
        rmap_product (nra_eval e) l1 = Some l2 ->
        nra_sem_map_product e l1 l2.
      Proof.
        intros.
        revert l2 H0.
        induction l1; simpl in *; intros.
        - inversion H0; econstructor.
        - generalize (rmap_product_cons_inv (nra_eval e) l1 a l2 H0); intros.
          elim H1; clear H1; intros.
          elim H1; clear H1; intros.
          elim H1; clear H1; intros.
          elim H2; clear H2; intros.
          subst.
          unfold oomap_concat in H1.
          case_eq (nra_eval e a); intros; rewrite H3 in *; [|congruence].
          case_eq d; intros; rewrite H4 in H1; try congruence.
          subst.
          specialize (H a (dcoll l) H3).
          rewrite omap_concat_correct_and_complete in H1.
          apply (sem_NRAMapProduct_cons e a l1 x0 l x).
          + assumption.
          + assumption.
          + apply IHl1; assumption.
      Qed.

      Lemma nra_eval_select_correct e l1 l2 :
        (forall d1 d2 : data, nra_eval e d1 = Some d2 -> nra_sem e d1 d2) ->
        lift_filter
          (fun d1 : data =>
             match nra_eval e d1 with
             | Some dunit => None
             | Some (dnat _) => None
             | Some (dbool b) => Some b
             | Some (dstring _) => None
             | Some (dcoll _) => None
             | Some (drec _) => None
             | Some (dleft _) => None
             | Some (dright _) => None
             | Some (dbrand _ _) => None
             | Some (dforeign _) => None
             | None => None
             end) l1 = Some l2 ->
        nra_sem_select e l1 l2.
      Proof.
        intro.
        revert l2; induction l1; simpl; intros.
        - inversion H0. econstructor.
        - case_eq (nra_eval e a); intros; rewrite H1 in *; simpl in *.
          destruct d; simpl in *; try congruence.
          case_eq
            (lift_filter
               (fun d1 : data =>
                  match nra_eval e d1 with
                  | Some dunit => None
                  | Some (dnat _) => None
                  | Some (dbool b) => Some b
                  | Some (dstring _) => None
                  | Some (dcoll _) => None
                  | Some (drec _) => None
                  | Some (dleft _) => None
                  | Some (dright _) => None
                  | Some (dbrand _ _) => None
                  | Some (dforeign _) => None
                  | None => None
                  end) l1);
            intros; rewrite H2 in *; clear H2; [|congruence].
          specialize (IHl1 l eq_refl).
          destruct b; simpl in *;
            simpl in *; inversion H0; clear H0; subst.
          + econstructor; eauto.
          + econstructor; eauto.
          + congruence.
      Qed.

      Lemma nra_eval_correct : forall e d1 d2,
          nra_eval e d1 = Some d2 ->
          nra_sem e d1 d2.
      Proof.
        induction e; simpl; intros.
        - econstructor; eauto.
        - inversion H; econstructor; eauto.
        - inversion H; econstructor; eauto.
        - unfold olift2 in H.
          case_eq (nra_eval e1 d1); intros; rewrite H0 in *; [|congruence].
          case_eq (nra_eval e2 d1); intros; rewrite H1 in *; [|congruence].
          specialize (IHe1 d1 d H0); specialize (IHe2 d1 d0 H1);
            econstructor; eauto.
        - unfold olift in H.
          case_eq (nra_eval e d1); intros; rewrite H0 in *; [|congruence].
          specialize (IHe d1 d H0); econstructor; eauto.
        - unfold olift in H.
          case_eq (nra_eval e2 d1); intros; rewrite H0 in *; [|congruence].
          unfold lift_oncoll in H.
          destruct d; simpl in H; try congruence.
          unfold lift in H.
          case_eq (rmap (nra_eval e1) l); intros; rewrite H1 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          apply nra_eval_map_correct; auto.
        - unfold olift in H.
          case_eq (nra_eval e2 d1); intros; rewrite H0 in *; [|congruence].
          unfold lift_oncoll in H.
          destruct d; simpl in H; try congruence.
          unfold lift in H.
          case_eq (rmap_product (nra_eval e1) l); intros; rewrite H1 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          apply nra_eval_map_product_correct; auto.
        - unfold olift2 in H.
          (*
          case_eq (nra_eval e1 d1); intros; rewrite H0 in *; [|congruence].
          case_eq (nra_eval e2 d1); intros; rewrite H1 in *; [|congruence].
          unfold lift_ondcoll2 in H.
          destruct d; try congruence.
          destruct d0; try congruence.
          unfold lift in H.
          case_eq (rproduct l l0); intros; rewrite H2 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          rewrite <- rproduct_correct_and_complete. assumption.
           *)
          admit.
        - unfold olift in H.
          case_eq (nra_eval e2 d1); intros; rewrite H0 in *; [|congruence].
          unfold lift_oncoll in H.
          destruct d; simpl in H; try congruence.
          unfold lift in H.
          specialize (IHe2 d1 (dcoll l) H0).
          case_eq
            (lift_filter
               (fun d1 : data =>
                  match nra_eval e1 d1 with
                  | Some dunit => None
                  | Some (dnat _) => None
                  | Some (dbool b) => Some b
                  | Some (dstring _) => None
                  | Some (dcoll _) => None
                  | Some (drec _) => None
                  | Some (dleft _) => None
                  | Some (dright _) => None
                  | Some (dbrand _ _) => None
                  | Some (dforeign _) => None
                  | None => None
                  end) l); intros; rewrite H1 in *; [|congruence].
          inversion H; clear H; subst.
          econstructor; eauto.
          apply nra_eval_select_correct; auto.
        - unfold olift in H.
          case_eq (nra_eval e1 d1); intros; rewrite H0 in *; [|congruence].
          elim (data_eq_dec d (dcoll nil)); intros.
          subst.
          + econstructor; eauto.
          + destruct d; inversion H; subst; auto;
              eapply sem_NRADefault_not_empty; auto;
                destruct l; auto; inversion H; subst; auto.
            congruence.
        - destruct d1; try congruence.
          econstructor; apply IHe1; auto.
          econstructor; apply IHe2; auto.
        - case_eq (nra_eval e1 d1); intros; rewrite H0 in *; [|congruence].
          destruct d; intros; try congruence.
         + destruct d; intros; try congruence.
            case_eq (nra_eval e2 d1); intros; rewrite H1 in *; [|congruence].
            destruct d; intros; try congruence.
            inversion H; subst; clear H; intros.
            econstructor; eauto.
          + destruct d; intros; try congruence.
            case_eq (nra_eval e2 d1); intros; rewrite H1 in *; [|congruence].
            destruct d; intros; try congruence.
            inversion H; subst; clear H; intros.
            econstructor; eauto.
        - unfold olift in H.
          case_eq (nra_eval e2 d1); intros; rewrite H0 in *; [|congruence].
          econstructor; eauto.
      Admitted.
 
    End EvalCorrect.

    Section EvalNormalized.
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
        - intros.
          unfold edot in H.
          apply assoc_lookupr_in in H.
          rewrite Forall_forall in HconstNorm.
          specialize (HconstNorm (s,o)); simpl in *.
          auto.
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
          unfold rmap_product in *.
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
        - intros;
            specialize (IHop1 d);
            destruct (nra_eval op1 d); simpl in *; try discriminate.
          specialize (IHop1 _ (eq_refl _) H0).
          destruct d0; simpl in *; try discriminate.
          apply some_lift in H; destruct H; subst.
          constructor.
          inversion IHop1; subst.
          unfold rmap_product in *.
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
          unfold rmap_product in *.
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
      Qed.
    End EvalNormalized.
  End Semantics.
  
  Section Top.
    Context (h:list(string*string)).
    Definition nra_eval_top (q:nra) (cenv:bindings) : option data :=
      nra_eval h (rec_sort cenv) q dunit.
  End Top.

  Section FreeVars.
    Fixpoint nra_free_variables (q:nra) : list string :=
      match q with
      | NRAGetConstant s => s :: nil
      | NRAID => nil
      | NRAConst _ => nil
      | NRABinop _ q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | NRAUnop _ q1 =>
        (nra_free_variables q1)
      | NRAMap q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | NRAMapProduct q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | NRAProduct q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | NRASelect q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | NRADefault q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | NRAEither ql qr =>
        app (nra_free_variables ql) (nra_free_variables qr)
      | NRAEitherConcat q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
      | NRAApp q1 q2 =>
        app (nra_free_variables q1) (nra_free_variables q2)
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

Notation "'ID'" := (NRAID)  (at level 50) : nra_scope.
Notation "TABLE⟨ s ⟩" := (NRAGetConstant s) (at level 50) : nra_core_scope.
Notation "‵‵ c" := (NRAConst (dconst c))  (at level 0) : nra_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (NRAConst c)  (at level 0) : nra_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (NRAConst (dcoll nil))  (at level 0) : nra_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (NRAConst (drec nil)) (at level 50) : nra_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (NRABinop OpAnd r1 r2) (right associativity, at level 65): nra_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (NRABinop OpOr r1 r2) (right associativity, at level 70): nra_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (NRABinop OpEqual r1 r2) (right associativity, at level 70): nra_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (NRABinop OpLt r1 r2) (no associativity, at level 70): nra_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (NRABinop OpBagUnion r1 r2) (right associativity, at level 70): nra_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (NRABinop OpBagDiff r1 r2) (right associativity, at level 70): nra_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (NRABinop OpBagMin r1 r2) (right associativity, at level 70): nra_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (NRABinop OpBagMax r1 r2) (right associativity, at level 70): nra_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((NRABinop OpRecConcat) p r) (at level 70) : nra_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((NRABinop OpRecMerge) p r) (at level 70) : nra_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (NRAUnop OpNeg r1) (right associativity, at level 70): nra_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (NRAUnop OpDistinct r1) (right associativity, at level 70): nra_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (NRAUnop OpCount r1) (right associativity, at level 70): nra_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (NRAUnop OpFlatten d) (at level 50) : nra_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((NRAUnop OpBag) d)  (at level 50) : nra_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((NRAUnop (OpRec s)) r) (at level 50) : nra_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((NRAUnop (OpRecRemove s1)) r) (at level 50) : nra_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((NRAUnop (OpRecProject s1)) r) (at level 50) : nra_scope.          (* π = \pi *)
Notation "p · r" := ((NRAUnop (OpDot r)) p) (left associativity, at level 40): nra_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (NRAMap p r) (at level 70) : nra_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (NRAMapProduct e2 e1) (at level 70) : nra_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (NRAProduct r1 r2) (right associativity, at level 70): nra_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (NRASelect p r) (at level 70) : nra_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (NRADefault r1 r2) (right associativity, at level 70): nra_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (NRAApp r1 r2) (right associativity, at level 60): nra_scope.           (* ◯ = \bigcirc *)

Hint Resolve nra_eval_normalized.

Local Open Scope string_scope.
Tactic Notation "nra_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NRAGetConstant"
  | Case_aux c "NRAID"
  | Case_aux c "NRAConst"
  | Case_aux c "NRABinop"
  | Case_aux c "NRAUnop"
  | Case_aux c "NRAMap"
  | Case_aux c "NRAMapProduct"
  | Case_aux c "NRAProduct"
  | Case_aux c "NRASelect"
  | Case_aux c "NRADefault"
  | Case_aux c "NRAEither"
  | Case_aux c "NRAEitherConcat"
  | Case_aux c "NRAApp" ].

(* end hide *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
