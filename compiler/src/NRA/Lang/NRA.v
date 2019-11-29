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
combinators (i.e., with no variables). Expressions in NRA take a
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

Require Import String.
Require Import List.
Require Import Compare_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.

Section NRA.
  Context {fruntime:foreign_runtime}.
  
  (** * Abstract Syntax *)

  Section Syntax.
  
  (** By convention, "static" parameters come first, followed by
     so-called dependent operators. This allows for easy instanciation
     on those parameters *)

    Inductive nra : Set :=
    | NRAGetConstant : string -> nra              (**r global variable lookup ([$$v]) *)
    | NRAID : nra                                 (**r current value ([ID]) *)
    | NRAConst : data -> nra                      (**r constant data ([d]) *)
    | NRABinop : binary_op -> nra -> nra -> nra   (**r binary operator ([e₁ ⊠ e₂]) *)
    | NRAUnop : unary_op -> nra -> nra            (**r unary operator ([⊞ e]) *)
    | NRAMap : nra -> nra -> nra                  (**r map operator ([χ⟨e₂⟩(e₁)]) *)
    | NRAMapProduct : nra -> nra -> nra           (**r dependent product operator ([⋈ᵈ⟨e₂⟩(e₁)]) *)
    | NRAProduct : nra -> nra -> nra              (**r product operator ([e₁ × e₂]) *)
    | NRASelect : nra -> nra -> nra               (**r selection operator ([σ⟨e₂⟩(e₁)]) *)
    | NRADefault : nra -> nra -> nra              (**r default operator ([e₁ ∥ e₂]) *)
    | NRAEither : nra -> nra -> nra               (**r either operator ([either e₁ e₂]) *)
    | NRAEitherConcat : nra -> nra -> nra         (**r either-concat operator ([either⊕ e₁ e₂]) *)
    | NRAApp : nra -> nra -> nra.                 (**r compose operator ([e₂ ∘ e₁]) *)

    Tactic Notation "nra_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "NRAGetConstant"%string
      | Case_aux c "NRAID"%string
      | Case_aux c "NRAConst"%string
      | Case_aux c "NRABinop"%string
      | Case_aux c "NRAUnop"%string
      | Case_aux c "NRAMap"%string
      | Case_aux c "NRAMapProduct"%string
      | Case_aux c "NRAProduct"%string
      | Case_aux c "NRASelect"%string
      | Case_aux c "NRADefault"%string
      | Case_aux c "NRAEither"%string
      | Case_aux c "NRAEitherConcat"%string
      | Case_aux c "NRAApp"%string ].

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

    (** ** Denotational Semantics *)

    (** The semantics is defined using the main judgment [Γc ; d ⊢〚e
    〛⇓ d'] ([nra_sem]) where [Γc] is the global environment, [d] is
    the input value, [e] the NRA expression and [d'] the resulting
    value. *)
    
    (** The auxiliary judgment [Γc ; {c₁} ⊢〚e〛χ ⇓ {c₂}]
    ([nra_sem_map]) is used in the definition of the map [χ]
    operator. *)
    
    (** The auxiliary judgment [Γc ; {c₁} ⊢〚e〛⋈ᵈ ⇓ {c₂}]
    ([nra_map_product_select]) is used in the definition of the
    dependant product [⋈ᵈ] operator. *)
    
    (** The auxiliary judgment [Γc ; {c₁} ⊢〚e〛σ ⇓ {c₂}]
    ([nra_sem_select]) is used in the definition of the selection [σ]
    operator. *)
    
    Section Denotation.
      Inductive nra_sem: nra -> data -> data -> Prop :=
      | sem_NRAGetConstant : forall v d d1,
          edot constant_env v = Some d1 ->                (**r   [Γc(v) = d₁] *)
          nra_sem (NRAGetConstant v) d d1                 (**r ⇒ [Γc ; d ⊢〚$$v〛⇓ d₁] *)
      | sem_NRAID : forall d,
          nra_sem NRAID d d                               (**r   [Γc ; d ⊢ ID ⇓ d] *)
      | sem_NRAConst : forall d d1 d2,
          normalize_data h d1 = d2 ->                     (**r   [norm(d₁) = d₂] *)
          nra_sem (NRAConst d1) d d2                      (**r ⇒ [Γc ; d ⊢〚d₁〛⇓ d₂] *)
      | sem_NRABinop : forall bop e1 e2 d d1 d2 d3,
          nra_sem e1 d d1 ->                              (**r   [Γc ; d ⊢〚e₁〛⇓ d₁] *)
          nra_sem e2 d d2 ->                              (**r ∧ [Γc ; d ⊢〚e₂〛⇓ d₂] *)
          binary_op_eval h bop d1 d2 = Some d3 ->         (**r ∧ [d₁ ⊠ d₂ = d₃] *)
          nra_sem (NRABinop bop e1 e2) d d3               (**r ⇒ [Γc ; d ⊢〚e₁ ⊠ e₂〛⇓ d₃] *)
      | sem_NRAUnop : forall uop e d d1 d2,
          nra_sem e d d1 ->                               (**r   [Γc ; d ⊢〚e〛⇓ d₁] *)
          unary_op_eval h uop d1 = Some d2 ->             (**r ∧ [⊞ d₁ = d₂] *)
          nra_sem (NRAUnop uop e) d d2                    (**r ⇒ [Γc ; d ⊢〚⊞ e〛⇓ d₂] *)
      | sem_NRAMap : forall e1 e2 d c1 c2,
          nra_sem e1 d (dcoll c1) ->                      (**r   [Γc ; d ⊢〚e₁〛⇓ {c₁}] *)
          nra_sem_map e2 c1 c2 ->                         (**r ∧ [Γc ; {c₁} ⊢〚e₂〛χ ⇓ {c₂}] *)
          nra_sem (NRAMap e2 e1) d (dcoll c2)             (**r ⇒ [Γc ; d ⊢〚χ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
      | sem_NRAMapProduct : forall e1 e2 d c1 c2,
          nra_sem e1 d (dcoll c1) ->                      (**r   [Γc ; d ⊢〚e₁〛⇓ {c₁}] *)
          nra_sem_map_product e2 c1 c2 ->                 (**r ∧ [Γc ; {c₁} ⊢〚e₂〛⋈ᵈ ⇓ {c₂}] *)
          nra_sem (NRAMapProduct e2 e1) d (dcoll c2)      (**r ⇒ [Γc ; d ⊢〚⋈ᵈ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
      | sem_NRAProduct_empty : forall e1 e2 d,            (**r Does not evaluate [e₂] if [e₁] is empty. This facilitates translation to cNNRC *)
          nra_sem e1 d (dcoll nil) ->                     (**r   [Γc ; d ⊢〚e₁〛⇓ {}] *)
          nra_sem (NRAProduct e1 e2) d (dcoll nil)        (**r ⇒ [Γc ; d ⊢〚e₁ × e₂〛⇓ {}] *)
      | sem_NRAProduct_nonEmpty : forall e1 e2 d c1 c2 c3,
          nra_sem e1 d (dcoll c1) ->                      (**r   [Γc ; d ⊢〚e₁〛⇓ {c₁}] *)
          c1 <> nil ->                                    (**r ∧ [{c₁} ≠ {}] *)
          nra_sem e2 d (dcoll c2) ->                      (**r ∧ [Γc ; d ⊢〚e₂〛⇓ {c₂}] *)
          product_sem c1 c2 c3 ->                         (**r ∧ [{c₁} × {c₂} ⇓ {c₃}] *)
          nra_sem (NRAProduct e1 e2) d (dcoll c3)         (**r ⇒ [Γc ; d ⊢〚e₁ × e₂〛⇓ {c₃}] *)
      | sem_NRASelect : forall e1 e2 d c1 c2,
          nra_sem e1 d (dcoll c1) ->                      (**r   [Γc ; d ⊢〚e₁〛⇓ {c₁}] *)
          nra_sem_select e2 c1 c2 ->                      (**r ∧ [Γc ; {c₁} ⊢〚e₂〛σ ⇓ {c₂}] *)
          nra_sem (NRASelect e2 e1) d (dcoll c2)          (**r ⇒ [Γc ; d ⊢〚σ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
      | sem_NRADefault_empty : forall e1 e2 d d2,
          nra_sem e1 d  (dcoll nil) ->                    (**r   [Γc ; d ⊢〚e₁〛⇓ {}] *)
          nra_sem e2 d d2 ->                              (**r ∧ [Γc ; d ⊢〚e₂〛⇓ d₂] *)
          nra_sem (NRADefault e1 e2) d d2                 (**r ⇒ [Γc ; d ⊢〚e₁ ∥ e₂〛⇓ d₂] *)
      | sem_NRADefault_not_empty : forall e1 e2 d d1,
          nra_sem e1 d d1 ->                              (**r   [Γc ; d ⊢〚e₁〛⇓ d₁] *)
          d1 <> dcoll nil ->                              (**r ∧ [d₁ ≠ {}] *)
          nra_sem (NRADefault e1 e2) d d1                 (**r ⇒ [Γc ; d ⊢〚e₁ ∥ e₂〛⇓ d₁] *)
      | sem_NRAEither_left : forall e1 e2 d d1,
          nra_sem e1 d d1 ->                              (**r   [Γc ; d ⊢〚e₁〛⇓ d₁] *)
          nra_sem (NRAEither e1 e2) (dleft d) d1          (**r ⇒ [Γc ; (dleft d) ⊢〚either e₁ e₂〛⇓ d₁] *)
      | sem_NRAEither_right : forall e1 e2 d d2,
          nra_sem e2 d d2 ->                              (**r   [Γc ; d ⊢〚e₂〛⇓ d₂] *)
          nra_sem (NRAEither e1 e2) (dright d) d2         (**r ⇒ [Γc ; (dright d) ⊢〚either e₁ e₂〛⇓ d₂] *)
      | sem_NRAEitherConcat_left : forall e1 e2 d r1 r2,
          nra_sem e1 d (dleft (drec r1)) ->               (**r   [Γc ; d ⊢〚e₁〛⇓ (dleft [r₁])] *)
          nra_sem e2 d (drec r2) ->                       (**r ∧ [Γc ; d ⊢〚e₂〛⇓ [r₂]] *)
          nra_sem (NRAEitherConcat e1 e2) d               (**r ⇒ [Γc ; d ⊢〚either⊕ e₁ e₂〛⇓ (dleft [r₁]⊕[r₂]]) *)
                  (dleft (drec (rec_concat_sort r1 r2)))
      | sem_NRAEitherConcat_right : forall e1 e2 d r1 r2,
          nra_sem e1 d (dright (drec r1)) ->              (**r   [Γc ; d ⊢〚e₁〛⇓ (dright [r₁])] *)
          nra_sem e2 d (drec r2) ->                       (**r ∧ [Γc ; d ⊢〚e₂〛⇓ [r₂]] *)
          nra_sem (NRAEitherConcat e1 e2) d               (**r ⇒ [Γc ; d ⊢〚either⊕ e₁ e₂〛⇓ (dright [r₁]⊕[r₂]]) *)
                  (dright (drec (rec_concat_sort r1 r2)))
      | sem_NRAApp : forall e1 e2 d d1 d2,
          nra_sem e1 d d1 ->                              (**r   [Γc ; d ⊢〚e₁〛⇓ d₁] *)
          nra_sem e2 d1 d2 ->                             (**r   [Γc ; d₁ ⊢〚e₂〛⇓ d₂] *)
          nra_sem (NRAApp e2 e1) d d2                     (**r ⇒ [Γc ; d ⊢〚e₂ ∘ e₁〛⇓ d₂] *)
      with nra_sem_map: nra -> list data -> list data -> Prop :=
      | sem_NRAMap_empty : forall e,
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
          map_concat_sem d1 c3 c4 ->                  (**r ∧ [d₁ χ⊕ c₃ ⇓ c₄] *)
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
              lift_oncoll (fun d1 => lift dcoll (lift_map (nra_eval e2) d1)) c1
          in olift aux_map (nra_eval e1 din)
        | NRAMapProduct e2 e1 =>
          let aux_mapconcat c1 :=
              lift_oncoll (fun d1 => lift dcoll (omap_product (nra_eval e2) d1)) c1
          in olift aux_mapconcat (nra_eval e1 din)
        | NRAProduct e1 e2 =>
          (* Note: (fun _ => nra_eval e2 din) does not depend on
             input, but we still use a nested loop and delay op2
             evaluation so it does not fail in case the op1 operand is
             an empty collection -- this facilitates translation for
             the NNRC version where one cannot easily enforce an eager
             evaluation. *)
          let aux_product d :=
              lift_oncoll
                (fun c1 => lift dcoll (omap_product (fun _ => nra_eval e2 din) c1)) d
          in olift aux_product (nra_eval e1 din)
        | NRASelect e2 e1 =>
          let pred d1 :=
              match nra_eval e2 d1 with
              | Some (dbool b) => Some b
              | _ => None
              end
          in
          let aux_select d :=
              lift_oncoll (fun d1 => lift dcoll (lift_filter pred d1)) d
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
      (** Auxiliary correctness lemmas for map, map_product and select judgments. *)
      Lemma nra_eval_map_correct : forall e l1 l2,
        (forall d1 d2 : data, nra_eval e d1 = Some d2 -> nra_sem e d1 d2) ->
        lift_map (nra_eval e) l1 = Some l2 ->
        nra_sem_map e l1 l2.
      Proof.
        intros.
        revert l2 H0.
        induction l1; simpl in *; intros.
        - inversion H0; econstructor.
        - case_eq (nra_eval e a); intros; rewrite H1 in *; [|congruence].
          unfold lift in H0.
          case_eq (lift_map (nra_eval e) l1); intros; rewrite H2 in *; [|congruence].
          specialize (IHl1 l eq_refl).
          inversion H0.
          econstructor; eauto.
      Qed.
          
      Lemma nra_eval_map_product_correct : forall e l1 l2,
        (forall d1 d2 : data, nra_eval e d1 = Some d2 -> nra_sem e d1 d2) ->
        omap_product (nra_eval e) l1 = Some l2 ->
        nra_sem_map_product e l1 l2.
      Proof.
        intros.
        revert l2 H0.
        induction l1; simpl in *; intros.
        - inversion H0; econstructor.
        - generalize (omap_product_cons_inv (nra_eval e) l1 a l2 H0); intros.
          elim H1; clear H1; intros.
          elim H1; clear H1; intros.
          elim H1; clear H1; intros.
          elim H2; clear H2; intros.
          subst.
          unfold oncoll_map_concat in H1.
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
             | Some (dfloat _) => None
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
                  | Some (dfloat _) => None
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

      Lemma omap_product_some_is_oproduct d1 d2 l1 l2 :
        omap_product (fun _ : data => Some d2) (d1 :: l1) = Some l2 ->
        exists l, d2 = dcoll l /\ oproduct (d1::l1) l = Some l2.
      Proof.
        intros.
        unfold omap_product, oproduct in *; simpl in *.
        case_eq d2; intros; rewrite H0 in *; simpl in *; try congruence.
        exists l; split; [reflexivity| ].
        unfold oncoll_map_concat in H.
        destruct (omap_concat d1 l); [|congruence].
        assumption.
      Qed.

      (** Evaluation is correct wrt. the NRA semantics. *)

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
          case_eq (lift_map (nra_eval e1) l); intros; rewrite H1 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          apply nra_eval_map_correct; auto.
        - unfold olift in H.
          case_eq (nra_eval e2 d1); intros; rewrite H0 in *; [|congruence].
          unfold lift_oncoll in H.
          destruct d; simpl in H; try congruence.
          unfold lift in H.
          case_eq (omap_product (nra_eval e1) l); intros; rewrite H1 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          apply nra_eval_map_product_correct; auto.
        - unfold olift2 in H.
          case_eq (nra_eval e1 d1); intros; rewrite H0 in *; simpl in *; [|congruence].
          destruct d; simpl in *; try congruence.
          destruct l; simpl in *.
          (* Left collection is empty *)
          + inversion H; subst.
            econstructor; eauto.
          (* Left collection is not empty *)
          + specialize (IHe1 d1 (dcoll (d::l)) H0).
            unfold lift in H.
            case_eq (nra_eval e2 d1); intros; rewrite H1 in *.
            * case_eq (omap_product (fun _ : data => nra_eval e2 d1) (d :: l)); intros;
                rewrite H1 in H2; simpl in *; rewrite H2 in *; [|congruence].
              inversion H; clear H; subst.
              elim (omap_product_some_is_oproduct d d0 l l0 H2); intros.
              elim H; clear H; intros; subst.
              econstructor; eauto. congruence.
              apply oproduct_correct; assumption.
            * unfold omap_product in H; simpl in H.
              congruence.
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
                  | Some (dfloat _) => None
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
      Qed.
 
      (** Auxiliary lemmas used in the completeness theorem *)

      Lemma nra_map_eval_complete e c1 c2:
        (forall d1 d2 : data, nra_sem e d1 d2 -> nra_eval e d1 = Some d2) ->
        (nra_sem_map e c1 c2) ->
        lift dcoll (lift_map (nra_eval e) c1) = Some (dcoll c2).
      Proof.
        intros.
        revert c2 H0.
        induction c1; simpl in *; intros.
        - inversion H0; reflexivity.
        - inversion H0; clear H0; subst.
          rewrite (H a d2 H4); simpl.
          specialize (IHc1 c3 H6).
          unfold lift in *.
          case_eq (lift_map (nra_eval e) c1); intros; rewrite H0 in *; [|congruence].
          inversion IHc1; clear IHc1; subst; reflexivity.
      Qed.
        
      Lemma nra_map_product_eval_complete e c1 c2:
        (forall d1 d2 : data, nra_sem e d1 d2 -> nra_eval e d1 = Some d2) ->
        (nra_sem_map_product e c1 c2) ->
        lift dcoll (omap_product (nra_eval e) c1) = Some (dcoll c2).
      Proof.
        intros.
        revert c2 H0.
        induction c1; simpl in *; intros.
        - inversion H0; reflexivity.
        - inversion H0; clear H0; subst.
          unfold omap_product in *.
          unfold oncoll_map_concat in *; simpl.
          rewrite (H a (dcoll c4) H3); simpl.
          rewrite <- omap_concat_correct_and_complete in H5.
          rewrite H5; simpl.
          specialize (IHc1 c3 H7).
          unfold lift in *.
          destruct (lift_flat_map
             (fun a : data =>
              match nra_eval e a with
              | Some dunit => None
              | Some (dnat _) => None
              | Some (dfloat _) => None
              | Some (dbool _) => None
              | Some (dstring _) => None
              | Some (dcoll y) => omap_concat a y
              | Some (drec _) => None
              | Some (dleft _) => None
              | Some (dright _) => None
              | Some (dbrand _ _) => None
              | Some (dforeign _) => None
              | None => None
              end) c1); [|congruence].
          inversion IHc1; reflexivity.
      Qed.
        
      Lemma nra_select_eval_complete e c1 c2:
        (forall d1 d2 : data, nra_sem e d1 d2 -> nra_eval e d1 = Some d2) ->
        (nra_sem_select e c1 c2) ->
        lift dcoll
             (lift_filter
                (fun d0 : data =>
                   match nra_eval e d0 with
                   | Some dunit => None
                   | Some (dnat _) => None
                   | Some (dfloat _) => None
                   | Some (dbool b) => Some b
                   | Some (dstring _) => None
                   | Some (dcoll _) => None
                   | Some (drec _) => None
                   | Some (dleft _) => None
                   | Some (dright _) => None
                   | Some (dbrand _ _) => None
                   | Some (dforeign _) => None
                   | None => None
                   end) c1) = Some (dcoll c2).
      Proof.
        intros.
        revert c2 H0.
        induction c1; simpl in *; intros.
        - inversion H0; reflexivity.
        - inversion H0; clear H0; subst.
          (* condition is true *)
          + rewrite (H a (dbool true) H4); simpl.
            specialize (IHc1 c3 H6).
            destruct
              (lift_filter
                 (fun d0 : data =>
                    match nra_eval e d0 with
                    | Some dunit => None
                    | Some (dnat _) => None
                    | Some (dfloat _) => None
                    | Some (dbool b) => Some b
                    | Some (dstring _) => None
                    | Some (dcoll _) => None
                    | Some (drec _) => None
                    | Some (dleft _) => None
                    | Some (dright _) => None
                    | Some (dbrand _ _) => None
                    | Some (dforeign _) => None
                    | None => None
                    end) c1); simpl in *; [|congruence].
            inversion IHc1; reflexivity.
          + rewrite (H a (dbool false) H4); simpl.
            specialize (IHc1 c2 H6).
            destruct
              (lift_filter
                 (fun d0 : data =>
                    match nra_eval e d0 with
                    | Some dunit => None
                    | Some (dnat _) => None
                    | Some (dfloat _) => None
                    | Some (dbool b) => Some b
                    | Some (dstring _) => None
                    | Some (dcoll _) => None
                    | Some (drec _) => None
                    | Some (dleft _) => None
                    | Some (dright _) => None
                    | Some (dbrand _ _) => None
                    | Some (dforeign _) => None
                    | None => None
                    end) c1); simpl in *; [|congruence].
            inversion IHc1; reflexivity.
      Qed.

      (** Evaluation is complete wrt. the NRA semantics. *)

      Lemma nra_eval_complete : forall e d1 d2,
          nra_sem e d1 d2 ->
          nra_eval e d1 = Some d2.
      Proof.
        induction e; intros.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe1 d1 d0 H3);
            rewrite (IHe2 d1 d3 H6); simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe d1 d0 H2); simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe2 d1 (dcoll c1) H2); simpl.
          apply nra_map_eval_complete; auto.
        - inversion H; subst; simpl.
          rewrite (IHe2 d1 (dcoll c1) H2); simpl.
          apply nra_map_product_eval_complete; auto.
        - inversion H; subst; simpl.
          (* empty first collection *)
          + rewrite (IHe1 d1 (dcoll nil) H4); reflexivity.
          + destruct c1; [congruence| ]; clear H3.
            rewrite (IHe1 d1 (dcoll (d :: c1)) H2); simpl.
            rewrite <- oproduct_correct_and_complete in H7.
            rewrite (IHe2 d1 (dcoll c2) H4).
            unfold oproduct in H7.
            unfold omap_product.
            unfold oncoll_map_concat.
            unfold omap_concat in *.
            rewrite H7; reflexivity.
        - inversion H; subst; simpl.
          rewrite (IHe2 d1 (dcoll c1) H2); simpl.
          apply nra_select_eval_complete; auto.
        - inversion H; subst; simpl.
          (* empty collection case *)
          + rewrite (IHe1 d1 (dcoll nil) H2); simpl; auto.
          (* non-empty collection case *)
          + rewrite (IHe1 d1 d2 H2); simpl; auto.
            destruct d2; try congruence.
            destruct l; congruence.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl.
          (* left case *)
          + rewrite (IHe1 d1 (dleft (drec r1)) H2); simpl.
            rewrite (IHe2 d1 (drec r2) H5); reflexivity.
          (* right case *)
          + rewrite (IHe1 d1 (dright (drec r1)) H2); simpl.
            rewrite (IHe2 d1 (drec r2) H5); reflexivity.
        - inversion H; subst; simpl.
          rewrite (IHe2 d1 d0 H2); simpl.
          rewrite (IHe1 d0 d2 H5); reflexivity.
      Qed.

      (** Main equivalence theorem. *)
      
      Theorem nra_eval_correct_and_complete : forall e d d',
          nra_eval e d = Some d' <-> nra_sem e d d'.
      Proof.
        split.
        apply nra_eval_correct.
        apply nra_eval_complete.
      Qed.

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
          apply (lift_map_Forall e H1); eauto.
        - intros;
            specialize (IHop2 d);
            destruct (nra_eval op2 d); simpl in *; try discriminate;
              specialize (IHop2 _ (eq_refl _) H0).
          destruct d0; simpl in *; try discriminate.
          apply some_lift in H; destruct H; subst.
          constructor.
          inversion IHop2; subst.
          unfold omap_product in *.
          apply (lift_flat_map_Forall e H1); intros.
          specialize (IHop1 x0).
          unfold oncoll_map_concat in H.
          match_destr_in H.
          specialize (IHop1 _ (eq_refl _) H2).
          unfold omap_concat in H.
          match_destr_in H.
          inversion IHop1; subst.
          apply (lift_map_Forall H H4); intros.
          eapply (data_normalized_orecconcat H3); trivial.
        - intros;
            specialize (IHop1 d);
            destruct (nra_eval op1 d); simpl in *; try discriminate.
          specialize (IHop1 _ (eq_refl _) H0).
          destruct d0; simpl in *; try discriminate.
          apply some_lift in H; destruct H; subst.
          constructor.
          inversion IHop1; subst.
          unfold omap_product in *.
          apply (lift_flat_map_Forall e H1); intros.
          specialize (IHop2 d).
          unfold oncoll_map_concat in H.
          match_destr_in H.
          specialize (IHop2 _ (eq_refl _) H0).
          unfold omap_concat in H.
          match_destr_in H.
          inversion IHop2; subst.
          apply (lift_map_Forall H H4); intros.
          eapply (data_normalized_orecconcat H3); trivial.
        - intros;
          specialize (IHop2 d);
          destruct (nra_eval op2 d); simpl in *; try discriminate;
            specialize (IHop2 _ (eq_refl _) H0).
          destruct d0; simpl in *; try discriminate.
          apply some_lift in H; destruct H; subst.      
          constructor.
          inversion IHop2; subst.
          unfold omap_product in *.
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

Tactic Notation "nra_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NRAGetConstant"%string
  | Case_aux c "NRAID"%string
  | Case_aux c "NRAConst"%string
  | Case_aux c "NRABinop"%string
  | Case_aux c "NRAUnop"%string
  | Case_aux c "NRAMap"%string
  | Case_aux c "NRAMapProduct"%string
  | Case_aux c "NRAProduct"%string
  | Case_aux c "NRASelect"%string
  | Case_aux c "NRADefault"%string
  | Case_aux c "NRAEither"%string
  | Case_aux c "NRAEitherConcat"%string
  | Case_aux c "NRAApp"%string ].

(* end hide *)

