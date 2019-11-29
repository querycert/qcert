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

(** cNRAEnv is the Core Nested Relational Algebra with
Environments. *)

(** cNRAEnv is a small pure language without functions based on
combinators (i.e., with no variables). Expressions in cNRAEnv take two
values as input, a current value and a value that can encode an
environment. *)

(** Summary:
- Language: cNRAEnv (Core Nested Relational Algebra with Environments)
- Based on: "Handling Environments in a Nested Relational Algebra with
  Combinators and an Implementation in a Verified Query Compiler", by
  Joshua Auerbach, Martin Hirzel, Louis Mandel, Avraham Shinnar and
  Jérôme Siméon (ACM SIGMOD'2017 conference).
- translating to cNRAEnv: CAMP, NRA, NRAEnv
- translating from cNRAEnv: cNNRC, NRAEnv *)

(** Compared to the version from Hirzel et al:
- We add two operators for matching against either values ([Either]
  and [EitherConcat]).
*)

Require Import String.
Require Import List.
Require Import Compare_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRARuntime.

Section cNRAEnv.
  Context {fruntime:foreign_runtime}.

  (** * Abstract Syntax *)

  Section Syntax.
  
  (** By convention, "static" parameters come first, followed by
    so-called dependent operators. This allows for easy instanciation
    on those parameters *)

    Inductive nraenv_core : Set :=
    | cNRAEnvGetConstant : string -> nraenv_core
    | cNRAEnvID : nraenv_core
    | cNRAEnvConst : data -> nraenv_core
    | cNRAEnvBinop : binary_op -> nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvUnop : unary_op -> nraenv_core -> nraenv_core
    | cNRAEnvMap : nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvMapProduct : nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvProduct : nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvSelect : nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvDefault : nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvEither :  nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvEitherConcat :  nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvApp : nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvEnv : nraenv_core
    | cNRAEnvAppEnv : nraenv_core -> nraenv_core -> nraenv_core
    | cNRAEnvMapEnv : nraenv_core -> nraenv_core
    .

    (** Equality between two cNRAEnv expressions is decidable. *)
  
    Global Instance nraenv_core_eqdec : EqDec nraenv_core eq.
    Proof.
      change (forall x y : nraenv_core,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec | apply data_eqdec | apply string_eqdec].
    Defined.

  End Syntax.

  Tactic Notation "nraenv_core_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "cNRAEnvGetConstant"%string
    | Case_aux c "cNRAEnvID"%string
    | Case_aux c "cNRAEnvConst"%string
    | Case_aux c "cNRAEnvBinop"%string
    | Case_aux c "cNRAEnvUnop"%string
    | Case_aux c "cNRAEnvMap"%string
    | Case_aux c "cNRAEnvMapProduct"%string
    | Case_aux c "cNRAEnvProduct"%string
    | Case_aux c "cNRAEnvSelect"%string
    | Case_aux c "cNRAEnvDefault"%string
    | Case_aux c "cNRAEnvEither"%string
    | Case_aux c "cNRAEnvEitherConcat"%string
    | Case_aux c "cNRAEnvApp"%string
    | Case_aux c "cNRAEnvEnv"%string
    | Case_aux c "cNRAEnvAppEnv"%string
    | Case_aux c "cNRAEnvMapEnv"%string].
  
  (** * Semantics *)
  
  Section Semantics.
    (** Part of the context is fixed for the rest of the development:
- [h] is the brand relation
- [constant_env] is the global environment *)

    Context (h:list(string*string)).
    Context (constant_env:list (string*data)).

    (** ** Denotational Semantics *)

    (** The semantics is defined using the main judgment [Γc ; γ ; d ⊢
    〚e〛⇓ d'] ([nraenv_core_sem]) where [Γc] is the global
    environment, [γ] is the reified input environment, [d] is the
    input value, [e] the cNRAEnv expression and [d'] the resulting
    value. *)
    
    (** The auxiliary judgment [Γc ; γ ; {c₁} ⊢〚e〛χ ⇓ {c₂}]
    ([nraenv_core_sem_map]) is used in the definition of the map [χ]
    operator. *)
    
    (** The auxiliary judgment [Γc ; γ ; {c₁} ⊢〚e〛⋈ᵈ ⇓ {c₂}]
    ([nra_map_product_select]) is used in the definition of the
    dependant product [⋈ᵈ] operator. *)
    
    (** The auxiliary judgment [Γc ; γ ; {c₁} ⊢〚e〛σ ⇓ {c₂}]
    ([nraenv_core_sem_select]) is used in the definition of the
    selection [σ] operator. *)
    
    (** The auxiliary judgment [Γc ; {c₁} ; d ⊢〚e〛χᵉ ⇓ {c₂}]
    ([nraenv_core_sem_map_env]) is used in the definition of the map
    over environment [χᵉ] operator. *)
    
    Section Denotation.
      Inductive nraenv_core_sem: nraenv_core -> data -> data -> data -> Prop :=
      | sem_cNRAEnvGetConstant : forall v env d d1,
          edot constant_env v = Some d1 ->                   (**r   [Γc(v) = d₁] *)
          nraenv_core_sem (cNRAEnvGetConstant v) env d d1    (**r ⇒ [Γc ; γ ; d ⊢〚$$v〛⇓ d₁] *)
      | sem_cNRAEnvID : forall env d,
          nraenv_core_sem cNRAEnvID env d d                  (**r   [Γc ; γ ; d ⊢ ID ⇓ d] *)
      | sem_cNRAEnvConst : forall env d d1 d2,
          normalize_data h d1 = d2 ->                        (**r   [norm(d₁) = d₂] *)
          nraenv_core_sem (cNRAEnvConst d1) env d d2         (**r ⇒ [Γc ; γ ; d ⊢〚d₁〛⇓ d₂] *)
      | sem_cNRAEnvBinop : forall bop e1 e2 env d d1 d2 d3,
          nraenv_core_sem e1 env d d1 ->                     (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          nraenv_core_sem e2 env d d2 ->                     (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ d₂] *)
          binary_op_eval h bop d1 d2 = Some d3 ->            (**r ∧ [d₁ ⊠ d₂ = d₃] *)
          nraenv_core_sem (cNRAEnvBinop bop e1 e2) env d d3  (**r ⇒ [Γc ; γ ; d ⊢〚e₁ ⊠ e₂〛⇓ d₃] *)
      | sem_cNRAEnvUnop : forall uop e env d d1 d2,
          nraenv_core_sem e env d d1 ->                      (**r   [Γc ; γ ; d ⊢〚e〛⇓ d₁] *)
          unary_op_eval h uop d1 = Some d2 ->                (**r ∧ [⊞ d₁ = d₂] *)
          nraenv_core_sem (cNRAEnvUnop uop e) env d d2       (**r ⇒ [Γc ; γ ; d ⊢〚⊞ e〛⇓ d₂] *)
      | sem_cNRAEnvMap : forall e1 e2 env d c1 c2,
          nraenv_core_sem e1 env d (dcoll c1) ->             (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          nraenv_core_sem_map e2 env c1 c2 ->                (**r ∧ [Γc ; γ ; {c₁} ⊢〚e₂〛χ ⇓ {c₂}] *)
          nraenv_core_sem (cNRAEnvMap e2 e1) env d (dcoll c2)(**r ⇒ [Γc ; γ ; d ⊢〚χ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
      | sem_cNRAEnvMapProduct : forall e1 e2 env d c1 c2,
          nraenv_core_sem e1 env d (dcoll c1) ->             (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          nraenv_core_sem_map_product e2 env c1 c2 ->        (**r ∧ [Γc ; γ ; {c₁} ⊢〚e₂〛⋈ᵈ ⇓ {c₂}] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; d ⊢〚⋈ᵈ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
            (cNRAEnvMapProduct e2 e1) env d (dcoll c2)
      | sem_cNRAEnvProduct_empty : forall e1 e2 env d,       (**r Does not evaluate [e₂] if [e₁] is empty. This facilitates translation to cNNRC *)
          nraenv_core_sem e1 env d (dcoll nil) ->            (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {}] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; d ⊢〚e₁ × e₂〛⇓ {}] *)
            (cNRAEnvProduct e1 e2) env d (dcoll nil)
      | sem_cNRAEnvProduct_nonEmpty : forall e1 e2 env d c1 c2 c3,
          nraenv_core_sem e1 env d (dcoll c1) ->             (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          c1 <> nil ->                                       (**r ∧ [{c₁} ≠ {}] *)
          nraenv_core_sem e2 env d (dcoll c2) ->             (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ {c₂}] *)
          product_sem c1 c2 c3 ->                            (**r ∧ [{c₁} × {c₂} ⇓ {c₃}] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; d ⊢〚e₁ × e₂〛⇓ {c₃}] *)
            (cNRAEnvProduct e1 e2) env d (dcoll c3)
      | sem_cNRAEnvSelect : forall e1 e2 env d c1 c2,
          nraenv_core_sem e1 env d (dcoll c1) ->             (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          nraenv_core_sem_select e2 env c1 c2 ->             (**r ∧ [Γc ; γ ; {c₁} ⊢〚e₂〛σ ⇓ {c₂}] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; d ⊢〚σ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
            (cNRAEnvSelect e2 e1) env d (dcoll c2)
      | sem_cNRAEnvDefault_empty : forall e1 e2 env d d2,
          nraenv_core_sem e1 env d  (dcoll nil) ->           (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {}] *)
          nraenv_core_sem e2 env d d2 ->                     (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ d₂] *)
          nraenv_core_sem (cNRAEnvDefault e1 e2) env d d2    (**r ⇒ [Γc ; γ ; d ⊢〚e₁ ∥ e₂〛⇓ d₂] *)
      | sem_cNRAEnvDefault_not_empty : forall e1 e2 env d d1,
          nraenv_core_sem e1 env d d1 ->                     (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          d1 <> dcoll nil ->                                 (**r ∧ [d₁ ≠ {}] *)
          nraenv_core_sem (cNRAEnvDefault e1 e2) env d d1    (**r ⇒ [Γc ; γ ; d ⊢〚e₁ ∥ e₂〛⇓ d₁] *)
      | sem_cNRAEnvEither_left : forall e1 e2 env d d1,
          nraenv_core_sem e1 env d d1 ->                     (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; (dleft d) ⊢〚either e₁ e₂〛⇓ d₁] *)
            (cNRAEnvEither e1 e2) env (dleft d) d1
      | sem_cNRAEnvEither_right : forall e1 e2 env d d2,
          nraenv_core_sem e2 env d d2 ->                     (**r   [Γc ; γ ; d ⊢〚e₂〛⇓ d₂] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; (dright d) ⊢〚either e₁ e₂〛⇓ d₂] *)
            (cNRAEnvEither e1 e2) env (dright d) d2
      | sem_cNRAEnvEitherConcat_left : forall e1 e2 env d r1 r2,
          nraenv_core_sem e1 env d (dleft (drec r1)) ->      (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ (dleft [r₁])] *)
          nraenv_core_sem e2 env d (drec r2) ->              (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ [r₂]] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; d ⊢〚either⊕ e₁ e₂〛⇓ (dleft [r₁]⊕[r₂]]) *)
            (cNRAEnvEitherConcat e1 e2) env d
            (dleft (drec (rec_concat_sort r1 r2)))
      | sem_cNRAEnvEitherConcat_right : forall e1 e2 env d r1 r2,
          nraenv_core_sem e1 env d (dright (drec r1)) ->     (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ (dright [r₁])] *)
          nraenv_core_sem e2 env d (drec r2) ->              (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ [r₂]] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; γ ; d ⊢〚either⊕ e₁ e₂〛⇓ (dright [r₁]⊕[r₂]]) *)
            (cNRAEnvEitherConcat e1 e2) env d
            (dright (drec (rec_concat_sort r1 r2)))
      | sem_cNRAEnvApp : forall e1 e2 env d d1 d2,
          nraenv_core_sem e1 env d d1 ->                     (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          nraenv_core_sem e2 env d1 d2 ->                    (**r   [Γc ; γ ; d₁ ⊢〚e₂〛⇓ d₂] *)
          nraenv_core_sem (cNRAEnvApp e2 e1) env d d2        (**r ⇒ [Γc ; γ ; d ⊢〚e₂ ∘ e₁〛⇓ d₂] *)
      | sem_cNRAEnvEnv : forall env d,
          nraenv_core_sem cNRAEnvEnv env d env               (**r   [Γc ; γ ; d ⊢ ENV ⇓ γ] *)
      | sem_cNRAEnvAppEnv : forall e1 e2 env d env1 d2,
          nraenv_core_sem e1 env d env1 ->                   (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ γ₁] *)
          nraenv_core_sem e2 env1 d d2 ->                    (**r   [Γc ; γ₁ ; d ⊢〚e₂〛⇓ d₂] *)
          nraenv_core_sem (cNRAEnvAppEnv e2 e1) env d d2     (**r ⇒ [Γc ; γ ; d ⊢〚e₂ ∘ᵉ e₁〛⇓ d₂] *)
      | sem_cNRAEnvMapEnv : forall e c1 d c2,
          nraenv_core_sem_map_env e c1 d c2 ->               (**r ∧ [Γc ; {c₁} ; d ⊢〚e〛χᵉ ⇓ {c₂}] *)
          nraenv_core_sem                                    (**r ⇒ [Γc ; {c₁} ; d ⊢〚χᵉ⟨e⟩〛⇓ {c₂}] *)
            (cNRAEnvMapEnv e) (dcoll c1) d (dcoll c2)
      with nraenv_core_sem_map: nraenv_core -> data -> list data -> list data -> Prop :=
      | sem_cNRAEnvMap_empty : forall e env,
          nraenv_core_sem_map e env nil nil                     (**r   [Γc ; γ ; {} ⊢〚e〛χ ⇓ {}] *)
      | sem_cNRAEnvMap_cons : forall e env d1 c1 d2 c2,
          nraenv_core_sem e env d1 d2 ->                        (**r   [Γc ; γ ; d₁ ⊢〚e〛⇓ d₂]  *)
          nraenv_core_sem_map e env c1 c2 ->                    (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛χ ⇓ {c₂}] *)
          nraenv_core_sem_map e env (d1::c1) (d2::c2)           (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛χ ⇓ {d₂::c₂}] *)
      with nraenv_core_sem_map_product: nraenv_core -> data -> list data -> list data -> Prop :=
      | sem_cNRAEnvMapProduct_empty : forall e env,
          nraenv_core_sem_map_product e env nil nil             (**r   [Γc ; γ ; {} ⊢〚e〛⋈ᵈ ⇓ {}] *)
      | sem_cNRAEnvMapProduct_cons : forall e env d1 c1 c2 c3 c4,
          nraenv_core_sem e env d1 (dcoll c3) ->                (**r   [Γc ; γ ; d₁ ⊢〚e〛⋈ᵈ ⇓ {c₃}]  *)
          map_concat_sem d1 c3 c4 ->                            (**r ∧ [d₁ χ⊕ c₃ ⇓ c₄] *)
          nraenv_core_sem_map_product e env c1 c2 ->            (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛⋈ᵈ ⇓ {c₂}] *)
          nraenv_core_sem_map_product e env (d1::c1) (c4 ++ c2) (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛⋈ᵈ ⇓ {c₄}∪{c₂}] *)
      with nraenv_core_sem_select: nraenv_core -> data -> list data -> list data -> Prop :=
      | sem_cNRAEnvSelect_empty : forall e env,
          nraenv_core_sem_select e env nil nil                  (**r   [Γc ; γ ; {} ⊢〚e〛σ ⇓ {}] *)
      | sem_cNRAEnvSelect_true : forall e env d1 c1 c2,
          nraenv_core_sem e env d1 (dbool true) ->              (**r   [Γc ; γ ; d₁ ⊢〚e〛σ ⇓ true]  *)
          nraenv_core_sem_select e env c1 c2 ->                 (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛σ ⇓ {c₂}] *)
          nraenv_core_sem_select e env (d1::c1) (d1::c2)        (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛σ ⇓ {d₁::c₂}] *)
      | sem_cNRAEnvSelect_false : forall e env d1 c1 c2,
          nraenv_core_sem e env d1 (dbool false) ->             (**r   [Γc ; γ ; d₁ ⊢〚e〛σ ⇓ false]  *)
          nraenv_core_sem_select e env c1 c2 ->                 (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛σ ⇓ {c₂}] *)
          nraenv_core_sem_select e env (d1::c1) c2              (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛σ ⇓ {c₂}] *)
      with nraenv_core_sem_map_env: nraenv_core -> list data -> data -> list data -> Prop :=
      | sem_cNRAEnvMapEnv_empty : forall e d,
          nraenv_core_sem_map_env e nil d nil                   (**r   [Γc ; {} ; d ⊢〚e〛χᵉ ⇓ {}] *)
      | sem_cNRAEnvMapEnv_cons : forall e d1 d c1 d2 c2,
          nraenv_core_sem e d1 d d2 ->                          (**r   [Γc ; d₁ ; d ⊢〚e〛⇓ d₂]  *)
          nraenv_core_sem_map_env e c1 d c2 ->                  (**r ∧ [Γc ; {c₁} ; d ⊢〚e〛χᵉ ⇓ {c₂}] *)
          nraenv_core_sem_map_env e (d1::c1) d (d2::c2)         (**r ⇒ [Γc ; {d₁::c₁} ; d ⊢〚e〛χᵉ ⇓ {d₂::c₂}] *)
      .

    End Denotation.

    Section Evaluation.

      Fixpoint nraenv_core_eval (e:nraenv_core) (envin: data) (din:data) : option data :=
        match e with
        | cNRAEnvGetConstant s =>
          edot constant_env s
        | cNRAEnvID =>
          Some din
        | cNRAEnvConst rd =>
          Some (normalize_data h rd)
        | cNRAEnvBinop bop e1 e2 =>
          olift2 (fun d1 d2 => binary_op_eval h bop d1 d2)
                 (nraenv_core_eval e1 envin din) (nraenv_core_eval e2 envin din)
        | cNRAEnvUnop uop e =>
          olift (fun d1 => unary_op_eval h uop d1)
                (nraenv_core_eval e envin din)
        | cNRAEnvMap e2 e1 =>
          let aux_map d :=
              lift_oncoll
                (fun c1 => lift dcoll (lift_map (nraenv_core_eval e2 envin) c1)) d
          in olift aux_map (nraenv_core_eval e1 envin din)
        | cNRAEnvMapProduct e2 e1 =>
          let aux_mapconcat d :=
              lift_oncoll
                (fun c1 => lift dcoll (omap_product (nraenv_core_eval e2 envin) c1)) d
          in olift aux_mapconcat (nraenv_core_eval e1 envin din)
        | cNRAEnvProduct e1 e2 =>
          (* Note: (fun y => nra_eval op2 x) does not depend on input,
             but we still use a nested loop and delay op2 evaluation
             so it does not fail in case the op1 operand is an empty
             collection -- this makes sure to align the semantics with
             the NNRC version. - Jerome *)
          let aux_product d :=
              lift_oncoll
                (fun c1 => lift dcoll (omap_product (fun _ => nraenv_core_eval e2 envin din) c1)) d
          in olift aux_product (nraenv_core_eval e1 envin din)
        | cNRAEnvSelect e2 e1 =>
          let pred d1 :=
              match nraenv_core_eval e2 envin d1 with
              | Some (dbool b) => Some b
              | _ => None
              end
          in
          let aux_select d :=
              lift_oncoll (fun d1 => lift dcoll (lift_filter pred d1)) d
          in
          olift aux_select (nraenv_core_eval e1 envin din)
        | cNRAEnvDefault e1 e2 =>
          olift (fun d1 =>
                   match d1 with
                   | dcoll nil => nraenv_core_eval e2 envin din
                   | _ => Some d1
                   end)
                (nraenv_core_eval e1 envin din)
        | cNRAEnvEither e1 e2 =>
          match din with
          | dleft d1 => nraenv_core_eval e1 envin d1
          | dright d2 => nraenv_core_eval e2 envin d2
          | _ => None
          end
        | cNRAEnvEitherConcat e1 e2 =>
          match nraenv_core_eval e1 envin din, nraenv_core_eval e2 envin din with
          | Some (dleft (drec l)), Some (drec t)  =>
            Some (dleft (drec (rec_concat_sort l t)))
          | Some (dright (drec r)), Some (drec t)  =>
            Some (dright (drec (rec_concat_sort r t)))
          | _, _ => None
          end
        | cNRAEnvApp e2 e1 =>
          olift (fun d1 => nraenv_core_eval e2 envin d1) (nraenv_core_eval e1 envin din)
        | cNRAEnvEnv =>
          Some envin
        | cNRAEnvAppEnv e2 e1 =>
          olift (fun env1 => nraenv_core_eval e2 env1 din) (nraenv_core_eval e1 envin din)
        | cNRAEnvMapEnv e =>
          lift_oncoll
            (fun c1 => lift dcoll
                            (lift_map ((fun env1 => nraenv_core_eval e env1 din)) c1)) envin
        end.

    End Evaluation.

    Section EvalCorrect.
      (** Auxiliary correctness lemmas for map, map_product, select and map_env judgments. *)
      Lemma nraenv_core_eval_map_correct : forall e env l1 l2,
        (forall env d1 d2 : data,
            nraenv_core_eval e env d1 = Some d2 -> nraenv_core_sem e env d1 d2) ->
        lift_map (nraenv_core_eval e env) l1 = Some l2 ->
        nraenv_core_sem_map e env l1 l2.
      Proof.
        intros.
        revert l2 H0.
        induction l1; simpl in *; intros.
        - inversion H0; econstructor.
        - case_eq (nraenv_core_eval e env a); intros; rewrite H1 in *; [|congruence].
          unfold lift in H0.
          case_eq (lift_map (nraenv_core_eval e env) l1); intros; rewrite H2 in *; [|congruence].
          specialize (IHl1 l eq_refl).
          inversion H0.
          econstructor; eauto.
      Qed.
          
      Lemma nraenv_core_eval_map_product_correct : forall e env l1 l2,
        (forall env d1 d2 : data,
            nraenv_core_eval e env d1 = Some d2 -> nraenv_core_sem e env d1 d2) ->
        omap_product (nraenv_core_eval e env) l1 = Some l2 ->
        nraenv_core_sem_map_product e env l1 l2.
      Proof.
        intros.
        revert l2 H0.
        induction l1; simpl in *; intros.
        - inversion H0; econstructor.
        - generalize (omap_product_cons_inv (nraenv_core_eval e env) l1 a l2 H0); intros.
          elim H1; clear H1; intros.
          elim H1; clear H1; intros.
          elim H1; clear H1; intros.
          elim H2; clear H2; intros.
          subst.
          unfold oncoll_map_concat in H1.
          case_eq (nraenv_core_eval e env a); intros; rewrite H3 in *; [|congruence].
          case_eq d; intros; rewrite H4 in H1; try congruence.
          subst.
          specialize (H env a (dcoll l) H3).
          rewrite omap_concat_correct_and_complete in H1.
          apply (sem_cNRAEnvMapProduct_cons e env a l1 x0 l x).
          + assumption.
          + assumption.
          + apply IHl1; assumption.
      Qed.

      Lemma nraenv_core_eval_select_correct e env l1 l2 :
        (forall env d1 d2 : data,
            nraenv_core_eval e env d1 = Some d2 -> nraenv_core_sem e env d1 d2) ->
        lift_filter
          (fun d1 : data =>
             match nraenv_core_eval e env d1 with
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
        nraenv_core_sem_select e env l1 l2.
      Proof.
        intro.
        revert l2; induction l1; simpl; intros.
        - inversion H0. econstructor.
        - case_eq (nraenv_core_eval e env a); intros; rewrite H1 in *; simpl in *.
          destruct d; simpl in *; try congruence.
          case_eq
            (lift_filter
               (fun d1 : data =>
                  match nraenv_core_eval e env d1 with
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

      Lemma nraenv_core_eval_map_env_correct : forall e l1 d l2,
        (forall env d1 d2 : data,
            nraenv_core_eval e env d1 = Some d2 -> nraenv_core_sem e env d1 d2) ->
        lift_map (fun env1 : data => nraenv_core_eval e env1 d) l1 = Some l2 ->
        nraenv_core_sem_map_env e l1 d l2.
      Proof.
        intros.
        revert l2 H0.
        induction l1; simpl in *; intros.
        - inversion H0; econstructor.
        - case_eq (nraenv_core_eval e a d); intros; rewrite H1 in *; [|congruence].
          unfold lift in H0.
          case_eq (lift_map (fun env1 : data => nraenv_core_eval e env1 d) l1);
            intros; rewrite H2 in *; [|congruence].
          specialize (IHl1 l eq_refl).
          inversion H0.
          econstructor; eauto.
      Qed.

      (** Evaluation is correct wrt. the cNRAEnv semantics. *)

      Lemma nraenv_core_eval_correct : forall e env d1 d2,
          nraenv_core_eval e env d1 = Some d2 ->
          nraenv_core_sem e env d1 d2.
      Proof.
        induction e; simpl; intros.
        - econstructor; eauto.
        - inversion H; econstructor; eauto.
        - inversion H; econstructor; eauto.
        - unfold olift2 in H.
          case_eq (nraenv_core_eval e1 env d1); intros; rewrite H0 in *; [|congruence].
          case_eq (nraenv_core_eval e2 env d1); intros; rewrite H1 in *; [|congruence].
          specialize (IHe1 env d1 d H0); specialize (IHe2 env d1 d0 H1);
            econstructor; eauto.
        - unfold olift in H.
          case_eq (nraenv_core_eval e env d1); intros; rewrite H0 in *; [|congruence].
          specialize (IHe env d1 d H0); econstructor; eauto.
        - unfold olift in H.
          case_eq (nraenv_core_eval e2 env d1); intros; rewrite H0 in *; [|congruence].
          unfold lift_oncoll in H.
          destruct d; simpl in H; try congruence.
          unfold lift in H.
          case_eq (lift_map (nraenv_core_eval e1 env) l); intros; rewrite H1 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          apply nraenv_core_eval_map_correct; auto.
        - unfold olift in H.
          case_eq (nraenv_core_eval e2 env d1); intros; rewrite H0 in *; [|congruence].
          unfold lift_oncoll in H.
          destruct d; simpl in H; try congruence.
          unfold lift in H.
          case_eq (omap_product (nraenv_core_eval e1 env) l); intros; rewrite H1 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          apply nraenv_core_eval_map_product_correct; auto.
        - unfold olift2 in H.
          case_eq (nraenv_core_eval e1 env d1); intros; rewrite H0 in *; simpl in *; [|congruence].
          destruct d; simpl in *; try congruence.
          destruct l; simpl in *.
          (* Left collection is empty *)
          + inversion H; subst.
            econstructor; eauto.
          (* Left collection is not empty *)
          + specialize (IHe1 env d1 (dcoll (d::l)) H0).
            unfold lift in H.
            case_eq (nraenv_core_eval e2 env d1); intros; rewrite H1 in *.
            * case_eq (omap_product (fun _ : data => nraenv_core_eval e2 env d1) (d :: l)); intros;
                rewrite H1 in H2; simpl in *; rewrite H2 in *; [|congruence].
              inversion H; clear H; subst.
              elim (omap_product_some_is_oproduct d d0 l l0 H2); intros.
              elim H; clear H; intros; subst.
              econstructor; eauto. congruence.
              apply oproduct_correct; assumption.
            * unfold omap_product in H; simpl in H.
              congruence.
        - unfold olift in H.
          case_eq (nraenv_core_eval e2 env d1); intros; rewrite H0 in *; [|congruence].
          unfold lift_oncoll in H.
          destruct d; simpl in H; try congruence.
          unfold lift in H.
          specialize (IHe2 env d1 (dcoll l) H0).
          case_eq
            (lift_filter
               (fun d1 : data =>
                  match nraenv_core_eval e1 env d1 with
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
          apply nraenv_core_eval_select_correct; auto.
        - unfold olift in H.
          case_eq (nraenv_core_eval e1 env d1); intros; rewrite H0 in *; [|congruence].
          elim (data_eq_dec d (dcoll nil)); intros.
          subst.
          + econstructor; eauto.
          + destruct d; inversion H; subst; auto;
              eapply sem_cNRAEnvDefault_not_empty; auto;
                destruct l; auto; inversion H; subst; auto.
            congruence.
        - destruct d1; try congruence.
          econstructor; apply IHe1; auto.
          econstructor; apply IHe2; auto.
        - case_eq (nraenv_core_eval e1 env d1); intros; rewrite H0 in *; [|congruence].
          destruct d; intros; try congruence.
         + destruct d; intros; try congruence.
           case_eq (nraenv_core_eval e2 env d1); intros; rewrite H1 in *; [|congruence].
           destruct d; intros; try congruence.
           inversion H; subst; clear H; intros.
           econstructor; eauto.
         + destruct d; intros; try congruence.
           case_eq (nraenv_core_eval e2 env d1); intros; rewrite H1 in *; [|congruence].
           destruct d; intros; try congruence.
           inversion H; subst; clear H; intros.
           econstructor; eauto.
        - unfold olift in H.
          case_eq (nraenv_core_eval e2 env d1); intros; rewrite H0 in *; [|congruence].
          econstructor; eauto.
        - inversion H; subst; econstructor.
        - unfold olift in H.
          case_eq (nraenv_core_eval e2 env d1); intros; rewrite H0 in *; [|congruence].
          econstructor; eauto.
        - unfold lift_oncoll in H.
          destruct env; simpl in H; try congruence.
          unfold lift in H.
          case_eq (lift_map (fun env1 : data => nraenv_core_eval e env1 d1) l);
            intros; rewrite H0 in *; [|congruence].
          inversion H; subst; clear H.
          econstructor; eauto.
          apply nraenv_core_eval_map_env_correct; auto.
      Qed.
 
      (** Auxiliary lemmas used in the completeness theorem *)

      Lemma nraenv_core_map_eval_complete e env c1 c2:
        (forall env d1 d2 : data,
            nraenv_core_sem e env d1 d2 -> nraenv_core_eval e env d1 = Some d2) ->
        (nraenv_core_sem_map e env c1 c2) ->
        lift dcoll (lift_map (nraenv_core_eval e env) c1) = Some (dcoll c2).
      Proof.
        intros.
        revert c2 H0.
        induction c1; simpl in *; intros.
        - inversion H0; reflexivity.
        - inversion H0; clear H0; subst.
          rewrite (H env a d2 H5); simpl.
          specialize (IHc1 c3 H7).
          unfold lift in *.
          case_eq (lift_map (nraenv_core_eval e env) c1); intros; rewrite H0 in *; [|congruence].
          inversion IHc1; clear IHc1; subst; reflexivity.
      Qed.

      Lemma nraenv_core_map_product_eval_complete e env c1 c2:
        (forall env d1 d2 : data,
            nraenv_core_sem e env d1 d2 -> nraenv_core_eval e env d1 = Some d2) ->
        (nraenv_core_sem_map_product e env c1 c2) ->
        lift dcoll (omap_product (nraenv_core_eval e env) c1) = Some (dcoll c2).
      Proof.
        intros.
        revert c2 H0.
        induction c1; simpl in *; intros.
        - inversion H0; reflexivity.
        - inversion H0; clear H0; subst.
          unfold omap_product in *.
          unfold oncoll_map_concat in *; simpl.
          rewrite (H env a (dcoll c4) H3); simpl.
          rewrite <- omap_concat_correct_and_complete in H6.
          rewrite H6; simpl.
          specialize (IHc1 c3 H8).
          unfold lift in *.
          destruct (lift_flat_map
             (fun a : data =>
              match nraenv_core_eval e env a with
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
        
      Lemma nraenv_core_select_eval_complete e env c1 c2:
        (forall env d1 d2 : data,
            nraenv_core_sem e env d1 d2 -> nraenv_core_eval e env d1 = Some d2) ->
        (nraenv_core_sem_select e env c1 c2) ->
        lift dcoll
             (lift_filter
                (fun d0 : data =>
                   match nraenv_core_eval e env d0 with
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
          + rewrite (H env a (dbool true) H5); simpl.
            specialize (IHc1 c3 H7).
            destruct
              (lift_filter
                 (fun d0 : data =>
                    match nraenv_core_eval e env d0 with
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
          + rewrite (H env a (dbool false) H5); simpl.
            specialize (IHc1 c2 H7).
            destruct
              (lift_filter
                 (fun d0 : data =>
                    match nraenv_core_eval e env d0 with
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

      Lemma nraenv_core_map_env_eval_complete e c1 d c2:
        (forall env d1 d2 : data,
            nraenv_core_sem e env d1 d2 -> nraenv_core_eval e env d1 = Some d2) ->
        (nraenv_core_sem_map_env e c1 d c2) ->
        lift dcoll (lift_map (fun env1 : data => nraenv_core_eval e env1 d) c1) = Some (dcoll c2).
      Proof.
        intros.
        revert c2 H0.
        induction c1; simpl in *; intros.
        - inversion H0; reflexivity.
        - inversion H0; clear H0; subst.
          rewrite (H a d d2 H4); simpl.
          specialize (IHc1 c3 H7).
          unfold lift in *.
          case_eq (lift_map (fun env1 : data => nraenv_core_eval e env1 d) c1);
            intros; rewrite H0 in *; [|congruence].
          inversion IHc1; clear IHc1; subst; reflexivity.
      Qed.

      (** Evaluation is complete wrt. the cNRAEnv semantics. *)

      Lemma nraenv_core_eval_complete : forall e env d1 d2,
          nraenv_core_sem e env d1 d2 ->
          nraenv_core_eval e env d1 = Some d2.
      Proof.
        induction e; intros.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe1 env d1 d0 H3);
            rewrite (IHe2 env d1 d3 H7); simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe env d1 d0 H2); simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe2 env d1 (dcoll c1) H2); simpl.
          apply nraenv_core_map_eval_complete; auto.
        - inversion H; subst; simpl.
          rewrite (IHe2 env d1 (dcoll c1) H2); simpl.
          apply nraenv_core_map_product_eval_complete; auto.
        - inversion H; subst; simpl.
          (* empty first collection *)
          + rewrite (IHe1 env d1 (dcoll nil) H5); reflexivity.
          + destruct c1; [congruence| ]; clear H3.
            rewrite (IHe1 env d1 (dcoll (d :: c1)) H2); simpl.
            rewrite <- oproduct_correct_and_complete in H8.
            rewrite (IHe2 env d1 (dcoll c2) H4).
            unfold oproduct in H8.
            unfold omap_product.
            unfold oncoll_map_concat.
            unfold omap_concat in *.
            rewrite H8; reflexivity.
        - inversion H; subst; simpl.
          rewrite (IHe2 env d1 (dcoll c1) H2); simpl.
          apply nraenv_core_select_eval_complete; auto.
        - inversion H; subst; simpl.
          (* empty collection case *)
          + rewrite (IHe1 env d1 (dcoll nil) H2); simpl; auto.
          (* non-empty collection case *)
          + rewrite (IHe1 env d1 d2 H2); simpl; auto.
            destruct d2; try congruence.
            destruct l; congruence.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl.
          (* left case *)
          + rewrite (IHe1 env d1 (dleft (drec r1)) H2); simpl.
            rewrite (IHe2 env d1 (drec r2) H6); reflexivity.
          (* right case *)
          + rewrite (IHe1 env d1 (dright (drec r1)) H2); simpl.
            rewrite (IHe2 env d1 (drec r2) H6); reflexivity.
        - inversion H; subst; simpl.
          rewrite (IHe2 env d1 d0 H2); simpl.
          rewrite (IHe1 env d0 d2 H6); reflexivity.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe2 env d1 env1 H2); simpl.
          rewrite (IHe1 env1 d1 d2 H6); reflexivity.
        - inversion H; subst; simpl.
          apply nraenv_core_map_env_eval_complete; auto.
      Qed.

      (** Main equivalence theorem. *)
      
      Theorem nraenv_core_eval_correct_and_complete : forall e env d d',
          nraenv_core_eval e env d = Some d' <-> nraenv_core_sem e env d d'.
      Proof.
        split.
        apply nraenv_core_eval_correct.
        apply nraenv_core_eval_complete.
      Qed.

    End EvalCorrect.

    (** Functions used to map dual input env/data into single input *)
    (* Input encoding *)

    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Fixpoint nra_of_nraenv_core (ae:nraenv_core) : nra :=
      match ae with
      | cNRAEnvGetConstant s =>
        NRAGetConstant s
      | cNRAEnvID =>
        nra_data
      | cNRAEnvConst d =>
        NRAConst d
      | cNRAEnvBinop b ae1 ae2 =>
        NRABinop b (nra_of_nraenv_core ae1) (nra_of_nraenv_core ae2)
      | cNRAEnvUnop u ae1 =>
        NRAUnop u (nra_of_nraenv_core ae1)
      | cNRAEnvMap ea1 ea2 =>
        NRAMap (nra_of_nraenv_core ea1)
               (unnest_two
                  "a1"
                  "PDATA"
                  (NRAUnop OpBag (nra_wrap_a1 (nra_of_nraenv_core ea2))))
      | cNRAEnvMapProduct ea1 ea2 =>
        (NRAMap (NRABinop OpRecConcat
                          (NRAUnop (OpDot "PDATA") NRAID)
                          (NRAUnop (OpDot "PDATA2") NRAID))
                (NRAMapProduct
                   (NRAMap (NRAUnop (OpRec "PDATA2") NRAID) (nra_of_nraenv_core ea1))
                   (unnest_two
                      "a1"
                      "PDATA"
                      (NRAUnop OpBag (nra_wrap_a1 (nra_of_nraenv_core ea2))))))
      | cNRAEnvProduct ea1 ea2 =>
        NRAProduct (nra_of_nraenv_core ea1) (nra_of_nraenv_core ea2)
      | cNRAEnvSelect ea1 ea2 =>
        (NRAMap (NRAUnop (OpDot "PDATA") NRAID)
                (NRASelect (nra_of_nraenv_core ea1)
                           (unnest_two
                              "a1"
                              "PDATA"
                              (NRAUnop OpBag (nra_wrap_a1 (nra_of_nraenv_core ea2))))))
      | cNRAEnvDefault ea1 ea2 =>
        NRADefault (nra_of_nraenv_core ea1) (nra_of_nraenv_core ea2)
      | cNRAEnvEither eal ear =>
        NRAApp
          (NRAEither (nra_of_nraenv_core eal) (nra_of_nraenv_core ear))
          (NRAEitherConcat
             (NRAApp (NRARecEither "PDATA") nra_data)
             (NRAUnop (OpRec "PBIND") nra_bind))
      | cNRAEnvEitherConcat ea1 ea2 =>
        NRAEitherConcat (nra_of_nraenv_core ea1) (nra_of_nraenv_core ea2)
      | cNRAEnvApp ea1 ea2 =>
        NRAApp (nra_of_nraenv_core ea1)
               (nra_wrap (nra_of_nraenv_core ea2))
      | cNRAEnvEnv => nra_bind
      | cNRAEnvAppEnv ea1 ea2 =>
        NRAApp (nra_of_nraenv_core ea1)
               (nra_context (nra_of_nraenv_core ea2) nra_data)
      | cNRAEnvMapEnv ea1 =>
        (* fix this: the nra_data should change to a nra_pair *)
        NRAMap (nra_of_nraenv_core ea1)
               (unnest_two
                  "a1"
                  "PBIND"
                  (NRAUnop OpBag (nra_wrap_bind_a1 nra_data)))
      end.

    Lemma lift_map_map_rec1 l s:
      lift_map (fun x : data => Some (drec ((s, x) :: nil))) l =
      Some (map (fun x : data => (drec ((s, x) :: nil))) l).
    Proof.
      induction l; try reflexivity; simpl; rewrite IHl; reflexivity.
    Qed.
    
    Lemma lift_map_map_rec2 env a1 l :
      (lift_map
         (fun x : data =>
            match x with
            | drec r1 =>
              Some
                (drec
                   (rec_concat_sort
                      (("PBIND", env) :: ("a1", dcoll a1) :: nil) r1))
            | _  => None
            end)
         (map (fun x : data => drec (("PDATA", x) :: nil)) l))
      =
      Some (map (fun x : data =>  drec (("PBIND", env) :: ("PDATA", x) :: ("a1", dcoll a1) :: nil)) l).
    Proof.
      induction l; try reflexivity; simpl.
      rewrite IHl; reflexivity.
    Qed.

    Lemma lift_map_map_rec3 d a1 l :
      (lift_map
         (fun x : data =>
            match x with
            | drec r1 =>
              Some
                (drec
                   (rec_concat_sort
                      (("PDATA", d) :: ("a1", dcoll a1) :: nil) r1))
            | _ => None
            end)
         (map (fun x : data => drec (("PBIND", x) :: nil)) l))
      =
      Some (map (fun x : data =>  drec (("PBIND", x) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil)) l).
    Proof.
      induction l; try reflexivity; simpl.
      rewrite IHl; reflexivity.
    Qed.

    Lemma option_id {A} (x:option A) :
      (match x with None => None | Some y => Some y end) = x.
    Proof.
      destruct x; reflexivity.
    Qed.
  
    Lemma lift_map_map_unnest2 env a l0 l1 :
      lift_map
        (fun x : data =>
           olift2
             (fun d1 d2 : data =>
                match d1 with
                | drec r1 =>
                  match d2 with
                  | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                  | _ => None
                  end
                | _ => None
                end)
             match x with
             | drec r => edot r "PDATA"
             | _ => None
             end
             match x with
             | drec r => edot r "PDATA2"
             | _ => None
             end)
        (map
           (fun x : data =>
              drec (("PBIND", env) :: ("PDATA", a) :: ("PDATA2", x) :: nil)) l0 ++ l1)
      =
      olift2 (fun d1 d2 => Some (d1 ++ d2))
             (lift_map
                (fun x : data =>
                   match a with
                   | drec r2 =>
                     match x with
                     | drec r1 => Some (drec (rec_concat_sort r2 r1))
                     | _ => None
                     end
                   | _ => None
                   end) l0)
             (lift_map
                (fun x : data =>
                   olift2
                     (fun d1 d2 : data =>
                        match d1 with
                        | drec r1 =>
                          match d2 with
                          | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                          | _ => None
                          end
                        | _ => None
                        end)
                     match x with
                     | drec r => edot r "PDATA"
                     | _ => None
                     end
                     match x with
                     | drec r => edot r "PDATA2"
                     | _ => None
                     end)
                l1).
    Proof.
      induction l0; try reflexivity; simpl.
      rewrite option_id; reflexivity.
      rewrite IHl0; clear IHl0; simpl.
      destruct a; try reflexivity.
      destruct a0; try reflexivity.
      simpl.
      destruct ((lift_map
                   (fun x : data =>
                      match x with
                      | drec r1 => Some (drec (rec_concat_sort l r1))
                      | _ => None
                      end) l0)); try reflexivity; simpl.
      generalize (     lift_map
                         (fun x : data =>
                            olift2
                              (fun d1 d2 : data =>
                                 match d1 with
                                 | drec r1 =>
                                   match d2 with
                                   | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                                   | _ => None
                                   end
                                 | _ => None
                                 end)
                              match x with
                              | drec r => edot r "PDATA"
                              | _ => None
                              end
                              match x with
                              | drec r => edot r "PDATA2"
                              | _ => None
                              end) l1); intros.
      destruct o; reflexivity.
    Qed.

    Lemma omap_concat_map_rec env a1 l :
      omap_concat
        (drec (("PBIND", env) :: ("a1", dcoll a1) :: nil))
        (map (fun x : data => drec (("PDATA", x) :: nil)) l)
      =
      Some (map (fun x : data =>  drec (("PBIND", env) :: ("PDATA", x) :: ("a1", dcoll a1) :: nil)) l).
    Proof.
      unfold omap_concat; simpl.
      induction l; try reflexivity; simpl.
      rewrite IHl; reflexivity.
    Qed.

    Lemma omap_concat_map_rec2 env a l :
      omap_concat (drec (("PBIND", env) :: ("PDATA", a) :: nil))
                  (map (fun x : data => drec (("PDATA2", x) :: nil)) l)
                  
      =
      Some (map (fun x : data =>  drec (("PBIND", env) :: ("PDATA", a) :: ("PDATA2", x) :: nil)) l).
    Proof.
      unfold omap_concat; simpl.
      induction l; try reflexivity; simpl.
      rewrite IHl; reflexivity.
    Qed.

    Lemma omap_concat_map_rec3 d a1 l :
      omap_concat
        (drec (("PDATA", d) :: ("a1", dcoll a1) :: nil))
        (map (fun x : data => drec (("PBIND", x) :: nil)) l)
      =
      Some (map (fun x : data =>  drec (("PBIND", x) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil)) l).
    Proof.
      unfold omap_concat; simpl.
      induction l; try reflexivity; simpl.
      rewrite IHl; reflexivity.
    Qed.

    Lemma omap_concat_unnest env a a1 l :
      omap_concat
        (drec (("PBIND", env) :: ("a1", dcoll a1) :: nil))
        (drec (("PDATA", a) :: nil)
              :: map (fun x : data => drec (("PDATA", x) :: nil)) l)
      =
      Some (drec (("PBIND", env) :: ("PDATA", a) :: ("a1", dcoll a1) :: nil) ::
                 (map (fun x : data => drec (("PBIND", env) :: ("PDATA", x) :: ("a1", dcoll a1) :: nil)) l)).
    Proof.
      unfold omap_concat; simpl.
      rewrite lift_map_map_rec2; simpl; reflexivity.
    Qed.

    Lemma omap_concat_unnest2 d a a1 l :
      omap_concat
        (drec (("PDATA", d) :: ("a1", dcoll a1) :: nil))
        (drec (("PBIND", a) :: nil)
              :: map (fun x : data => drec (("PBIND", x) :: nil)) l)
      =
      Some (drec (("PBIND", a) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil) ::
                 (map (fun x : data => drec (("PBIND", x) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil)) l)).
    Proof.
      unfold omap_concat; simpl.
      rewrite lift_map_map_rec3; simpl; reflexivity.
    Qed.

    Lemma lift_map_remove1 env l l2:
      lift_map
        (fun x : data =>
           match x with
           | drec r => Some (drec (rremove r "a1"))
           | _ => None
           end)
        (map
           (fun x : data =>
              drec
                (("PBIND", env) :: ("PDATA", x) :: ("a1", dcoll l2) :: nil))
           l)
      =
      Some (map (fun x: data => drec (("PBIND", env) :: ("PDATA", x) :: nil)) l).
    Proof.
      induction l; try reflexivity; simpl.
      rewrite IHl; reflexivity.
    Qed.
    
  Lemma lift_map_remove2 d l l2:
    lift_map
      (fun x : data =>
         match x with
           | drec r => Some (drec (rremove r "a1"))
           | _ => None
         end)
      (map
         (fun x : data =>
            drec
              (("PBIND", x) :: ("PDATA", d) :: ("a1", dcoll l2) :: nil))
         l)
    =
    Some (map (fun x: data => drec (("PBIND", x) :: ("PDATA", d) :: nil)) l).
  Proof.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.
  
  Lemma lift_map_one1 env a l:
    lift_map
      (fun x : data =>
         match x with
           | drec r => edot r "PDATA"
           | _ => None
         end) (drec (("PBIND", env) :: ("PDATA", a) :: nil) :: l)
    =
    match
      lift_map
        (fun x : data =>
           match x with
             | drec r => edot r "PDATA"
             | _ => None
           end) l
    with
      | Some a' => Some (a :: a')
      | None => None
    end.
  Proof.
    reflexivity.
  Qed.

  Lemma unfold_env_nra (ae:nraenv_core) (env:data) (x:data) :
    (nraenv_core_eval ae env x) = (h ⊢ (nra_of_nraenv_core ae) @ₐ (nra_context_data env x) ⊣ constant_env).
  Proof.
    revert env x; nraenv_core_cases (induction ae) Case; simpl; intros.
    - Case "cNRAEnvGetConstant"%string.
      reflexivity.
    - Case "cNRAEnvID"%string.
      simpl; reflexivity.
    - Case "cNRAEnvConst"%string.
      reflexivity.
    - Case "cNRAEnvBinop"%string.
      rewrite IHae1; rewrite IHae2; reflexivity.
    - Case "cNRAEnvUnop"%string.
      rewrite IHae; reflexivity.
    - Case "cNRAEnvMap"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_nraenv_core ae2) @ₐ (nra_context_data env x) ⊣ constant_env);
        intros; clear ae2 x.
      unfold olift.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold omap_product, oncoll_map_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite lift_map_map_rec1; simpl; intros.
      rewrite omap_concat_unnest; simpl.
      rewrite omap_concat_map_rec in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite lift_map_remove1 in *; simpl.
      rewrite (IHae1 env a); unfold nra_context_data; simpl.
      generalize (h ⊢ (nra_of_nraenv_core ae1) @ₐ (drec
                   (("PBIND", env)
                    :: ("PDATA", a) :: nil)) ⊣ constant_env); intros.
      destruct o; try reflexivity; simpl.
      unfold lift, lift_oncoll in *.
      revert IHl.
      destruct (lift_map (nra_eval h constant_env (nra_of_nraenv_core ae1))
         (map (fun x : data =>
           drec
             (("PBIND", env)
              :: ("PDATA", x) :: nil)) l)); try reflexivity; try congruence; simpl; destruct (lift_map (nraenv_core_eval ae1 env) l); try reflexivity; try congruence.
    - Case "cNRAEnvMapProduct"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_nraenv_core ae2) @ₐ (nra_context_data env x) ⊣ constant_env); intros; clear ae2 x.
      unfold olift.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold omap_product, oncoll_map_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite lift_map_map_rec1; simpl; intros.
      rewrite omap_concat_unnest; simpl.
      rewrite omap_concat_map_rec in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite lift_map_remove1 in *; simpl.
      rewrite (IHae1 env a); unfold nra_context_data; simpl.
      generalize (h ⊢ (nra_of_nraenv_core ae1) @ₐ(drec
            (("PBIND", env)
             :: ("PDATA", a) :: nil)) ⊣ constant_env); intros.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      rewrite lift_map_map_rec1 in *; simpl in *.
      rewrite omap_concat_map_rec2 in *.
      unfold lift in *; simpl in *.
      revert IHl; generalize (
            lift_flat_map
              (fun a0 : data =>
               match
                 match h ⊢ (nra_of_nraenv_core ae1) @ₐ a0 ⊣ constant_env with
                 | Some x' =>
                     lift_oncoll
                       (fun c1 : list data =>
                        match
                          lift_map
                            (fun x : data =>
                             Some (drec (("PDATA2", x) :: nil))) c1
                        with
                        | Some a' => Some (dcoll a')
                        | None => None
                        end) x'
                 | None => None
                 end
               with
               | Some (dcoll y) => omap_concat a0 y
               | _ => None
               end)
              (map
              (fun x : data =>
               drec
                  (("PBIND", env)
                     :: ("PDATA", x) :: nil)) l)
                    ); intros.
      destruct o; try reflexivity; try congruence; simpl.
      * unfold lift_oncoll in *; simpl in *.
        rewrite lift_map_map_unnest2; simpl in *.
        revert IHl; generalize (
                        (lift_map
          (fun x : data =>
           olift2
             (fun d1 d2 : data =>
              match d1 with
              | drec r1 =>
                  match d2 with
                  | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                  | _ => None
                  end
              | _ => None
              end)
             match x with
             | drec r => edot r "PDATA"
             | _ => None
             end
             match x with
             | drec r => edot r "PDATA2"
             | _ => None
             end) l1)
                      ); generalize (lift_flat_map
            (fun a0 : data =>
             match nraenv_core_eval ae1 env a0 with
             | Some (dcoll y) => omap_concat a0 y
             | _ => None
             end) l) ; intros.
        destruct o; try reflexivity; try congruence; simpl.
        destruct o0; try reflexivity; try congruence; simpl.
        inversion IHl; clear IHl H0.
        unfold olift2, omap_concat; simpl.
        unfold orecconcat; simpl.
        generalize (       lift_map
         (fun x : data =>
          match a with
          | drec r2 =>
              match x with
              | drec r1 => Some (drec (rec_concat_sort r2 r1))
              | _ => None
              end
          | _ => None
          end) l0); simpl; intros.
        destruct o; try reflexivity; simpl.
        destruct o0; try reflexivity; try congruence; simpl.
      * unfold olift2; simpl.
        destruct (omap_concat a l0); simpl; try reflexivity.
        revert IHl; generalize (lift_flat_map
         (fun a0 : data =>
          match nraenv_core_eval ae1 env a0 with
          | Some (dcoll y) => omap_concat a0 y
          | _ => None
          end) l); intros.
        destruct o; try reflexivity; congruence.
    - Case "cNRAEnvProduct"%string.
      rewrite IHae1; rewrite IHae2; reflexivity.
    - Case "cNRAEnvSelect"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_nraenv_core ae2) @ₐ (nra_context_data env x) ⊣ constant_env); intros; clear ae2 x.
      unfold olift.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold omap_product, oncoll_map_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite lift_map_map_rec1; simpl; intros.
      rewrite omap_concat_unnest; simpl.
      rewrite omap_concat_map_rec in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite lift_map_remove1 in *; simpl.
      rewrite (IHae1 env a); unfold nra_context_data; simpl.
      generalize (h ⊢ (nra_of_nraenv_core ae1) @ₐ(drec
            (("PBIND", env)
             :: ("PDATA", a) :: nil)) ⊣ constant_env); intros.
      destruct o; try reflexivity; simpl.
      unfold lift, lift_oncoll in *.
      destruct d; try reflexivity; simpl.
      destruct b; try reflexivity; simpl.
      * revert IHl.
        generalize (lift_filter
                      (fun x' : data =>
                         match nraenv_core_eval ae1 env x' with
                           | Some (dbool b) => Some b
                           | _ => None
                         end) l);
          generalize (lift_filter
                        (fun x' : data =>
                           match h ⊢ (nra_of_nraenv_core ae1) @ₐ x' ⊣ constant_env with
                             | Some (dbool b) => Some b
                             | _ => None
                           end)
                        (map
              (fun x : data =>
               drec
                 (("PBIND", env)
                  :: ("PDATA", x) :: nil)) l));
          intros.
        destruct o; destruct o0; try congruence; try reflexivity;
        rewrite lift_map_one1;
        revert IHl;
        generalize (lift_map
                      (fun x : data =>
                         match x with
                           | drec r => edot r "PDATA"
                                   | _ => None
                         end) l0); intros;
        destruct o; try reflexivity; congruence.
      * revert IHl.
        generalize (lift_filter
                      (fun x' : data =>
                         match nraenv_core_eval ae1 env x' with
                           | Some (dbool b) => Some b
                           | _ => None
                         end) l);
          generalize (lift_filter
                        (fun x' : data =>
                           match h ⊢ (nra_of_nraenv_core ae1) @ₐ x' ⊣ constant_env with
                             | Some (dbool b) => Some b
                             | _ => None
                           end)
                         (map
              (fun x : data =>
               drec
                (("PBIND", env)
                :: ("PDATA", x) :: nil)) l));
          intros.
        destruct o; destruct o0; try congruence; reflexivity.
    - Case "cNRAEnvDefault"%string.
      rewrite IHae1; rewrite IHae2; reflexivity.
    - Case "cNRAEnvEither"%string.
      destruct x; simpl; trivial; [rewrite IHae1|rewrite IHae2]; reflexivity.
    - Case "cNRAEnvEitherConcat"%string.
      rewrite IHae2. generalize ((h ⊢ (nra_of_nraenv_core ae2) @ₐ (nra_context_data env x) ⊣ constant_env)); intros.
      destruct o; try reflexivity; simpl;
      rewrite IHae1; reflexivity.
    - Case "cNRAEnvApp"%string.
      rewrite IHae2. generalize ((h ⊢ (nra_of_nraenv_core ae2) @ₐ (nra_context_data env x) ⊣ constant_env)); intros.
      destruct o; try reflexivity; simpl.
      rewrite IHae1; reflexivity.
    - Case "cNRAEnvEnv"%string.
      reflexivity.
    - Case "cNRAEnvAppEnv"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_nraenv_core ae2) @ₐ (nra_context_data env x) ⊣ constant_env); intros.
      destruct o; try reflexivity; simpl.
      apply IHae1.
    - Case "cNRAEnvMapEnv"%string.
      unfold lift, olift, omap_product, oncoll_map_concat; simpl.
      destruct env; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold omap_product, oncoll_map_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite lift_map_map_rec1; simpl; intros.
      rewrite omap_concat_unnest2; simpl.
      rewrite omap_concat_map_rec3 in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite lift_map_remove2 in *; simpl.
      rewrite (IHae a x); unfold nra_context_data; simpl.
      generalize (h ⊢ (nra_of_nraenv_core ae) @ₐ (drec (("PBIND", a) :: ("PDATA", x) :: nil)) ⊣ constant_env); intros.
      destruct o; try reflexivity; simpl.
      unfold lift, lift_oncoll in *.
      revert IHl.
      destruct (lift_map (nra_eval h constant_env (nra_of_nraenv_core ae))
         (map (fun x0 : data => drec (("PBIND", x0) :: ("PDATA", x) :: nil))
              l)); try reflexivity; try congruence; simpl; destruct (lift_map (fun env' => (nraenv_core_eval ae env' x)) l); try reflexivity; try congruence.
  Qed.
  End Semantics.
  
End cNRAEnv.

(* Delimit Scope nraenv_core_scope with nraenv_core. *)
Delimit Scope nraenv_core_scope with nraenv_core.

Notation "h ⊢ₑ op @ₑ x ⊣ c ; env " := (nraenv_core_eval h c op env x) (at level 10) : nraenv_core_scope.

Section RcNRAEnv2.
  Local Open Scope nraenv_core.

  Context {fruntime:foreign_runtime}.

  Lemma nraenv_core_eval_const_sort h p x c env :
    h ⊢ₑ p @ₑ x ⊣ (rec_sort c); env = h ⊢ₑ p @ₑ x ⊣ c; env.
  Proof.
    revert x c env.
    induction p; simpl; unfold olift, olift2; intros; trivial;
    try rewrite IHp; try rewrite IHp1; try rewrite IHp2; trivial.
    - unfold edot. 
      rewrite (assoc_lookupr_drec_sort (odt:=ODT_string)).
      trivial.
    - match_destr.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply lift_map_ext; intros.
      congruence.
    - match_destr.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply omap_product_ext; intros.
      congruence.
    - match_destr.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply lift_filter_ext; intros.
      rewrite IHp1; match_destr.
    - match_destr.
    - match_destr.
    - match_destr.
    - apply lift_oncoll_ext; intros.
      f_equal.
      apply lift_map_ext; intros.
      congruence.
  Qed.

  Lemma unfold_env_nra_sort h c (ae:nraenv_core) (env:data) (x:data) :
    (nraenv_core_eval h c ae env x) = (h ⊢ (nra_of_nraenv_core ae) @ₐ (nra_context_data env x) ⊣ (rec_sort c)).
  Proof.
    rewrite <- (nraenv_core_eval_const_sort h _ x c env).
    rewrite unfold_env_nra by trivial.
    trivial.
  Qed.

  (* evaluation preserves normalization *)
  Lemma nraenv_core_eval_normalized h constant_env {op:nraenv_core} {env d:data} {o} :
    nraenv_core_eval h constant_env op env d = Some o ->
    Forall (fun x => data_normalized h (snd x)) constant_env ->
    data_normalized h env ->
    data_normalized h d ->
    data_normalized h o.
  Proof.
    Hint Resolve dnrec_sort_content.
    rewrite unfold_env_nra_sort; intros.
    eauto.
  Qed.

  Section Top.
    Context (h:list(string*string)).

    Definition nraenv_core_eval_top (q:nraenv_core) (env:bindings) :=
      nraenv_core_eval h (rec_sort env) q (drec nil) dunit.
  End Top.

  Section FreeVars.
    Fixpoint nraenv_core_free_vars (q:nraenv_core) : list string :=
      match q with
      | cNRAEnvGetConstant s => s :: nil
      | cNRAEnvID => nil
      | cNRAEnvConst rd => nil
      | cNRAEnvBinop _ q1 q2 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvUnop _ q1 =>
        nraenv_core_free_vars q1
      | cNRAEnvMap q2 q1 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvMapProduct q2 q1 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvProduct q1 q2 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvSelect q2 q1 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvEither ql qr =>
        nraenv_core_free_vars ql ++ nraenv_core_free_vars qr
      | cNRAEnvEitherConcat q1 q2 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvDefault q1 q2 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvApp q2 q1 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvEnv => nil
      | cNRAEnvAppEnv q2 q1 =>
        nraenv_core_free_vars q1 ++ nraenv_core_free_vars q2
      | cNRAEnvMapEnv q1 =>
        nraenv_core_free_vars q1
      end.
  End FreeVars.

End RcNRAEnv2.

  
Notation "'ID'" := (cNRAEnvID)  (at level 50) : nraenv_core_scope.
Notation "'ENV'" := (cNRAEnvEnv)  (at level 50) : nraenv_core_scope.
Notation "CGET⟨ s ⟩" := (cNRAEnvGetConstant s) (at level 50) : nraenv_core_scope.
  
Notation "‵‵ c" := (cNRAEnvConst (dconst c))  (at level 0) : nraenv_core_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (cNRAEnvConst c)  (at level 0) : nraenv_core_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (cNRAEnvConst (dcoll nil))  (at level 0) : nraenv_core_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (cNRAEnvConst (drec nil)) (at level 50) : nraenv_core_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (cNRAEnvBinop OpAnd r1 r2) (right associativity, at level 65): nraenv_core_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (cNRAEnvBinop OpOr r1 r2) (right associativity, at level 70): nraenv_core_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (cNRAEnvBinop OpEqual r1 r2) (right associativity, at level 70): nraenv_core_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (cNRAEnvBinop OpLe r1 r2) (no associativity, at level 70): nraenv_core_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (cNRAEnvBinop OpBagUnion r1 r2) (right associativity, at level 70): nraenv_core_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (cNRAEnvBinop OpBagDiff r1 r2) (right associativity, at level 70): nraenv_core_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (cNRAEnvBinop OpBagMin r1 r2) (right associativity, at level 70): nraenv_core_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (cNRAEnvBinop OpBagMax r1 r2) (right associativity, at level 70): nraenv_core_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((cNRAEnvBinop OpRecConcat) p r) (at level 70) : nraenv_core_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((cNRAEnvBinop OpRecMerge) p r) (at level 70) : nraenv_core_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (cNRAEnvUnop OpNeg r1) (right associativity, at level 70): nraenv_core_scope.        (* ¬ = \neg *)
Notation "♯distinct( r1 )" := (cNRAEnvUnop OpDistinct r1) (right associativity, at level 70): nraenv_core_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (cNRAEnvUnop OpCount r1) (right associativity, at level 70): nraenv_core_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (cNRAEnvUnop OpFlatten d) (at level 50) : nraenv_core_scope.                   (* ♯ = \sharp *)

Notation "a1 ♯+ a2" := (cNRAEnvBinop (OpNatBinary NatPlus) a1 a2) (right associativity, at level 70): nraenv_core_scope.
   (* ♯ = \sharp *)

Notation "a1 ♯- a2" := (cNRAEnvBinop (OpNatBinary NatMinus) a1 a2) (right associativity, at level 70): nraenv_core_scope.
   (* ♯ = \sharp *)

Notation "‵{| d |}" := ((cNRAEnvUnop OpBag) d)  (at level 50) : nraenv_core_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((cNRAEnvUnop (OpRec s)) r) (at level 50) : nraenv_core_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((cNRAEnvUnop (OpRecRemove s1)) r) (at level 50) : nraenv_core_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((cNRAEnvUnop (OpRecProject s1)) r) (at level 50) : nraenv_core_scope.          (* π = \pi *)
Notation "p · r" := ((cNRAEnvUnop (OpDot r)) p) (left associativity, at level 40): nraenv_core_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (cNRAEnvMap p r) (at level 70) : nraenv_core_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (cNRAEnvMapProduct e2 e1) (at level 70) : nraenv_core_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (cNRAEnvProduct r1 r2) (right associativity, at level 70): nraenv_core_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (cNRAEnvSelect p r) (at level 70) : nraenv_core_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (cNRAEnvDefault r1 r2) (right associativity, at level 70): nraenv_core_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (cNRAEnvApp r1 r2) (right associativity, at level 60): nraenv_core_scope.           (* ◯ = \bigcirc *)

Notation "r1 ◯ₑ r2" := (cNRAEnvAppEnv r1 r2) (right associativity, at level 60): nraenv_core_scope.           (* ◯ = \bigcirc *)
Notation "χᵉ⟨ p ⟩" := (cNRAEnvMapEnv p) (at level 70) : nraenv_core_scope.                              (* χ = \chi *)

Hint Resolve nraenv_core_eval_normalized.

Tactic Notation "nraenv_core_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "cNRAEnvGetConstant"%string
  | Case_aux c "cNRAEnvID"%string
  | Case_aux c "cNRAEnvConst"%string
  | Case_aux c "cNRAEnvBinop"%string
  | Case_aux c "cNRAEnvUnop"%string
  | Case_aux c "cNRAEnvMap"%string
  | Case_aux c "cNRAEnvMapProduct"%string
  | Case_aux c "cNRAEnvProduct"%string
  | Case_aux c "cNRAEnvSelect"%string
  | Case_aux c "cNRAEnvDefault"%string
  | Case_aux c "cNRAEnvEither"%string
  | Case_aux c "cNRAEnvEitherConcat"%string
  | Case_aux c "cNRAEnvApp"%string
  | Case_aux c "cNRAEnvEnv"%string
  | Case_aux c "cNRAEnvAppEnv"%string
  | Case_aux c "cNRAEnvMapEnv"%string].

