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

(** NRAEnv is nested relational algebra, extended with operations to
  facilitate encoding of environment manipulation. It serves as the
  main intermediate language for optimization. *)

(** NRAEnv is a thin layer over the core language cNRAEnv. As cNRAEnv,
  NRAEnv is combinators-based, i.e., it is evaluated with only a
  static global environment, but no notion of local variables. *)

(** Additional operators in NRAEnv can be easily expressed in terms of
  the core cNRAEnv, but are useful for optimization purposes. Those
  operators notably include joins and group-by. *)

(** NRAEnv builds on a large body of work from the database
community. For a complete treatment on nested relational algebras, we
refer to Guido Moerkotte's "Building Query Compilers", Chapter 7.

   http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf *)

(** Summary:

- Language: NRAEnv (Nested Relational Algebra with Environments)
- Based on: "Handling Environments in a Nested Relational Algebra with
  Combinators and an Implementation in a Verified Query Compiler"
  Joshua Auerbach, Martin Hirzel, Louis Mandel, Avraham Shinnar, and
  Jérôme Siméon. SIGMOD'2017.
- translating to NRAEnv: LambdaNRA, SQL, OQL, CAMP, cNRAEnv
- translating from NRAEnv: NNRC, cNRAEnv *)

Require Import String.
Require Import List.
Require Import Compare_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNRAEnv.
Require Import cNRAEnvEq.

Section NRAEnv.
  Context {fruntime:foreign_runtime}.
  
  (** * Abstract Syntax *)

  Section Syntax.
  
    (** As much as possible, notations are aligned with those of
      S. Cluet and G. Moerkotte. Nested queries in object bases. In
      Proc. Int.  Workshop on Database Programming Languages , pages
      226-242, 1993. *)

    Inductive nraenv : Set :=
    | NRAEnvGetConstant : string -> nraenv                      (**r global variable lookup ([$$v]) *)
    | NRAEnvID : nraenv                                         (**r current input ([ID]) *)
    | NRAEnvConst : data -> nraenv                              (**r constant data ([d]) *)
    | NRAEnvBinop : binary_op -> nraenv -> nraenv -> nraenv     (**r binary operator ([e₁ ⊠ e₂]) *)
    | NRAEnvUnop : unary_op -> nraenv -> nraenv                 (**r unary operator ([⊞ e]) *)
    | NRAEnvMap : nraenv -> nraenv -> nraenv                    (**r Map [χ] *)
    | NRAEnvMapProduct : nraenv -> nraenv -> nraenv             (**r dependent Cartesian product [⋈ᵈ] *)
    | NRAEnvProduct : nraenv -> nraenv -> nraenv                (**r Cartesian product [×] *)
    | NRAEnvSelect : nraenv -> nraenv -> nraenv                 (**r Relational selection [σ] *) 
    | NRAEnvDefault : nraenv -> nraenv -> nraenv                (**r Default for empty collection [∥] *)
    | NRAEnvEither : nraenv -> nraenv -> nraenv                 (**r case expression *)
    | NRAEnvEitherConcat : nraenv -> nraenv -> nraenv           (**r case expression with concatenation *)
    | NRAEnvApp : nraenv -> nraenv -> nraenv                    (**r composition over the current value [∘] *)
    | NRAEnvEnv : nraenv                                        (**r current reified environment *)
    | NRAEnvAppEnv : nraenv -> nraenv -> nraenv                 (**r composition over the reified environment [∘ᵉ] *)
    | NRAEnvMapEnv : nraenv -> nraenv                           (**r map over the reified environment [χᵉ] *)
    | NRAEnvFlatMap : nraenv -> nraenv -> nraenv                (**r flat map [Χ] *)
    | NRAEnvJoin : nraenv -> nraenv -> nraenv -> nraenv         (**r predicate join [e₂ ⋈⟨e₁⟩ e₃] *)
    | NRAEnvNaturalJoin : nraenv -> nraenv -> nraenv            (**r natural join [e₁ ⋈ e₂] *)
    | NRAEnvProject : list string -> nraenv -> nraenv           (**r relational projection [Π] *)
    | NRAEnvGroupBy : string -> list string -> nraenv -> nraenv (**r group-by [Γ] *)
    | NRAEnvUnnest : string -> string -> nraenv -> nraenv       (**r unnest [μ] *)
    .

    (** Equality between two NRAEnv expressions is decidable. *)
  
    Global Instance nraenv_eqdec : EqDec nraenv eq.
    Proof.
      change (forall x y : nraenv,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec | apply data_eqdec | apply string_eqdec | apply list_eqdec; apply string_eqdec].
    Defined.

  End Syntax.

  Tactic Notation "nraenv_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "NRAEnvGetConstant"%string
    | Case_aux c "NRAEnvID"%string
    | Case_aux c "NRAEnvConst"%string
    | Case_aux c "NRAEnvBinop"%string
    | Case_aux c "NRAEnvUnop"%string
    | Case_aux c "NRAEnvMap"%string
    | Case_aux c "NRAEnvMapProduct"%string
    | Case_aux c "NRAEnvProduct"%string
    | Case_aux c "NRAEnvSelect"%string
    | Case_aux c "NRAEnvDefault"%string
    | Case_aux c "NRAEnvEither"%string
    | Case_aux c "NRAEnvEitherConcat"%string
    | Case_aux c "NRAEnvApp"%string
    | Case_aux c "NRAEnvEnv"%string
    | Case_aux c "NRAEnvAppEnv"%string
    | Case_aux c "NRAEnvMapEnv"%string
    | Case_aux c "NRAEnvFlatMap"%string
    | Case_aux c "NRAEnvJoin"%string
    | Case_aux c "NRAEnvNaturalJoin"%string
    | Case_aux c "NRAEnvProject"%string
    | Case_aux c "NRAEnvGroupBy"%string
    | Case_aux c "NRAEnvUnnest"%string].
  
  (** * Macros *)

  Section Macros.
    (** All the additional operators in NRAEnv are defined in terms of
    the cNRAEnv. *)
  
    (** ** Joins *)

    (** Predicate join [e₂ ⋈⟨e₁) e₃ = σ⟨e₁⟩(e₂ × e₃)] *)
  
    Definition macro_cNRAEnvJoin (e1 e2 e3 : nraenv_core) : nraenv_core :=
      (cNRAEnvSelect e1 (cNRAEnvProduct e2 e3)).

    (** Semi join [e₂ ⋉⟨e₁) e₁ = σ⟨σ⟨e₁⟩({ID} × e₃) ≠ {}⟩(e₂)] *)
    
    Definition macro_cNRAEnvSemiJoin (e1 e2 e3 : nraenv_core) : nraenv_core :=
      cNRAEnvSelect
        (cNRAEnvUnop OpNeg
                     (cNRAEnvBinop OpEqual
                                   (cNRAEnvSelect e1
                                                  (cNRAEnvProduct
                                                     ((cNRAEnvUnop OpBag) cNRAEnvID) e3))
                                   (cNRAEnvConst (dcoll nil)))) e2.

    Definition macro_cNRAEnvAntiJoin (e1 e2 e3 : nraenv_core) : nraenv_core :=
      cNRAEnvSelect
        (cNRAEnvBinop OpEqual
                      (cNRAEnvSelect e1
                                     (cNRAEnvProduct
                                        ((cNRAEnvUnop OpBag) cNRAEnvID) e3))
                      (cNRAEnvConst (dcoll nil))) e2.

    (** Natural join [e₁ ⋈ e₂] *)

    Definition macro_cNRAEnvNaturalJoin (e1 e2 : nraenv_core) : nraenv_core :=
      cNRAEnvUnop
        OpFlatten
        (cNRAEnvMap
           (cNRAEnvBinop OpRecMerge
                         (cNRAEnvUnop (OpDot "t1") cNRAEnvID)
                         (cNRAEnvUnop (OpDot "t2") cNRAEnvID))
           (cNRAEnvProduct
              (cNRAEnvMap (cNRAEnvUnop (OpRec "t1") cNRAEnvID) e1)
              (cNRAEnvMap (cNRAEnvUnop (OpRec "t2") cNRAEnvID) e2))).

    (** ** Map operations *)

    Definition map_add_rec (s:string) (e1 e2 : nraenv_core) : nraenv_core :=
      cNRAEnvMap ((cNRAEnvBinop OpRecConcat) cNRAEnvID ((cNRAEnvUnop (OpRec s)) e1)) e2.
    Definition map_to_rec (s:string) (e : nraenv_core) : nraenv_core :=
      cNRAEnvMap (cNRAEnvUnop (OpRec s) cNRAEnvID) e.

    Definition macro_cNRAEnvFlatMap (e1 e2 : nraenv_core) : nraenv_core :=
      cNRAEnvUnop OpFlatten (cNRAEnvMap e1 e2).
  
    (** ** Projection *)
    Definition macro_cNRAEnvProject (fields:list string) (e:nraenv_core) : nraenv_core
      := cNRAEnvMap (cNRAEnvUnop (OpRecProject fields) cNRAEnvID) e.

    Definition project_remove (s:string) (e:nraenv_core) : nraenv_core :=
      cNRAEnvMap ((cNRAEnvUnop (OpRecRemove s)) cNRAEnvID) e.

    (** ** Renaming *)
    (* renames field s1 to s2 *)
    Definition map_rename_rec (s1 s2:string) (e:nraenv_core) : nraenv_core :=
      cNRAEnvMap ((cNRAEnvBinop OpRecConcat)
                    ((cNRAEnvUnop (OpRec s2)) ((cNRAEnvUnop (OpDot s1)) cNRAEnvID))
                    ((cNRAEnvUnop (OpRecRemove s1)) cNRAEnvID)) e.

    (** ** Grouping *)

    (** Defining group-by in terms of the core is more tricky, but is
      possible. You need to do two passes, and compare elements with
      the same set of attribute names which means you need to
      encapsulate each branch with distinct record names. *)

    Import ListNotations.
    (* g: partition name ; sl: list of grouping attributes *)
    (* [Γ[g][sl](op) ==
       χ⟨
       ID.t1.t2
       ⊗
       [ g : χ⟨ ID.t3 ⟩
       (σ⟨ π[sl](ID.t1) = π[sl](ID.t3) ⟩
       ({ ID.t2 } × ID.t4)) ]
       ⟩
      ( { [ t4 : χ⟨[t3]⟩(op) ] } × (χ⟨[t2:ID]⟩(χ⟨[t1:ID]⟩(♯distinct(Π[sl](op))))))] *)
  
    Definition group_by_no_env (g:string) (sl:list string) (e:nraenv_core) : nraenv_core :=
      cNRAEnvMap
        (cNRAEnvBinop OpRecConcat
                      (cNRAEnvUnop (OpDot "1") (cNRAEnvUnop (OpDot "2") cNRAEnvID))
                      (cNRAEnvUnop (OpRec g)
                                   (cNRAEnvMap (cNRAEnvUnop (OpDot "3") cNRAEnvID)
                                               (cNRAEnvSelect
                                                  (cNRAEnvBinop OpEqual
                                                                (cNRAEnvUnop (OpRecProject sl) (cNRAEnvUnop (OpDot "1") cNRAEnvID))
                                                                (cNRAEnvUnop (OpRecProject sl) (cNRAEnvUnop (OpDot "3") cNRAEnvID)))
                                                  (cNRAEnvProduct (cNRAEnvUnop OpBag (cNRAEnvUnop (OpDot "2") cNRAEnvID))
                                                                  (cNRAEnvUnop (OpDot "4") cNRAEnvID))))))
        (cNRAEnvProduct
           (cNRAEnvUnop OpBag (cNRAEnvUnop (OpRec "4") (map_to_rec "3" e)))
           (map_to_rec "2" (map_to_rec "1" (cNRAEnvUnop OpDistinct
                                                        (macro_cNRAEnvProject sl e))))).

    (** This is an alternative definition that isn't quite as
        inefficient. It stores the result of the input operator in the
        environment so it isn't computed twice. This is still
        quadratic. *)
  
    (* g: partition name ; sl: list of grouping attributes *)
    (* [Γ[g][sl](op) ==
       (χ⟨ ID ⊕ [ g : σ⟨ ENV.$key = π[sl](ID) ⟩(ENV.$pregroup) ◯ᵉ ([$key:ID] ⊕ ENV) ] ⟩
       (♯distinct(Π[sl](ENV.$pregroup)))) ◯ᵉ [ $pregroup : op ]]
     *)

    Definition macro_cNRAEnvGroupBy (g:string) (sl:list string) (e:nraenv_core) : nraenv_core :=
      let op_pregroup := cNRAEnvUnop (OpDot "$pregroup") cNRAEnvEnv in
      cNRAEnvAppEnv
        (cNRAEnvMap
           (cNRAEnvBinop
              OpRecConcat
              cNRAEnvID
              (cNRAEnvUnop
                 (OpRec g)
                 (cNRAEnvAppEnv
                    (cNRAEnvSelect
                       (cNRAEnvBinop OpEqual
                                     (cNRAEnvUnop (OpRecProject sl) cNRAEnvID)
                                     (cNRAEnvUnop (OpDot "$key") cNRAEnvEnv))
                       op_pregroup)
                    (cNRAEnvBinop OpRecConcat
                                  (cNRAEnvUnop (OpRec "$key")
                                               cNRAEnvID)
                                  cNRAEnvEnv))))
           (cNRAEnvUnop OpDistinct (macro_cNRAEnvProject sl op_pregroup)))
        (cNRAEnvUnop (OpRec "$pregroup") e).

    (** ** Unnesting *)

    Definition unnest_one (s:string) (e:nraenv_core) : nraenv_core :=
      cNRAEnvMap ((cNRAEnvUnop (OpRecRemove s)) cNRAEnvID)
                 (cNRAEnvMapProduct ((cNRAEnvUnop (OpDot s)) cNRAEnvID) e).

    Definition macro_cNRAEnvUnnest (a b:string) (e:nraenv_core) : nraenv_core :=
      cNRAEnvMap ((cNRAEnvUnop (OpRecRemove a)) cNRAEnvID)
                 (cNRAEnvMapProduct
                    (cNRAEnvMap ((cNRAEnvUnop (OpRec b)) cNRAEnvID)
                                ((cNRAEnvUnop (OpDot a)) cNRAEnvID)) e).

    (** ** Macro expansion *)

    Fixpoint nraenv_to_nraenv_core (e:nraenv) : nraenv_core :=
      match e with
      | NRAEnvGetConstant s => cNRAEnvGetConstant s
      | NRAEnvID => cNRAEnvID
      | NRAEnvConst d => cNRAEnvConst d
      | NRAEnvBinop b e1 e2 =>
        cNRAEnvBinop b
                     (nraenv_to_nraenv_core e1)
                     (nraenv_to_nraenv_core e2)
      | NRAEnvUnop u e1 => cNRAEnvUnop u (nraenv_to_nraenv_core e1)
      | NRAEnvMap e1 e2 =>
        cNRAEnvMap (nraenv_to_nraenv_core e1)
                   (nraenv_to_nraenv_core e2)
      | NRAEnvMapProduct e1 e2 =>
        cNRAEnvMapProduct (nraenv_to_nraenv_core e1)
                          (nraenv_to_nraenv_core e2)
      | NRAEnvProduct e1 e2 =>
        cNRAEnvProduct (nraenv_to_nraenv_core e1)
                       (nraenv_to_nraenv_core e2)
      | NRAEnvSelect e1 e2 =>
        cNRAEnvSelect (nraenv_to_nraenv_core e1)
                      (nraenv_to_nraenv_core e2)
      | NRAEnvDefault e1 e2 =>
        cNRAEnvDefault
          (nraenv_to_nraenv_core e1)
          (nraenv_to_nraenv_core e2)
      | NRAEnvEither opl opr =>
        cNRAEnvEither
          (nraenv_to_nraenv_core opl)
          (nraenv_to_nraenv_core opr)
      | NRAEnvEitherConcat e1 e2 =>
        cNRAEnvEitherConcat
          (nraenv_to_nraenv_core e1)
          (nraenv_to_nraenv_core e2)
      | NRAEnvApp e1 e2 =>
        cNRAEnvApp
          (nraenv_to_nraenv_core e1)
          (nraenv_to_nraenv_core e2)
      | NRAEnvEnv =>
        cNRAEnvEnv
      | NRAEnvAppEnv e1 e2 =>
        cNRAEnvAppEnv
          (nraenv_to_nraenv_core e1)
          (nraenv_to_nraenv_core e2)
      | NRAEnvMapEnv e1 =>
        cNRAEnvMapEnv
          (nraenv_to_nraenv_core e1)
      | NRAEnvFlatMap e1 e2 =>
        macro_cNRAEnvFlatMap
          (nraenv_to_nraenv_core e1)
          (nraenv_to_nraenv_core e2)
      | NRAEnvJoin e1 e2 e3 =>
        macro_cNRAEnvJoin
          (nraenv_to_nraenv_core e1)
          (nraenv_to_nraenv_core e2)
          (nraenv_to_nraenv_core e3)
      | NRAEnvNaturalJoin e1 e2 =>
        macro_cNRAEnvNaturalJoin
          (nraenv_to_nraenv_core e1)
          (nraenv_to_nraenv_core e2)
      | NRAEnvProject ls e1 =>
        macro_cNRAEnvProject ls (nraenv_to_nraenv_core e1)
      | NRAEnvGroupBy s ls e1 =>
        macro_cNRAEnvGroupBy s ls (nraenv_to_nraenv_core e1)
      | NRAEnvUnnest a b e1 =>
        macro_cNRAEnvUnnest a b (nraenv_to_nraenv_core e1)
      end.

    (** * Round-tripping *)

    (** Just checking that cNRAEnv can be lifted back to NRAEnv, and
        showing that we can round-trip. *)

    Fixpoint nraenv_core_to_nraenv (a:nraenv_core) : nraenv :=
      match a with
      | cNRAEnvGetConstant s => NRAEnvGetConstant s
      | cNRAEnvID => NRAEnvID
      | cNRAEnvConst d => NRAEnvConst d
      | cNRAEnvBinop b e1 e2 =>
        NRAEnvBinop b (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvUnop u e1 =>
        NRAEnvUnop u (nraenv_core_to_nraenv e1)
      | cNRAEnvMap e1 e2 =>
        NRAEnvMap (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvMapProduct e1 e2 =>
        NRAEnvMapProduct (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvProduct e1 e2 =>
        NRAEnvProduct (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvSelect e1 e2 =>
        NRAEnvSelect (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvDefault e1 e2 =>
        NRAEnvDefault (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvEither opl opr =>
        NRAEnvEither (nraenv_core_to_nraenv opl) (nraenv_core_to_nraenv opr)
      | cNRAEnvEitherConcat e1 e2 =>
        NRAEnvEitherConcat (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvApp e1 e2 =>
        NRAEnvApp (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvEnv => NRAEnvEnv
      | cNRAEnvAppEnv e1 e2 =>
        NRAEnvAppEnv (nraenv_core_to_nraenv e1) (nraenv_core_to_nraenv e2)
      | cNRAEnvMapEnv e1 =>
        NRAEnvMapEnv (nraenv_core_to_nraenv e1)
      end.

    (** Round tripping between NRAEnv and cNRAEnv is a purely
    syntactic remark. I.e., you obtain the exact same AST. *)
    
    Lemma nraenv_roundtrip (a:nraenv_core) :
      (nraenv_to_nraenv_core (nraenv_core_to_nraenv a)) = a.
    Proof.
      induction a;
        simpl;
        try reflexivity;
        try (rewrite IHa1; rewrite IHa2; try rewrite IHa3; reflexivity);
        rewrite IHa; reflexivity.
    Qed.

  End Macros.

  Section Semantics.
    (** Part of the context is fixed for the rest of the development:
- [h] is the brand relation
- [constant_env] is the global environment *)

    Context (h:list(string*string)).
    Context (constant_env:list (string*data)).

    (** ** Denotational Semantics *)

    (** The semantics is defined using the main judgment [Γc ; γ ; d ⊢
    〚e〛⇓ d'] ([nraenv_sem]) where [Γc] is the global
    environment, [γ] is the reified input environment, [d] is the
    input value, [e] the cNRAEnv expression and [d'] the resulting
    value. *)
    
    (** The auxiliary judgment [Γc ; γ ; {c₁} ⊢〚e〛χ ⇓ {c₂}]
    ([nraenv_sem_map]) is used in the definition of the map [χ]
    operator. *)
    
    (** The auxiliary judgment [Γc ; γ ; {c₁} ⊢〚e〛⋈ᵈ ⇓ {c₂}]
    ([nra_map_product_select]) is used in the definition of the
    dependant product [⋈ᵈ] operator. *)
    
    (** The auxiliary judgment [Γc ; γ ; {c₁} ⊢〚e〛σ ⇓ {c₂}]
    ([nraenv_sem_select]) is used in the definition of the
    selection [σ] operator. *)
    
    (** The auxiliary judgment [Γc ; {c₁} ; d ⊢〚e〛χᵉ ⇓ {c₂}]
    ([nraenv_sem_map_env]) is used in the definition of the map
    over environment [χᵉ] operator. *)
    
    Section Denotation.
      Inductive nraenv_sem: nraenv -> data -> data -> data -> Prop :=
      | sem_NRAEnvGetConstant : forall v env d d1,
          edot constant_env v = Some d1 ->                   (**r   [Γc(v) = d₁] *)
          nraenv_sem (NRAEnvGetConstant v) env d d1          (**r ⇒ [Γc ; γ ; d ⊢〚$$v〛⇓ d₁] *)
      | sem_NRAEnvID : forall env d,
          nraenv_sem NRAEnvID env d d                        (**r   [Γc ; γ ; d ⊢ ID ⇓ d] *)
      | sem_NRAEnvConst : forall env d d1 d2,
          normalize_data h d1 = d2 ->                        (**r   [norm(d₁) = d₂] *)
          nraenv_sem (NRAEnvConst d1) env d d2               (**r ⇒ [Γc ; γ ; d ⊢〚d₁〛⇓ d₂] *)
      | sem_NRAEnvBinop : forall bop e1 e2 env d d1 d2 d3,
          nraenv_sem e1 env d d1 ->                          (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          nraenv_sem e2 env d d2 ->                          (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ d₂] *)
          binary_op_eval h bop d1 d2 = Some d3 ->            (**r ∧ [d₁ ⊠ d₂ = d₃] *)
          nraenv_sem (NRAEnvBinop bop e1 e2) env d d3        (**r ⇒ [Γc ; γ ; d ⊢〚e₁ ⊠ e₂〛⇓ d₃] *)
      | sem_NRAEnvUnop : forall uop e env d d1 d2,
          nraenv_sem e env d d1 ->                           (**r   [Γc ; γ ; d ⊢〚e〛⇓ d₁] *)
          unary_op_eval h uop d1 = Some d2 ->                (**r ∧ [⊞ d₁ = d₂] *)
          nraenv_sem (NRAEnvUnop uop e) env d d2             (**r ⇒ [Γc ; γ ; d ⊢〚⊞ e〛⇓ d₂] *)
      | sem_NRAEnvMap : forall e1 e2 env d c1 c2,
          nraenv_sem e1 env d (dcoll c1) ->                  (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          nraenv_sem_map e2 env c1 c2 ->                     (**r ∧ [Γc ; γ ; {c₁} ⊢〚e₂〛χ ⇓ {c₂}] *)
          nraenv_sem (NRAEnvMap e2 e1) env d (dcoll c2)      (**r ⇒ [Γc ; γ ; d ⊢〚χ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
      | sem_NRAEnvMapProduct : forall e1 e2 env d c1 c2,
          nraenv_sem e1 env d (dcoll c1) ->                  (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          nraenv_sem_map_product e2 env c1 c2 ->             (**r ∧ [Γc ; γ ; {c₁} ⊢〚e₂〛⋈ᵈ ⇓ {c₂}] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; d ⊢〚⋈ᵈ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
            (NRAEnvMapProduct e2 e1) env d (dcoll c2)
      | sem_NRAEnvProduct_empty : forall e1 e2 env d,        (**r Does not evaluate [e₂] if [e₁] is empty. This facilitates translation to cNNRC *)
          nraenv_sem e1 env d (dcoll nil) ->                 (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {}] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; d ⊢〚e₁ × e₂〛⇓ {}] *)
            (NRAEnvProduct e1 e2) env d (dcoll nil)
      | sem_NRAEnvProduct_nonEmpty : forall e1 e2 env d c1 c2 c3,
          nraenv_sem e1 env d (dcoll c1) ->                  (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          c1 <> nil ->                                       (**r ∧ [{c₁} ≠ {}] *)
          nraenv_sem e2 env d (dcoll c2) ->                  (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ {c₂}] *)
          product_sem c1 c2 c3 ->                            (**r ∧ [{c₁} × {c₂} ⇓ {c₃}] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; d ⊢〚e₁ × e₂〛⇓ {c₃}] *)
            (NRAEnvProduct e1 e2) env d (dcoll c3)
      | sem_NRAEnvSelect : forall e1 e2 env d c1 c2,
          nraenv_sem e1 env d (dcoll c1) ->                  (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          nraenv_sem_select e2 env c1 c2 ->                  (**r ∧ [Γc ; γ ; {c₁} ⊢〚e₂〛σ ⇓ {c₂}] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; d ⊢〚σ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
            (NRAEnvSelect e2 e1) env d (dcoll c2)
      | sem_NRAEnvDefault_empty : forall e1 e2 env d d2,
          nraenv_sem e1 env d  (dcoll nil) ->                (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {}] *)
          nraenv_sem e2 env d d2 ->                          (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ d₂] *)
          nraenv_sem (NRAEnvDefault e1 e2) env d d2          (**r ⇒ [Γc ; γ ; d ⊢〚e₁ ∥ e₂〛⇓ d₂] *)
      | sem_NRAEnvDefault_not_empty : forall e1 e2 env d d1,
          nraenv_sem e1 env d d1 ->                          (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          d1 <> dcoll nil ->                                 (**r ∧ [d₁ ≠ {}] *)
          nraenv_sem (NRAEnvDefault e1 e2) env d d1          (**r ⇒ [Γc ; γ ; d ⊢〚e₁ ∥ e₂〛⇓ d₁] *)
      | sem_NRAEnvEither_left : forall e1 e2 env d d1,
          nraenv_sem e1 env d d1 ->                          (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; (dleft d) ⊢〚either e₁ e₂〛⇓ d₁] *)
            (NRAEnvEither e1 e2) env (dleft d) d1
      | sem_NRAEnvEither_right : forall e1 e2 env d d2,
          nraenv_sem e2 env d d2 ->                          (**r   [Γc ; γ ; d ⊢〚e₂〛⇓ d₂] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; (dright d) ⊢〚either e₁ e₂〛⇓ d₂] *)
            (NRAEnvEither e1 e2) env (dright d) d2
      | sem_NRAEnvEitherConcat_left : forall e1 e2 env d r1 r2,
          nraenv_sem e1 env d (dleft (drec r1)) ->           (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ (dleft [r₁])] *)
          nraenv_sem e2 env d (drec r2) ->                   (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ [r₂]] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; d ⊢〚either⊕ e₁ e₂〛⇓ (dleft [r₁]⊕[r₂]]) *)
            (NRAEnvEitherConcat e1 e2) env d
            (dleft (drec (rec_concat_sort r1 r2)))
      | sem_NRAEnvEitherConcat_right : forall e1 e2 env d r1 r2,
          nraenv_sem e1 env d (dright (drec r1)) ->          (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ (dright [r₁])] *)
          nraenv_sem e2 env d (drec r2) ->                   (**r ∧ [Γc ; γ ; d ⊢〚e₂〛⇓ [r₂]] *)
          nraenv_sem                                         (**r ⇒ [Γc ; γ ; d ⊢〚either⊕ e₁ e₂〛⇓ (dright [r₁]⊕[r₂]]) *)
            (NRAEnvEitherConcat e1 e2) env d
            (dright (drec (rec_concat_sort r1 r2)))
      | sem_NRAEnvApp : forall e1 e2 env d d1 d2,
          nraenv_sem e1 env d d1 ->                          (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ d₁] *)
          nraenv_sem e2 env d1 d2 ->                         (**r   [Γc ; γ ; d₁ ⊢〚e₂〛⇓ d₂] *)
          nraenv_sem (NRAEnvApp e2 e1) env d d2              (**r ⇒ [Γc ; γ ; d ⊢〚e₂ ∘ e₁〛⇓ d₂] *)
      | sem_NRAEnvEnv : forall env d,
          nraenv_sem NRAEnvEnv env d env                     (**r   [Γc ; γ ; d ⊢ ENV ⇓ γ] *)
      | sem_NRAEnvAppEnv : forall e1 e2 env d env1 d2,
          nraenv_sem e1 env d env1 ->                        (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ γ₁] *)
          nraenv_sem e2 env1 d d2 ->                         (**r   [Γc ; γ₁ ; d ⊢〚e₂〛⇓ d₂] *)
          nraenv_sem (NRAEnvAppEnv e2 e1) env d d2           (**r ⇒ [Γc ; γ ; d ⊢〚e₂ ∘ᵉ e₁〛⇓ d₂] *)
      | sem_NRAEnvMapEnv : forall e c1 d c2,
          nraenv_sem_map_env e c1 d c2 ->                    (**r ∧ [Γc ; {c₁} ; d ⊢〚e〛χᵉ ⇓ {c₂}] *)
          nraenv_sem                                         (**r ⇒ [Γc ; {c₁} ; d ⊢〚χᵉ⟨e⟩〛⇓ {c₂}] *)
            (NRAEnvMapEnv e) (dcoll c1) d (dcoll c2)
      | sem_NRAEnvFlatMap : forall e1 e2 env d c1 c2,
          nraenv_sem e1 env d (dcoll c1) ->                  (**r   [Γc ; γ ; d ⊢〚e₁〛⇓ {c₁}] *)
          nraenv_sem_flat_map e2 env c1 c2 ->                (**r ∧ [Γc ; γ ; {c₁} ⊢〚e₂〛Χ ⇓ {c₂}] *)
          nraenv_sem (NRAEnvFlatMap e2 e1) env d (dcoll c2)      (**r ⇒ [Γc ; γ ; d ⊢〚Χ⟨e₂⟩(e₁)〛⇓ {c₂}] *)
      with nraenv_sem_map: nraenv -> data -> list data -> list data -> Prop :=
      | sem_NRAEnvMap_empty : forall e env,
          nraenv_sem_map e env nil nil                       (**r   [Γc ; γ ; {} ⊢〚e〛χ ⇓ {}] *)
      | sem_NRAEnvMap_cons : forall e env d1 c1 d2 c2,
          nraenv_sem e env d1 d2 ->                          (**r   [Γc ; γ ; d₁ ⊢〚e〛⇓ d₂]  *)
          nraenv_sem_map e env c1 c2 ->                      (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛χ ⇓ {c₂}] *)
          nraenv_sem_map e env (d1::c1) (d2::c2)             (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛χ ⇓ {d₂::c₂}] *)
      with nraenv_sem_map_product: nraenv -> data -> list data -> list data -> Prop :=
      | sem_NRAEnvMapProduct_empty : forall e env,
          nraenv_sem_map_product e env nil nil               (**r   [Γc ; γ ; {} ⊢〚e〛⋈ᵈ ⇓ {}] *)
      | sem_NRAEnvMapProduct_cons : forall e env d1 c1 c2 c3 c4,
          nraenv_sem e env d1 (dcoll c3) ->                  (**r   [Γc ; γ ; d₁ ⊢〚e〛⋈ᵈ ⇓ {c₃}]  *)
          map_concat_sem d1 c3 c4 ->                         (**r ∧ [d₁ χ⊕ c₃ ⇓ c₄] *)
          nraenv_sem_map_product e env c1 c2 ->              (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛⋈ᵈ ⇓ {c₂}] *)
          nraenv_sem_map_product e env (d1::c1) (c4 ++ c2)   (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛⋈ᵈ ⇓ {c₄}∪{c₂}] *)
      with nraenv_sem_select: nraenv -> data -> list data -> list data -> Prop :=
      | sem_NRAEnvSelect_empty : forall e env,
          nraenv_sem_select e env nil nil                    (**r   [Γc ; γ ; {} ⊢〚e〛σ ⇓ {}] *)
      | sem_NRAEnvSelect_true : forall e env d1 c1 c2,
          nraenv_sem e env d1 (dbool true) ->                (**r   [Γc ; γ ; d₁ ⊢〚e〛σ ⇓ true]  *)
          nraenv_sem_select e env c1 c2 ->                   (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛σ ⇓ {c₂}] *)
          nraenv_sem_select e env (d1::c1) (d1::c2)          (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛σ ⇓ {d₁::c₂}] *)
      | sem_NRAEnvSelect_false : forall e env d1 c1 c2,
          nraenv_sem e env d1 (dbool false) ->               (**r   [Γc ; γ ; d₁ ⊢〚e〛σ ⇓ false]  *)
          nraenv_sem_select e env c1 c2 ->                   (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛σ ⇓ {c₂}] *)
          nraenv_sem_select e env (d1::c1) c2                (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛σ ⇓ {c₂}] *)
      with nraenv_sem_map_env: nraenv -> list data -> data -> list data -> Prop :=
      | sem_NRAEnvMapEnv_empty : forall e d,
          nraenv_sem_map_env e nil d nil                     (**r   [Γc ; {} ; d ⊢〚e〛χᵉ ⇓ {}] *)
      | sem_NRAEnvMapEnv_cons : forall e d1 d c1 d2 c2,
          nraenv_sem e d1 d d2 ->                            (**r   [Γc ; d₁ ; d ⊢〚e〛⇓ d₂]  *)
          nraenv_sem_map_env e c1 d c2 ->                    (**r ∧ [Γc ; {c₁} ; d ⊢〚e〛χᵉ ⇓ {c₂}] *)
          nraenv_sem_map_env e (d1::c1) d (d2::c2)           (**r ⇒ [Γc ; {d₁::c₁} ; d ⊢〚e〛χᵉ ⇓ {d₂::c₂}] *)
      with nraenv_sem_flat_map: nraenv -> data -> list data -> list data -> Prop :=
      | sem_NRAEnvFlatMap_empty : forall e env,
          nraenv_sem_flat_map e env nil nil                  (**r   [Γc ; γ ; {} ⊢〚e〛Χ ⇓ {}] *)
      | sem_NRAEnvFlatMap_cons : forall e env d1 c1 c2 c3,
          nraenv_sem e env d1 (dcoll c2) ->                  (**r   [Γc ; γ ; d₁ ⊢〚e〛⇓ {c₂}]  *)
          nraenv_sem_flat_map e env c1 c3 ->                 (**r ∧ [Γc ; γ ; {c₁} ⊢〚e〛Χ ⇓ {c₃}] *)
          nraenv_sem_flat_map e env (d1::c1) (c2++c3)        (**r ⇒ [Γc ; γ ; {d₁::c₁} ⊢〚e〛Χ ⇓ {c₂}++{c₃}] *)
      .

    End Denotation.

    (** * Evaluation Semantics *)

    Section Evaluation.
      (** Evaluation semantics is obtained using macro expansion. *)
      
      Definition nraenv_eval (e:nraenv) (env:data) (x:data) : option data :=
        nraenv_core_eval h constant_env (nraenv_to_nraenv_core e) env x.
    End Evaluation.

    Section MacroCorrect.
      (** Proof that macro expension preserves semantics. *)
      
      Lemma nraenv_macro_map_correct e1 env c1 c2:
        (forall env d1 d2 : data,
            nraenv_sem e1 env d1 d2 ->
            nraenv_core_sem h constant_env (nraenv_to_nraenv_core e1) env d1 d2) ->
        nraenv_sem_map e1 env c1 c2 ->
        nraenv_core_sem_map h constant_env (nraenv_to_nraenv_core e1) env c1 c2.
      Proof.
        revert c2.
        induction c1; intros.
        - inversion H0; clear H0; subst.
          econstructor; eauto.
        - inversion H0; subst.
          econstructor; eauto.
      Qed.

      Lemma nraenv_macro_map_product_correct e1 env c1 c2:
        (forall env d1 d2 : data,
            nraenv_sem e1 env d1 d2 ->
            nraenv_core_sem h constant_env (nraenv_to_nraenv_core e1) env d1 d2) ->
        nraenv_sem_map_product e1 env c1 c2 ->
        nraenv_core_sem_map_product h constant_env (nraenv_to_nraenv_core e1) env c1 c2.
      Proof.
        revert c2.
        induction c1; intros.
        - inversion H0; clear H0; subst.
          econstructor; eauto.
        - inversion H0; subst.
          econstructor; eauto.
      Qed.

      Lemma nraenv_macro_select_correct e1 env c1 c2:
        (forall env d1 d2 : data,
            nraenv_sem e1 env d1 d2 ->
            nraenv_core_sem h constant_env (nraenv_to_nraenv_core e1) env d1 d2) ->
        nraenv_sem_select e1 env c1 c2 ->
        nraenv_core_sem_select h constant_env (nraenv_to_nraenv_core e1) env c1 c2.
      Proof.
        revert c2.
        induction c1; intros.
        - inversion H0; clear H0; subst.
          econstructor; eauto.
        - inversion H0; subst.
          econstructor; eauto.
          econstructor; eauto.
      Qed.

      Lemma nraenv_macro_map_env_correct e1 c1 d1 c2:
        (forall env d1 d2 : data,
            nraenv_sem e1 env d1 d2 ->
            nraenv_core_sem h constant_env (nraenv_to_nraenv_core e1) env d1 d2) ->
        nraenv_sem_map_env e1 c1 d1 c2 ->
        nraenv_core_sem_map_env h constant_env (nraenv_to_nraenv_core e1) c1 d1 c2.
      Proof.
        revert c2.
        induction c1; intros.
        - inversion H0; clear H0; subst.
          econstructor; eauto.
        - inversion H0; subst.
          econstructor; eauto.
      Qed.

      (** Evaluation is correct wrt. the cNRAEnv semantics. *)

      Lemma nraenv_macro_sem_correct : forall e env d1 d2,
          nraenv_sem e env d1 d2 ->
          nraenv_core_sem h constant_env (nraenv_to_nraenv_core e) env d1 d2.
      Proof.
        induction e; simpl; intros.
        - inversion H; econstructor; eauto.
        - inversion H; econstructor; eauto.
        - inversion H; econstructor; eauto.
        - inversion H; econstructor; eauto.
        - inversion H; econstructor; eauto.
        - inversion H; subst; econstructor; eauto.
          apply nraenv_macro_map_correct; eauto.
        - inversion H; subst; econstructor; eauto.
          apply nraenv_macro_map_product_correct; eauto.
        - inversion H; econstructor; eauto.
        - inversion H; subst; econstructor; eauto.
          apply nraenv_macro_select_correct; eauto.
        - inversion H; subst.
          + eapply sem_cNRAEnvDefault_empty; eauto.
          + eapply sem_cNRAEnvDefault_not_empty; eauto.
        - inversion H; subst.
          + eapply sem_cNRAEnvEither_left; eauto.
          + eapply sem_cNRAEnvEither_right; eauto.
        - inversion H; subst.
          + eapply sem_cNRAEnvEitherConcat_left; eauto.
          + eapply sem_cNRAEnvEitherConcat_right; eauto.
        - inversion H; subst; econstructor; eauto.
        - inversion H; subst; econstructor; eauto.
        - inversion H; subst; econstructor; eauto.
        - inversion H; subst; econstructor; eauto.
          apply nraenv_macro_map_env_correct; eauto.
        - inversion H; clear H; subst.
          (*
          unfold macro_cNRAEnvFlatMap.
          econstructor.
          econstructor; eauto.
          + clear H2 IHe2.
            Lemma test :
              exists

            induction c1.
            econstructor.
            inversion H6; subst.
            econstructor; eauto.
            specialize (IHe1 env a (dcoll c3) H3).
            
          Focus 2.
          inversion H2. *)
          admit.
        - inversion H.
        - inversion H.
        - inversion H.
      Admitted.
 
    End MacroCorrect.
    
  End Semantics.
    
  (** * Toplevel *)
  
  (** Top-level evaluation is used externally by the Q*cert
    compiler. It takes an NRAEnv expression and a global environment
    as input. The initial current environment is set to an empty
    record, and the initial current value to unit. *)

  Section Top.
    Context (h:list(string*string)).
    
    Definition nraenv_eval_top (q:nraenv) (env:bindings) :=
      nraenv_eval h (rec_sort env) q (drec nil) dunit.

  End Top.

  Section FreeVars.
    Fixpoint nraenv_free_vars (q:nraenv) : list string :=
      match q with
      | NRAEnvGetConstant s => s :: nil
      | NRAEnvID => nil
      | NRAEnvConst rd => nil
      | NRAEnvBinop _ q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvUnop _ q1 =>
        nraenv_free_vars q1
      | NRAEnvMap q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvMapProduct q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvProduct q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvSelect q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvEither ql qr =>
        nraenv_free_vars ql ++ nraenv_free_vars qr
      | NRAEnvEitherConcat q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvDefault q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvApp q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvEnv => nil
      | NRAEnvAppEnv q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvMapEnv q1 =>
        nraenv_free_vars q1
      | NRAEnvFlatMap q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvJoin q3 q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2 ++ nraenv_free_vars q3
      | NRAEnvNaturalJoin q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvProject _ q1 =>
        nraenv_free_vars q1
      | NRAEnvGroupBy _ _ q1 =>
        nraenv_free_vars q1
      | NRAEnvUnnest _ _ q1 =>
        nraenv_free_vars q1
      end.

    Lemma nraenv_free_vars_as_core (q:nraenv) :
      nraenv_core_free_vars (nraenv_to_nraenv_core q) = nraenv_free_vars q.
    Proof.
      induction q; simpl; try reflexivity;
        try solve[rewrite IHq1; rewrite IHq2; reflexivity|rewrite IHq;reflexivity].
      - rewrite IHq1; rewrite IHq2; rewrite IHq3.
        rewrite app_assoc; reflexivity.
      - rewrite IHq1; rewrite IHq2;
        repeat rewrite app_nil_r; reflexivity.
      - rewrite app_nil_r; rewrite IHq; reflexivity.
      - rewrite app_nil_r; rewrite IHq; reflexivity.
      - rewrite app_nil_r; rewrite app_nil_r; rewrite IHq; reflexivity.
    Qed.
  End FreeVars.

End NRAEnv.

(* begin hide *)
Delimit Scope nraenv_scope with nraenv.

Notation "h ⊢ EOp @ₓ x ⊣ c ; env" := (nraenv_eval h c EOp env x) (at level 10): nraenv_scope.
(* end hide *)

Tactic Notation "nraenv_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NRAEnvGetConstant"%string
  | Case_aux c "NRAEnvID"%string
  | Case_aux c "NRAEnvConst"%string
  | Case_aux c "NRAEnvBinop"%string
  | Case_aux c "NRAEnvUnop"%string
  | Case_aux c "NRAEnvMap"%string
  | Case_aux c "NRAEnvMapProduct"%string
  | Case_aux c "NRAEnvProduct"%string
  | Case_aux c "NRAEnvSelect"%string
  | Case_aux c "NRAEnvDefault"%string
  | Case_aux c "NRAEnvEither"%string
  | Case_aux c "NRAEnvEitherConcat"%string
  | Case_aux c "NRAEnvApp"%string
  | Case_aux c "NRAEnvEnv"%string
  | Case_aux c "NRAEnvAppEnv"%string
  | Case_aux c "NRAEnvMapEnv"%string
  | Case_aux c "NRAEnvFlatMap"%string
  | Case_aux c "NRAEnvJoin"%string
  | Case_aux c "NRAEnvNaturalJoin"%string
  | Case_aux c "NRAEnvProject"%string
  | Case_aux c "NRAEnvGroupBy"%string
  | Case_aux c "NRAEnvUnnest"%string].

