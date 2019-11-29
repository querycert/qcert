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

Require Import String.
Require Import List.
Require Import Arith.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRS.
Require Import NNRSEval.
Require Import NNRSSem.
Require Import NNRSSemEval.
Require Import NNRSVars.

Section TNNRS.
  (** Typing rules for NNRS *)
  Context {m:basic_model}.

  Definition pd_tbindings := list (string*option rtype).
  Definition mc_tbindings := list (string*rtype).
  Definition md_tbindings := list (string*rtype).

  Definition preserves_Some {A B} (f:A->option B) (xd yd:A) : Prop
    := forall xd', f xd = Some xd' -> exists yd', f yd= Some yd'.

  Global Instance preserves_Some_pre {A B} (f:A->option B)
    : PreOrder (preserves_Some f).
  Proof.
    constructor; red; unfold preserves_Some; firstorder.
  Qed.


  Lemma Forall2_preserves_Some_snd_update_first {B} l v (d:B) :
    Forall2 (preserves_Some snd) l (update_first string_dec l v (Some d)).
  Proof.
    induction l; simpl; trivial.
    destruct a.
    match_destr.
    - subst.
      constructor; try reflexivity.
      red; simpl; intros; subst; eauto.
    - constructor; eauto.
      reflexivity.
  Qed.
  
  Definition pd_bindings_type (b:pd_bindings) (t:pd_tbindings)
    := Forall2 (fun xy1 xy2 =>
                  (fst xy1) = (fst xy2)
                  /\ lift2Pr data_type (snd xy1) (snd xy2)) b t.

  Definition mc_bindings_type (b:mc_bindings) (t:mc_tbindings)
    := Forall2 (fun xy1 xy2 =>
                  (fst xy1) = (fst xy2)
                  /\ Forall (fun d => data_type d (snd xy2)) (snd xy1)) b t.

  Definition md_bindings_type (b:md_bindings) (t:md_tbindings)
    := Forall2 (fun xy1 xy2 =>
                  (fst xy1) = (fst xy2)
                  /\ forall d, Some d = snd xy1 ->
                               data_type d (snd xy2)) b t.
  
  Section typ.
    Context (Γc:tbindings).

    Reserved Notation "[ Γ  ⊢ e ▷ τ ]".

    Inductive nnrs_expr_type : pd_tbindings -> nnrs_expr -> rtype -> Prop :=
    | type_NNRSGetConstant {τ} Γ s :
        tdot Γc s = Some τ ->
        [ Γ ⊢ NNRSGetConstant s ▷ τ ]
    | type_NNRSVar {τ} Γ v :
        lookup equiv_dec Γ v = Some (Some τ) ->
        [ Γ ⊢ NNRSVar v ▷ τ ]
    | type_NNRSConst {τ} Γ c :
        normalize_data brand_relation_brands c ▹ τ ->
        [ Γ ⊢ NNRSConst c ▷ τ ]
    | type_NNRSBinop  {τ₁ τ₂ τ} Γ b e₁ e₂ :
        binary_op_type b τ₁ τ₂ τ ->
        [ Γ ⊢ e₁ ▷ τ₁ ] ->
        [ Γ ⊢ e₂ ▷ τ₂ ] ->
        [ Γ ⊢ NNRSBinop b e₁ e₂ ▷ τ ]
    | type_NNRSUnop {τ₁ τ} Γ u e :
        unary_op_type u τ₁ τ ->
        [ Γ ⊢ e ▷ τ₁ ] ->
        [ Γ ⊢ NNRSUnop u e ▷ τ ]
    | type_NNRSGroupBy {τl k pf} Γ g sl e :
        sublist sl (domain τl) ->
        [ Γ ⊢ e ▷ Coll (Rec k τl pf) ] ->
        [ Γ ⊢ NNRSGroupBy g sl e ▷ GroupBy_type g sl k τl pf ]
    where
    "[ Γ ⊢ e ▷ τ ]" := (nnrs_expr_type Γ e τ) : nnrs
    .

    Notation "[ Γ  ⊢ e ▷ τ ]" := (nnrs_expr_type Γ e τ) : nnrs.

    (* Observation: all the contexts are stacklike in their domain,
       and there is no reason to allow strong updates, since there is a phase
       distinction between mutating/reading (and we have a join operator on types)
       So we can model the types of all the contexts as stacks, even though the 
       evaluation semantics models them in a more state-like way.
     *)

    (* TODO: move this out.  This is also useful for optimizations.
       In particular, if not must_assign, and it is well-typed,
       then we can replace it with a Seq
     *)
    Fixpoint nnrs_stmt_must_assign (s:nnrs_stmt) (x:var) : Prop
      := match s with
         | NNRSSeq s₁ s₂ =>
           nnrs_stmt_must_assign s₁ x \/ nnrs_stmt_must_assign s₂ x
         | NNRSLet v e₁ s₂ =>
           nnrs_stmt_must_assign s₂ x
         | NNRSLetMut v s₁ s₂ =>
           (v <> x /\ nnrs_stmt_must_assign s₁ x) \/ nnrs_stmt_must_assign s₂ x
         | NNRSLetMutColl v s₁ s₂ =>
           nnrs_stmt_must_assign s₁ x \/ nnrs_stmt_must_assign s₂ x
         | NNRSAssign v e =>
           v = x
         | NNRSPush v e =>
           False
         | NNRSFor v e s₀ => (* Since the loop may not execute *)
           False
         | NNRSIf e s₁ s₂ =>
           nnrs_stmt_must_assign s₁ x /\ nnrs_stmt_must_assign s₂ x
         | NNRSEither e x₁ s₁ x₂ s₂ =>
           nnrs_stmt_must_assign s₁ x /\ nnrs_stmt_must_assign s₂ x
         end.

    Reserved Notation "[  Γ , Δc , Δd  ⊢ s ]".

    Inductive nnrs_stmt_type :
      pd_tbindings -> mc_tbindings -> md_tbindings ->
      nnrs_stmt -> Prop :=
    | type_NNRSSeq Γ Δc Δd s₁ s₂ :
        [  Γ , Δc , Δd  ⊢ s₁ ] -> 
        [  Γ , Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSSeq s₁ s₂ ]
    | type_NNRSLet Γ Δc Δd τ x e₁ s₂ :
        [  Γ  ⊢ e₁ ▷ τ ] -> 
        [  (x,Some τ)::Γ , Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSLet x e₁ s₂ ]
    | type_NNRSLetMutDef Γ Δc Δd τ x s₁ s₂ :
        nnrs_stmt_must_assign s₁ x ->
        [  Γ , Δc , (x,τ)::Δd  ⊢ s₁ ]  ->
        [  (x,Some τ)::Γ, Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSLetMut x s₁ s₂ ]
    | type_NNRSLetMutNotUsed Γ Δc Δd x τ s₁ s₂ :
        [  Γ , Δc , (x,τ)::Δd  ⊢ s₁ ]  ->
        [  (x,None)::Γ, Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSLetMut x s₁ s₂ ]
    | type_NNRSLetMutColl Γ Δc Δd τ x s₁ s₂ :
        [  Γ , (x,τ)::Δc , Δd  ⊢ s₁ ]  ->
        [  (x,Some (Coll τ))::Γ, Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSLetMutColl x s₁ s₂ ]
    | type_NNRSAssign Γ Δc Δd τ x e :
        [ Γ ⊢ e ▷ τ ] ->
        lookup string_dec Δd x = Some τ ->
        [  Γ , Δc , Δd  ⊢ NNRSAssign x e ]
    | type_NNRSPush Γ Δc Δd τ x e :
        [ Γ ⊢ e ▷ τ ] ->
        lookup string_dec Δc x = Some τ ->
        [  Γ , Δc , Δd  ⊢ NNRSPush x e ]
    | type_NNRSFor Γ Δc Δd τ x e₁ s₂ :
        [  Γ  ⊢ e₁ ▷ Coll τ ] -> 
        [  (x,Some τ)::Γ , Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSFor x e₁ s₂ ]
    | type_NNRSIf Γ Δc Δd e s₁ s₂ :
        [  Γ  ⊢ e ▷ Bool] -> 
        [  Γ , Δc , Δd  ⊢ s₁ ] -> 
        [  Γ , Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSIf e s₁ s₂ ]
    | type_NNRSEither Γ Δc Δd τl τr e x₁ s₁ x₂ s₂ :
        [  Γ  ⊢ e ▷ Either τl τr] -> 
        [  (x₁,Some τl)::Γ , Δc , Δd  ⊢ s₁ ] -> 
        [  (x₂,Some τr)::Γ , Δc , Δd  ⊢ s₂ ]  ->
        [  Γ , Δc , Δd  ⊢ NNRSEither e x₁ s₁ x₂ s₂ ]
    where
    "[ Γ , Δc , Δd  ⊢ s ]" := (nnrs_stmt_type Γ Δc  Δd s) : nnrs
    .

    Notation "[ Γ , Δc , Δd  ⊢ s ]" := (nnrs_stmt_type Γ Δc  Δd s) : nnrs.
  End typ.

  Notation "[ Γc ; Γ  ⊢ e ▷ τ ]" := (nnrs_expr_type Γc Γ e τ) : nnrs.
  Notation "[ Γc ; Γ , Δc , Δd  ⊢ s ]" := (nnrs_stmt_type Γc Γ Δc  Δd s) : nnrs.

  Local Open Scope nnrs.
  
  Definition nnrs_type Γc (si:nnrs) τ
    := let (s, ret) := si in
       [ Γc ; nil , nil , (ret, τ)::nil  ⊢ s ].

  Notation "[ Γc ⊢ si ▷ τ ]" := (nnrs_type Γc si τ) : nnrs.

  
  Lemma typed_nnrs_expr_yields_typed_data {σc Γc} {σ Γ} {e τ} :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    [ Γc ; Γ  ⊢ e ▷ τ ] ->
    exists d,
      nnrs_expr_eval brand_relation_brands σc σ e = Some d
      /\ d ▹ τ.
  Proof.
    intros Γctyp Γtyp etyp.
    dependent induction etyp; simpl.
    - unfold tdot in *.
      apply (Forall2_lookupr_some Γctyp H).
    - destruct (Forall2_lookup_some Γtyp H) as [?[??]].
      destruct x; simpl in *; try contradiction.
      rewrite H0; unfold id; simpl.
      eauto.
    - eauto.
    - destruct IHetyp1 as [?[eqq1 ?]]; trivial.
      destruct IHetyp2 as [?[eqq2 ?]]; trivial.
      rewrite eqq1, eqq2; simpl.
      eapply typed_binary_op_yields_typed_data; eauto.
    - destruct IHetyp as [?[eqq ?]]; trivial.
      rewrite eqq; simpl.
      eapply typed_unary_op_yields_typed_data; eauto.
    - destruct IHetyp as [?[eqq ?]]; trivial.
      rewrite eqq; simpl.
      dtype_inverter.
      apply typed_group_by_nested_eval_table_yields_typed_data; trivial.
  Qed.

  (* Computationally friendly version of this theorem *)
  Theorem typed_nnrs_expr_yields_typed_data_compute {σc Γc} {σ Γ} {e τ} :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    [ Γc ; Γ  ⊢ e ▷ τ ] ->
    {d |
     nnrs_expr_eval brand_relation_brands σc σ e = Some d
     & d ▹ τ}.
  Proof.
    intros Γctyp Γtyp etyp.
    generalize (typed_nnrs_expr_yields_typed_data Γctyp Γtyp etyp); intros HH.
    destruct (nnrs_expr_eval brand_relation_brands σc σ e).
    - exists d; destruct HH as [?[??]]; simpl; congruence.
    - cut False; [contradiction | ].
      destruct HH as [?[??]]; simpl; congruence.
  Defined.

  Lemma nnrs_stmt_md_preserves_some {s σc σ ψc ψd σ' ψc' ψd'} :
    nnrs_stmt_eval brand_relation_brands σc σ ψc ψd s =
    Some (σ', ψc', ψd') ->
    Forall2 (preserves_Some snd) ψd ψd'.
  Proof.
    revert σ ψc ψd σ' ψc' ψd'.
    induction s; simpl; intros σ ψc ψd σ' ψc' ψd' eqq1; simpl.
    - match_option_in eqq1.
      destruct p as [[??]?].
      specialize (IHs1 _ _ _ _ _ _ eqq).
      specialize (IHs2 _ _ _ _ _ _ eqq1).
      etransitivity; eauto.
    - repeat match_option_in eqq1.
      destruct p as [[??]?].
      destruct p; try discriminate.
      invcs eqq1.
      apply (IHs _ _ _ _ _ _ eqq0).
    - match_option_in eqq1.
      destruct p as [[??]?].
      destruct m1; try discriminate.
      destruct p0; simpl in *.
      specialize (IHs1 _ _ _ _ _ _ eqq); subst.
      invcs IHs1.
      match_option_in eqq1.
      destruct p0 as [[??]?].
      destruct p0; simpl in *; try discriminate.
      invcs eqq1.
      specialize (IHs2 _ _ _ _ _ _ eqq0); subst.
      etransitivity; eauto.
    - match_option_in eqq1.
      destruct p as [[??]?].
      destruct m0; try discriminate.
      destruct p0; simpl in *.
      specialize (IHs1 _ _ _ _ _ _ eqq); subst.
      match_option_in eqq1.
      destruct p0 as [[??]?].
      destruct p0; simpl in *; try discriminate.
      invcs eqq1.
      specialize (IHs2 _ _ _ _ _ _ eqq0); subst.
      etransitivity; eauto.
    - match_option_in eqq1.
      match_option_in eqq1.
      invcs eqq1.
      apply Forall2_preserves_Some_snd_update_first.
    - match_option_in eqq1.
      match_option_in eqq1.
      invcs eqq1.
      reflexivity.
    - match_option_in eqq1.
      destruct d; try discriminate.
      clear eqq.
      revert σ ψc ψd σ' ψc' ψd' eqq1.
      induction l; intros σ ψc ψd σ' ψc' ψd' eqq1.
      + invcs eqq1; reflexivity.
      + match_option_in eqq1.
        destruct p as [[??]?].
        destruct p; try discriminate.
        specialize (IHs _ _ _ _ _ _ eqq).
        specialize (IHl _ _ _ _ _ _ eqq1).
        etransitivity; eauto.
    - match_option_in eqq1.
      destruct d; try discriminate.
      clear eqq.
      destruct b; eauto.
    - match_option_in eqq1.
      destruct d; try discriminate
      ; clear eqq
      ; match_option_in eqq1
      ; destruct p as [[??]?]
      ; destruct p; simpl in *; try discriminate
      ; invcs eqq1
      ; eauto.
  Qed.

  Lemma nnrs_stmt_md_preserves_some2 {s σc σ ψc ψd σ' ψc' ψd'} :
    nnrs_stmt_eval brand_relation_brands σc σ ψc ψd s =
    Some (σ', ψc', ψd') ->
    Forall2 (fun d1 d2 => fst d1 = fst d2 /\ flip (preserves_Some id) (snd d1) (snd d2)) ψd' ψd.
  Proof.
    intros eqq1.
    generalize (nnrs_stmt_md_preserves_some eqq1); intros F.
    generalize (nnrs_stmt_eval_mdenv_domain_stack eqq1); intros domeq1.
    clear eqq1.
    induction F; simpl; trivial.
    invcs domeq1.
    constructor; eauto.
  Qed.

  Lemma nnrs_stmt_preserves_md_some_cons {s x σc σ ψc i ψd σ' ψc' o l} :
    nnrs_stmt_eval brand_relation_brands σc σ ψc ((x, Some i) :: ψd) s =
    Some (σ', ψc', (x, o) :: l) ->
    exists d, o = Some d.
  Proof.
    intros eqq.
    generalize (nnrs_stmt_md_preserves_some eqq); intros HH.
    invcs HH.
    unfold preserves_Some in *.
    destruct o; simpl in *; eauto.
  Qed.

  Lemma nnrs_stmt_must_assign_assigns {s x σc σ ψc ψd σ' ψc' ψd'} :
    nnrs_stmt_must_assign s x ->
    nnrs_stmt_eval brand_relation_brands σc σ ψc ψd s =
    Some (σ', ψc', ψd') ->
    In x (domain ψd) ->
    exists d, lookup string_dec ψd' x = Some (Some d).
  Proof.
    revert σ ψc ψd σ' ψc' ψd'.
    induction s; simpl; intros σ ψc ψd σ' ψc' ψd' ma eqq1 inn; simpl.
    - match_option_in eqq1.
      destruct p as [[??]?].
      generalize (nnrs_stmt_md_preserves_some2 eqq1); intros F.
      destruct ma.
      + destruct (IHs1 _ _ _ _ _ _ H eqq inn).
        destruct (Forall2_lookup_some F H0) as [dd [??]].
        unfold flip, id, preserves_Some in H2.
        destruct (H2 _ (eq_refl _)); subst.
        eauto.
      + apply (IHs2 _ _ _ _ _ _ H eqq1).
        generalize (nnrs_stmt_eval_mdenv_domain_stack eqq)
        ; intros domeq1.
        congruence.
    - repeat match_option_in eqq1.
      destruct p as [[??]?].
      destruct p; try discriminate.
      invcs eqq1.
      eauto.
    - match_option_in eqq1.
      destruct p as [[??]?].
      destruct m1; try discriminate.
      destruct p0.
      match_option_in eqq1.
      destruct p0 as [[??]?].
      destruct p0; try discriminate.
      invcs eqq1.
      generalize (nnrs_stmt_md_preserves_some2 eqq0); intros F.
      destruct ma as [[neq ma]|ma].
      + destruct (IHs1 _ _ _ _ _ _ ma eqq); [simpl;eauto | ].
        simpl in H.
        generalize (nnrs_stmt_eval_mdenv_domain_stack eqq)
        ; intros domeq.
        simpl in domeq; invcs domeq.
        match_destr_in H.
        * congruence.
        * destruct (Forall2_lookup_some F H) as [dd [??]].
          unfold flip, id, preserves_Some in H1.
          destruct (H1 _ (eq_refl _)); subst.
          eauto.
      + apply (IHs2 _ _ _ _ _ _ ma eqq0).
        generalize (nnrs_stmt_eval_mdenv_domain_stack eqq)
        ; intros domeq1.
        simpl in domeq1; invcs domeq1.
        congruence.
    - match_option_in eqq1.
      destruct p as [[??]?].
      destruct m0; try discriminate.
      destruct p0.
      match_option_in eqq1.
      destruct p0 as [[??]?].
      destruct p0; try discriminate.
      invcs eqq1.
      generalize (nnrs_stmt_md_preserves_some2 eqq0); intros F.
      destruct ma as [ma|ma].
      + destruct (IHs1 _ _ _ _ _ _ ma eqq); [simpl;eauto | ].
        destruct (Forall2_lookup_some F H) as [dd [??]].
        unfold flip, id, preserves_Some in H1.
        destruct (H1 _ (eq_refl _)); subst.
        eauto.
      + destruct (IHs2 _ _ _ _ _ _ ma eqq0); [simpl;eauto | ]; eauto.
        generalize (nnrs_stmt_eval_mdenv_domain_stack eqq)
        ; intros domeq1.
        simpl in domeq1; invcs domeq1.
        congruence.
    - repeat match_option_in eqq1.
      invcs eqq1.
      generalize (lookup_update_eq_in equiv_dec inn (n:=Some d)); intros HH.
      unfold equiv_dec, string_eqdec in *.
      eauto.
    - contradiction.
    - contradiction.
    - match_option_in eqq1.
      destruct ma as [ma1 ma2].
      destruct d; try discriminate.
      destruct b; eauto.
    - match_option_in eqq1.
      destruct ma as [ma1 ma2].
      destruct d; try discriminate
      ; match_option_in eqq1
      ; destruct p as [[??]?]
      ; destruct p; try discriminate
      ; invcs eqq1
      ; eauto.
  Qed.
  
  Lemma nnrs_stmt_must_assign_assigns_cons {s x σc σ ψc i ψd σ' ψc' o l} :
    nnrs_stmt_must_assign s x ->
    nnrs_stmt_eval brand_relation_brands σc σ ψc ((x, i) :: ψd) s =
    Some (σ', ψc', (x, o) :: l) ->
    exists d, o = Some d.
  Proof.
    intros ma eqq1.
    generalize (nnrs_stmt_must_assign_assigns ma eqq1); simpl.
    intuition.
    destruct (string_dec x x); [ | congruence].
    destruct H as [? eqq2].
    invcs eqq2; eauto.
  Qed.

  Lemma mc_bindings_type_lookup_back {ψc Δc τd x} :
    mc_bindings_type ψc Δc ->
    lookup string_dec Δc x = Some τd ->
    exists dl,
      lookup string_dec ψc x = Some dl
      /\ Forall (fun d => d ▹ τd) dl.
  Proof.
    intro mcb; induction mcb; simpl; try discriminate.
    destruct x0; destruct y; destruct H; simpl in *; subst.
    match_case; intros.
    invcs H1; subst.
    eauto.
  Qed.

  Lemma md_bindings_type_lookup_back {ψd Δd τd x} :
    md_bindings_type ψd Δd ->
    lookup string_dec Δd x = Some τd ->
    exists o,
      lookup string_dec ψd x = Some o
      /\ forall d : data, Some d = o -> d ▹ τd.
  Proof.
    intro mdb; induction mdb; simpl; try discriminate.
    destruct x0; destruct y; destruct H; simpl in *; subst.
    match_case; intros.
    invcs H1.
    eauto.
  Qed.

  Lemma mc_bindings_type_update_first_same  ψc Δc x dl τd :
    mc_bindings_type ψc Δc ->
    lookup string_dec Δc x = Some τd ->
    Forall (fun d => d ▹ τd) dl ->
    mc_bindings_type (update_first string_dec ψc x dl) Δc.
  Proof.
    intro mcb; induction mcb; simpl; try discriminate.
    destruct x0; destruct y; destruct H; simpl in *; subst.
    match_case; intros.
    - invcs H1; subst.
      constructor; simpl; intuition.
    - constructor; eauto 3.
      apply IHmcb; eauto.
  Qed.

  Lemma md_bindings_type_update_first_same  ψd Δd x d τd :
    md_bindings_type ψd Δd ->
    lookup string_dec Δd x = Some τd ->
    d ▹ τd ->
    md_bindings_type (update_first string_dec ψd x (Some d)) Δd.
  Proof.
    intro mdb; induction mdb; simpl; try discriminate.
    destruct x0; destruct y; destruct H; simpl in *; subst.
    match_case; intros.
    - invcs H1; subst.
      constructor; simpl; intuition.
      invcs H1; trivial.
    - constructor; eauto 3.
      apply IHmdb; eauto.
  Qed.

  (** Main lemma for the type correctness of NNNRC *)

  Theorem typed_nnrs_stmt_yields_typed_data {σc σ ψc ψd} {Γc Γ Δc Δd}  (s:nnrs_stmt) :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    mc_bindings_type ψc Δc ->
    md_bindings_type ψd Δd ->
    [  Γc ; Γ , Δc , Δd  ⊢ s ] ->
    (exists σ' ψc' ψd',
        (nnrs_stmt_eval brand_relation_brands σc σ ψc ψd s) = Some (σ', ψc', ψd')
        /\ pd_bindings_type σ' Γ
        /\ mc_bindings_type ψc' Δc
        /\ md_bindings_type ψd' Δd).
  Proof.
    intros typσc typσ typψc typψd typs.
    revert σ ψc ψd typσ typψc typψd.
    
    dependent induction typs; simpl; intros σ ψc ψd typσ typψc typψd.
    - destruct (IHtyps1 _ _ _ typσ typψc typψd)
        as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]].
      unfold var in *; rewrite eqq1.
      destruct (IHtyps2 _ _ _ typσ' typψc' typψd')
        as [σ'' [ψc'' [ψd'' [eqq2 [typσ'' [typψc'' typψd'']]]]]].
      rewrite eqq2.
      do 3 eexists; split; try reflexivity.
      eauto. 
    - destruct ( typed_nnrs_expr_yields_typed_data typσc typσ H)
        as [d [eqq typd]].
      rewrite eqq.
      assert (typσcons:pd_bindings_type ((x,Some d)::σ) ((x, Some τ) :: Γ)).
      { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; tauto. }
      destruct (IHtyps _ _ _ typσcons typψc typψd)
        as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]].
      unfold var in *; rewrite eqq1.
      invcs typσ'; simpl in *.
      do 3 eexists; split; try reflexivity.
      tauto.
    - assert (typψdcons:md_bindings_type ((x,None)::ψd) ((x, τ) :: Δd)).
      { unfold md_bindings_type in *; simpl; constructor; trivial; simpl; split; trivial.
        intros; discriminate.
      } 
      destruct (IHtyps1 _ _ _ typσ typψc typψdcons)
        as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]].
      unfold var in *; rewrite eqq1.
      invcs typψd' ; simpl in *.
      destruct x0; destruct H3; simpl in *; subst.
      destruct (nnrs_stmt_must_assign_assigns_cons H eqq1) as [d ?]
      ; subst.
      
      assert (typσcons:pd_bindings_type ((x,Some d)::σ') ((x, Some τ) :: Γ)).
      { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto. } 
      destruct (IHtyps2 _ _ _ typσcons typψc' H4)
        as [σ'' [ψc'' [ψd'' [eqq2 [typσ'' [typψc'' typψd'']]]]]].
      rewrite eqq2.
      destruct σ''; invcs typσ''.
      do 3 eexists; split; try reflexivity.
      eauto.
    - assert (typψdcons:md_bindings_type ((x,None)::ψd) ((x, τ) :: Δd)).
      { unfold md_bindings_type in *; simpl; constructor; trivial; simpl; split; trivial.
        intros; discriminate.
      } 
      destruct (IHtyps1 _ _ _ typσ typψc typψdcons)
        as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]].
      unfold var in *; rewrite eqq1.
      invcs typψd' ; simpl in *.
      destruct x0; destruct H2; simpl in *; subst.
      assert (typσcons:pd_bindings_type ((x,o)::σ') ((x, None) :: Γ)).
      { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto.
        destruct o; simpl; trivial. }
      destruct (IHtyps2 _ _ _ typσcons typψc' H3)
        as [σ'' [ψc'' [ψd'' [eqq2 [typσ'' [typψc'' typψd'']]]]]].
      rewrite eqq2.
      destruct σ''; invcs typσ''.
      do 3 eexists; split; try reflexivity.
      eauto.
    - assert (typψccons:mc_bindings_type ((x,[])::ψc) ((x, τ) :: Δc)).
      { unfold md_bindings_type in *; simpl; constructor; trivial; simpl; split; trivial.
      } 
      destruct (IHtyps1 _ _ _ typσ typψccons typψd)
        as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]].
      unfold var in *; rewrite eqq1.
      invcs typψc' ; simpl in *.
      destruct x0; destruct H2; simpl in *; subst.
      assert (typσcons:pd_bindings_type ((x,Some (dcoll l0))::σ') ((x, Some (Coll τ)) :: Γ)).
      { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto.
        constructor; trivial. }
      destruct (IHtyps2 _ _ _ typσcons H3 typψd')
        as [σ'' [ψc'' [ψd'' [eqq2 [typσ'' [typψc'' typψd'']]]]]].
      rewrite eqq2.
      invcs typσ''.
      do 3 eexists; split; try reflexivity.
      eauto.
    - destruct ( typed_nnrs_expr_yields_typed_data typσc typσ H)
        as [d [eqq typd]].
      rewrite eqq.
      destruct (md_bindings_type_lookup_back typψd H0) as [? [eqq1 ?]].
      rewrite eqq1.
      do 3 eexists; split; try reflexivity.
      intuition.
      eapply md_bindings_type_update_first_same; eauto.
    - destruct ( typed_nnrs_expr_yields_typed_data typσc typσ H)
        as [d [eqq typd]].
      rewrite eqq.
      destruct (mc_bindings_type_lookup_back typψc H0) as [dd [eqq1 typdd]].
      rewrite eqq1.
      do 3 eexists; split; try reflexivity.
      intuition.
      eapply mc_bindings_type_update_first_same; eauto.
      apply Forall_app; trivial.
      constructor; trivial.
    - destruct ( typed_nnrs_expr_yields_typed_data typσc typσ H)
        as [d [eqq typd]].
      rewrite eqq.
      invcs typd; rtype_equalizer; subst.
      clear eqq H.
      revert σ ψc ψd typσ typψc typψd.
      induction dl; intros σ ψc ψd typσ typψc typψd.
      + do 3 eexists; split; try reflexivity.
        eauto.
      + invcs H2.
        assert (typσcons:pd_bindings_type ((x, Some a)::σ) ((x, Some τ) :: Γ)).
        { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto. }
        destruct (IHtyps _ _ _ typσcons typψc typψd)
          as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]].
        unfold var in *; rewrite eqq1.
        invcs typσ' ; simpl in *.
        destruct (IHdl H3 _ _ _ H5 typψc' typψd')
          as [σ'' [ψc'' [ψd'' [eqq2 [typσ'' [typψc'' typψd'']]]]]].
        unfold var in *; rewrite eqq2.
        do 3 eexists; split; try reflexivity.
        eauto.
    - destruct ( typed_nnrs_expr_yields_typed_data typσc typσ H)
        as [d [eqq typd]].
      rewrite eqq.
      invcs typd.
      destruct b.
      + destruct (IHtyps1 _ _ _ typσ typψc typψd)
          as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]]
        ; unfold var in *; rewrite eqq1.
        do 3 eexists; split; try reflexivity
        ; eauto.
      + destruct (IHtyps2 _ _ _ typσ typψc typψd)
          as [σ' [ψc' [ψd' [eqq2 [typσ' [typψc' typψd']]]]]]
        ; unfold var in *; rewrite eqq2.
        do 3 eexists; split; try reflexivity
        ; eauto.
    - destruct ( typed_nnrs_expr_yields_typed_data typσc typσ H)
        as [d [eqq typd]].
      rewrite eqq.
      invcs typd; rtype_equalizer; subst.
      + assert (typσcons:pd_bindings_type ((x₁,Some d0)::σ) ((x₁, Some τl) :: Γ)).
        { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto. }
        destruct (IHtyps1 _ _ _ typσcons typψc typψd)
          as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]]
        ; unfold var in *; rewrite eqq1.
        invcs typσ'.
        do 3 eexists; split; try reflexivity
        ; eauto.
      + assert (typσcons:pd_bindings_type ((x₂,Some d0)::σ) ((x₂, Some τr) :: Γ)).
        { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto. }
        destruct (IHtyps2 _ _ _ typσcons typψc typψd)
          as [σ' [ψc' [ψd' [eqq2 [typσ' [typψc' typψd']]]]]]
        ; unfold var in *; rewrite eqq2.
        invcs typσ'.
        do 3 eexists; split; try reflexivity
        ; eauto.
  Qed.

  Theorem typed_nnrs_yields_typed_data {σc} {Γc} {τ} {si:nnrs}:
    bindings_type σc Γc ->
    [ Γc ⊢ si ▷ τ ] ->
    exists o,
      nnrs_eval brand_relation_brands σc si = Some o
      /\ forall d, o = Some d -> d ▹ τ.
  Proof.
    destruct si as [q ret]; simpl.
    intros typσc typq.
    destruct (@typed_nnrs_stmt_yields_typed_data
                σc nil nil [(ret, None)]
                Γc nil nil [(ret, τ)] q)
      as [σ' [ψc' [ψd' [eqq1 [typσ' [typψc' typψd']]]]]]
    ; trivial; try solve[constructor].
    - constructor; trivial.
      simpl; intuition discriminate.
    - rewrite eqq1.
      invcs typψd'.
      destruct x; simpl in *.
      eexists; split; try reflexivity.
      intros; subst; intuition.
  Qed.

  Theorem typed_nnrs_yields_typed_data_used {σc} {Γc} {τ} {si:nnrs}:
    nnrs_stmt_must_assign (fst si) (snd si) ->
    bindings_type σc Γc ->
    [ Γc ⊢ si ▷ τ ] ->
    exists d,
      nnrs_eval brand_relation_brands σc si = Some (Some d)
      /\ d ▹ τ.
  Proof.
    intros.
    destruct (typed_nnrs_yields_typed_data H0 H1) as [d [eqq1 typ]].
    rewrite eqq1.
    destruct si.
    unfold nnrs_eval in eqq1.
    match_option_in eqq1.
    destruct p as [[??]?].
    destruct m1; try discriminate.
    destruct p0.
    invcs eqq1.
    generalize (nnrs_stmt_eval_mdenv_domain_stack eqq)
    ; intros domeq1.
    simpl in domeq1; invcs domeq1.
    symmetry in H4; apply domain_nil in H4; subst.
    destruct (nnrs_stmt_must_assign_assigns H eqq) as [dd inn];
      simpl in *; try tauto.
    match_destr_in inn.
    invcs inn.
    eauto.
  Qed.

  Theorem typed_nnrs_top_yields_typed_data {σc} {Γc} {τ} {si:nnrs}:
    bindings_type σc Γc ->
    [ rec_sort Γc ⊢ si ▷ τ ] ->
    forall d, 
      nnrs_eval_top brand_relation_brands σc si = Some d
      -> d ▹ τ.
  Proof.
    intros bt typ.
    destruct (typed_nnrs_yields_typed_data (bindings_type_sort _ _ bt) typ)
      as [o [eqq dtyp]].
    unfold nnrs_eval_top.
    rewrite eqq; unfold id; simpl; tauto.
  Qed.

  Theorem typed_nnrs_top_yields_typed_data_used {σc} {Γc} {τ} {si:nnrs}:
    nnrs_stmt_must_assign (fst si) (snd si) ->
    bindings_type σc Γc ->
    [ rec_sort Γc ⊢ si ▷ τ ] ->
    exists d,
      nnrs_eval_top brand_relation_brands σc si = Some d
      /\ d ▹ τ.
  Proof.
    intros ma bt typ.
    destruct (typed_nnrs_yields_typed_data_used ma (bindings_type_sort _ _ bt) typ) as [o [eqq dtyp]].
    unfold nnrs_eval_top.
    rewrite eqq; unfold id; simpl.
    eauto.
  Qed.
  
  Section sem.
    (* restates type soundness theorems in terms of the semantics.  
       This enables nicer notation :-) *)

    Theorem typed_nnrs_yields_typed_data_sem {σc} {Γc} {τ} {si:nnrs}:
      bindings_type σc Γc ->
      [ Γc ⊢ si ▷ τ ] ->
      exists o,
        [ brand_relation_brands , σc ⊢ si ⇓ o  ]
        /\ forall d, o = Some d -> d ▹ τ.
    Proof.
      intros typΓc typsi.
      destruct (typed_nnrs_yields_typed_data typΓc typsi)
        as [o [ev F]].
      apply nnrs_sem_eval in ev.
      eauto.
    Qed.

    Theorem typed_nnrs_yields_typed_data_used_sem {σc} {Γc} {τ} {si:nnrs}:
      nnrs_stmt_must_assign (fst si) (snd si) ->
      bindings_type σc Γc ->
      [ Γc ⊢ si ▷ τ ] ->
      exists d,
        [ brand_relation_brands , σc ⊢ si ⇓ Some d  ]
        /\ d ▹ τ.
    Proof.
      intros ma typΓc typsi.
      destruct (typed_nnrs_yields_typed_data_used ma typΓc typsi)
        as [o [ev F]].
      apply nnrs_sem_eval in ev.
      eauto.
    Qed.
  End sem.
  
  (* we are only sensitive to the environment up to lookup *)
  Global Instance nnrs_expr_type_lookup_equiv_prop {m:basic_model} :
    Proper (eq ==> lookup_equiv ==> eq ==> eq ==> iff) nnrs_expr_type.
  Proof.
    cut (Proper (eq ==> lookup_equiv ==> eq ==> eq ==> impl) nnrs_expr_type);
      unfold Proper, respectful, lookup_equiv, iff, impl; intros; subst;
        [intuition; eauto | ].
    rename y1 into e.
    rename y2 into τ.
    rename x0 into b1.
    rename y0 into b2.
    revert b1 b2 τ H0 H3.
    induction e; simpl; inversion 2; subst; econstructor; eauto 3.
    rewrite <- H0; trivial.
  Qed.

  Global Instance nnrs_stmt_type_lookup_equiv_prop :
    Proper (eq ==> lookup_equiv ==> lookup_equiv ==> lookup_equiv ==> eq ==> iff) nnrs_stmt_type.
  Proof.
    Hint Constructors nnrs_stmt_type.
    
    cut (Proper (eq ==> lookup_equiv ==> lookup_equiv ==> lookup_equiv ==> eq ==> impl) nnrs_stmt_type)
    ; unfold Proper, respectful, iff, impl; intros; subst;
      [unfold lookup_equiv in *; intuition; eauto | ].
    rename y3 into s.
    rename y into Γc.
    rename x0 into Γ₁.
    rename x1 into Δc₁.
    rename x2 into Δd₁.
    rename y0 into Γ₂.
    rename y1 into Δc₂.
    rename y2 into Δd₂.
    rename H0 into Γeqq.
    rename H1 into Δceqq.
    rename H2 into Δdeqq.
    rename H4 into typ.
    revert Γ₁ Δc₁ Δd₁ Γ₂ Δc₂ Δd₂ Γeqq Δceqq Δdeqq typ.
    induction s; simpl; intros Γ₁ Δc₁ Δd₁ Γ₂ Δc₂ Δd₂ Γeqq Δceqq Δdeqq typ
    ; invcs typ
    ; try solve [
            econstructor; trivial
            ; [try solve [rewrite <- Γeqq; eauto] | .. ]
            ; first [eapply IHs | eapply IHs1 | eapply IHs2]
            ; eauto; unfold lookup_equiv; simpl; intros; match_destr
          ].
    - econstructor; eauto.
      + rewrite <- Γeqq; eauto.
      + rewrite <- Δdeqq; eauto.
    - econstructor; eauto.
      + rewrite <- Γeqq; eauto.
      + rewrite <- Δceqq; eauto.
  Qed.

  Section unused.
    Local Open Scope nnrs.

    Hint Constructors nnrs_expr_type.
    Hint Constructors nnrs_stmt_type.

    Section remove.
      
      Lemma nnrs_expr_type_unused_remove_env Γc l Γ e v τ τo:
        (In v (domain l) \/
         ~ In v (nnrs_expr_free_vars e)) ->
        [  Γc ; l++(v,τ)::Γ ⊢ e ▷ τo ] ->
        [  Γc ; l++Γ ⊢  e ▷ τo  ].
      Proof.
        revert l Γ τo.
        nnrs_expr_cases (induction e) Case
        ; simpl; intros ll Γ τo inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn
        ; eauto 3.
        - Case "NNRSVar"%string.
          econstructor.
          repeat rewrite lookup_app in *
          ; simpl in *.
          match_option
          ; rewrite eqq in H1; try congruence.
          apply lookup_none_nin in eqq.
          match_destr_in H1; unfold equiv, complement in *.
          subst; intuition.
        - Case "NNRSBinop"%string.
          econstructor; intuition eauto.
      Qed.

      Lemma nnrs_stmt_type_unused_remove_env Γc l Γ Δc Δd s v τ:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_env_vars s)) ->
        [  Γc ; l++(v,τ)::Γ , Δc , Δd  ⊢ s ] ->
        [  Γc ; l++Γ , Δc , Δd  ⊢ s ].
      Proof.
        Hint Resolve nnrs_expr_type_unused_remove_env.
        revert l Γ Δc Δd τ.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l Γ Δc Δd τ inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn.
        - Case "NNRSSeq"%string.
          econstructor; intuition eauto.
        - Case "NNRSLet"%string.
          econstructor.
          + eapply nnrs_expr_type_unused_remove_env; eauto.
            tauto.
          + specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
            eapply IHs; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.
        - Case "NNRSLetMut"%string.
          econstructor; trivial.
          + intuition eauto.
          + specialize (IHs2 ((v0, Some τ0) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.           
        - Case "NNRSLetMut"%string.
          eapply type_NNRSLetMutNotUsed.
          + intuition eauto.
          + specialize (IHs2 ((v0, None) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.           
        - Case "NNRSLetMutColl"%string.
          econstructor.
          + intuition eauto.
          + specialize (IHs2 ((v0, Some (Coll τ0)) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.
        - Case "NNRSAssign"%string.        
          eauto.
        - Case "NNRSPush"%string.
          eauto.
        - Case "NNRSFor"%string.
          econstructor.
          + eapply nnrs_expr_type_unused_remove_env;[|eauto]; tauto.
          + specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
            eapply IHs; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.
        - Case "NNRSIf"%string.
          econstructor; intuition eauto.
        - Case "NNRSEither"%string.
          econstructor.
          + eapply nnrs_expr_type_unused_remove_env;[|eauto]; tauto.
          + specialize (IHs1 ((v0, Some τl) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition.
            destruct (remove_nin_inv H); eauto.
          + specialize (IHs2 ((v1, Some τr) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition.
            destruct (remove_nin_inv H2); eauto.
      Qed.

      Lemma nnrs_stmt_type_unused_remove_mdenv Γc l Γ Δc Δd s v τ:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_mdenv_vars s)) ->
        [  Γc ; Γ , Δc , l++(v,τ)::Δd  ⊢ s ] ->
        [  Γc ; Γ , Δc , l++Δd  ⊢ s ].
      Proof.
        revert l Γ Δc Δd τ.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l Γ Δc Δd τ inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn
        ; try solve [econstructor; intuition eauto].
        - Case "NNRSLetMut"%string.
          econstructor; trivial.
          + specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition.
            destruct (remove_nin_inv H0); eauto.
          + intuition eauto.
        - Case "NNRSLetMut"%string.
          eapply type_NNRSLetMutNotUsed.
          + specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition; destruct (remove_nin_inv H0); eauto.
          + intuition eauto.
        - Case "NNRSAssign"%string.
          econstructor; eauto.
          repeat rewrite lookup_app in *
          ; simpl in *.
          match_option
          ; rewrite eqq in H5; try congruence.
          apply lookup_none_nin in eqq.
          match_destr_in H5; unfold equiv, complement in *.
          subst; intuition.
      Qed.

      Lemma nnrs_stmt_type_unused_remove_mcenv Γc l Γ Δc Δd s v τ:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_mcenv_vars s)) ->
        [  Γc ; Γ , l++(v,τ)::Δc , Δd  ⊢ s ] ->
        [  Γc ; Γ , l++Δc , Δd  ⊢ s ].
      Proof.
        revert l Γ Δc Δd τ.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l Γ Δc Δd τ inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn
        ; try solve [econstructor; intuition eauto].
        - Case "NNRSLetMutColl"%string.
          econstructor.
          + specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition.
            destruct (remove_nin_inv H0); eauto.
          + intuition eauto.
        - Case "NNRSPush"%string.
          econstructor; eauto.
          repeat rewrite lookup_app in *
          ; simpl in *.
          match_option
          ; rewrite eqq in H5; try congruence.
          apply lookup_none_nin in eqq.
          match_destr_in H5; unfold equiv, complement in *.
          subst; intuition.
      Qed.

    End remove.
    
    Section add.
      
      Lemma nnrs_expr_type_unused_add_env Γc l Γ e v τ τo:
        (In v (domain l) \/
         ~ In v (nnrs_expr_free_vars e)) ->
        [  Γc ; l++Γ ⊢  e ▷ τo  ] ->
        [  Γc ; l++(v,τ)::Γ ⊢ e ▷ τo ].
      Proof.
        revert l Γ τo.
        nnrs_expr_cases (induction e) Case
        ; simpl; intros ll Γ τo inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn
        ; eauto 3.
        - Case "NNRSVar"%string.
          econstructor.
          repeat rewrite lookup_app in *
          ; simpl in *.
          match_option
          ; rewrite eqq in H1; try congruence.
          apply lookup_none_nin in eqq.
          match_destr; unfold equiv, complement in *.
          subst; intuition.
        - Case "NNRSBinop"%string.
          econstructor; intuition eauto.
      Qed.

      Lemma nnrs_stmt_type_unused_add_env Γc l Γ Δc Δd s v τ:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_env_vars s)) ->
        [  Γc ; l++Γ , Δc , Δd  ⊢ s ] ->
        [  Γc ; l++(v,τ)::Γ , Δc , Δd  ⊢ s ].
      Proof.
        Hint Resolve nnrs_expr_type_unused_add_env.
        revert l Γ Δc Δd τ.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l Γ Δc Δd τ inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn.
        - Case "NNRSSeq"%string.
          econstructor; intuition eauto.
        - Case "NNRSLet"%string.
          econstructor.
          + eapply nnrs_expr_type_unused_add_env; eauto.
            tauto.
          + specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
            eapply IHs; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.
        - Case "NNRSLetMut"%string.
          econstructor; trivial.
          + intuition eauto.
          + specialize (IHs2 ((v0, Some τ0) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.           
        - Case "NNRSLetMut"%string.
          eapply type_NNRSLetMutNotUsed.
          + intuition eauto.
          + specialize (IHs2 ((v0, None) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.           
        - Case "NNRSLetMutColl"%string.
          econstructor.
          + intuition eauto.
          + specialize (IHs2 ((v0, Some (Coll τ0)) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.
        - Case "NNRSAssign"%string.        
          eauto.
        - Case "NNRSPush"%string.
          eauto.
        - Case "NNRSFor"%string.
          econstructor.
          + eapply nnrs_expr_type_unused_add_env;[|eauto]; tauto.
          + specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
            eapply IHs; eauto.
            intuition; destruct (remove_nin_inv H1); eauto.
        - Case "NNRSIf"%string.
          econstructor; intuition eauto.
        - Case "NNRSEither"%string.
          econstructor.
          + eapply nnrs_expr_type_unused_add_env;[|eauto]; tauto.
          + specialize (IHs1 ((v0, Some τl) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition.
            destruct (remove_nin_inv H); eauto.
          + specialize (IHs2 ((v1, Some τr) :: l)); simpl in IHs2.
            eapply IHs2; eauto.
            intuition.
            destruct (remove_nin_inv H2); eauto.
      Qed.

      Lemma nnrs_stmt_type_unused_add_mdenv Γc l Γ Δc Δd s v τ:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_mdenv_vars s)) ->
        [  Γc ; Γ , Δc , l++Δd  ⊢ s ] ->
        [  Γc ; Γ , Δc , l++(v,τ)::Δd  ⊢ s ].
      Proof.
        revert l Γ Δc Δd τ.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l Γ Δc Δd τ inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn
        ; try solve [econstructor; intuition eauto].
        - Case "NNRSLetMut"%string.
          econstructor; trivial.
          + specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition.
            destruct (remove_nin_inv H0); eauto.
          + intuition eauto.
        - Case "NNRSLetMut"%string.
          eapply type_NNRSLetMutNotUsed.
          + specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition; destruct (remove_nin_inv H0); eauto.
          + intuition eauto.
        - Case "NNRSAssign"%string.
          econstructor; eauto.
          repeat rewrite lookup_app in *
          ; simpl in *.
          match_option
          ; rewrite eqq in H5; try congruence.
          apply lookup_none_nin in eqq.
          match_destr; unfold equiv, complement in *.
          subst; intuition.
      Qed.

      Lemma nnrs_stmt_type_unused_add_mcenv Γc l Γ Δc Δd s v τ:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_mcenv_vars s)) ->
        [  Γc ; Γ , l++Δc , Δd  ⊢ s ] ->
        [  Γc ; Γ , l++(v,τ)::Δc , Δd  ⊢ s ].
      Proof.
        revert l Γ Δc Δd τ.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l Γ Δc Δd τ inn typ
        ; invcs typ
        ; repeat rewrite in_app_iff in inn
        ; try solve [econstructor; intuition eauto].
        - Case "NNRSLetMutColl"%string.
          econstructor.
          + specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
            eapply IHs1; eauto.
            intuition.
            destruct (remove_nin_inv H0); eauto.
          + intuition eauto.
        - Case "NNRSPush"%string.
          econstructor; eauto.
          repeat rewrite lookup_app in *
          ; simpl in *.
          match_option
          ; rewrite eqq in H5; try congruence.
          apply lookup_none_nin in eqq.
          match_destr; unfold equiv, complement in *.
          subst; intuition.
      Qed.

    End add.
  End unused.

  Lemma nnrs_stmt_must_assign_is_free s x : nnrs_stmt_must_assign s x -> In x (nnrs_stmt_free_mdenv_vars s).
  Proof.
    induction s; simpl; intuition.
    rewrite in_app_iff.
    rewrite <- remove_in_neq by congruence.
    tauto.
  Qed.

  Lemma nnrs_expr_unused_tenv_free_env {Γc Γ e τ}:
    [Γc; Γ ⊢ e ▷ τ] ->
    forall x,
      lookup equiv_dec Γ x = Some None ->
      ~ In x (nnrs_expr_free_vars e).
  Proof.
    revert τ.
    induction e; simpl
    ; intros τ typ x eqq
    ; invcs typ
    ; simpl in *
    ; repeat rewrite in_app_iff
    ; try solve[intuition eauto].
    - destruct (v == x); unfold equiv, complement in *
      ; subst; intuition congruence.
  Qed.

  Lemma nnrs_expr_type_env_in_none_some {l1 Γc Γ v e τ} :
    [Γc; l1++(v, None) :: Γ ⊢ e ▷ τ] ->
    ~ In v (domain l1) ->
    forall τ',
      [Γc; l1++(v, Some τ') :: Γ ⊢ e ▷ τ].
  Proof.
    Hint Constructors nnrs_expr_type.
    revert τ.
    induction e; intros τ typ nin τ'
    ; invcs typ; eauto.
    econstructor.
    repeat rewrite lookup_app in *.
    match_destr; simpl in *.
    match_destr.
  Qed.

  (* Move to tnnrs *)
  Lemma nnrs_stmt_type_env_in_none_some {l1 Γc Γ Δc Δd v s} :
    [Γc; l1++(v, None) :: Γ, Δc, Δd ⊢ s] ->
    ~ In v (domain l1) ->
    forall τ,
      [Γc; l1++(v, Some τ) :: Γ, Δc, Δd ⊢ s].
  Proof.
    Hint Constructors nnrs_stmt_type.
    revert l1 Γ Δc Δd.
    nnrs_stmt_cases (induction s) Case
    ; simpl; intros l1 Γ Δc Δd typ nin τ
    ; invcs typ.
    - Case "NNRSSeq"%string.
      eauto.
    - Case "NNRSLet"%string.
      econstructor.
      + apply nnrs_expr_type_env_in_none_some; eauto.
      + destruct (v == v0); unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v0, Some τ0) :: l1)) in H6
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v0, Some τ0) :: l1))
          ; simpl; try tauto.
        * apply (IHs ((v0, Some τ0) :: l1))
          ; simpl; intuition.
    - Case "NNRSLetMut"%string.
      econstructor; eauto.
      + destruct (v == v0); unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v0, Some τ0) :: l1)) in H7
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v0, Some τ0) :: l1))
          ; simpl; try tauto.
        * apply (IHs2 ((v0, Some τ0) :: l1))
          ; simpl; intuition.
    - Case "NNRSLetMut"%string.
      eapply type_NNRSLetMutNotUsed; eauto.
      + destruct (v == v0); unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v0, None) :: l1)) in H6
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v0, None) :: l1))
          ; simpl; try tauto.
        * apply (IHs2 ((v0, None) :: l1))
          ; simpl; intuition.
    - Case "NNRSLetMutColl"%string.
      econstructor; eauto.
      + destruct (v == v0); unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v0, Some (Coll τ0)) :: l1)) in H6
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v0, Some (Coll τ0)) :: l1))
          ; simpl; try tauto.
        * apply (IHs2 ((v0, Some (Coll τ0)) :: l1))
          ; simpl; intuition.
    - Case "NNRSAssign"%string.
      econstructor; eauto.
      apply nnrs_expr_type_env_in_none_some; eauto.
    - Case "NNRSPush"%string.
      econstructor; eauto.
      apply nnrs_expr_type_env_in_none_some; eauto.
    - Case "NNRSFor"%string.
      econstructor.
      + apply nnrs_expr_type_env_in_none_some; eauto.
      + destruct (v == v0); unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v0, Some τ0) :: l1)) in H6
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v0, Some τ0) :: l1))
          ; simpl; try tauto.
        * apply (IHs ((v0, Some τ0) :: l1))
          ; simpl; intuition.
    - Case "NNRSIf"%string.
      econstructor; eauto.
      apply nnrs_expr_type_env_in_none_some; eauto.
    - Case "NNRSEither"%string.
      econstructor.
      + apply nnrs_expr_type_env_in_none_some; eauto.
      + destruct (v == v0); unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v0, Some τl) :: l1)) in H8
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v0, Some τl) :: l1))
          ; simpl; try tauto.
        * apply (IHs1 ((v0, Some τl) :: l1))
          ; simpl; intuition.
      + destruct (v == v1); unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v1, Some τr) :: l1)) in H9
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v1, Some τr) :: l1))
          ; simpl; try tauto.
        * apply (IHs2 ((v1, Some τr) :: l1))
          ; simpl; intuition.
  Qed.

  Lemma nnrs_stmt_type_env_cons_none_some {Γc Γ Δc Δd v s} :
    [Γc; (v, None) :: Γ, Δc, Δd ⊢ s] ->
    forall τ,
      [Γc; (v, Some τ) :: Γ, Δc, Δd ⊢ s].
  Proof.
    intros typ.
    apply (nnrs_stmt_type_env_in_none_some (l1:=nil)); simpl; tauto.
  Qed.
  

End TNNRS.

Notation "[ Γc ; Γ  ⊢ e ▷ τ ]" := (nnrs_expr_type Γc Γ e τ) : nnrs.
Notation "[ Γc ; Γ , Δc , Δd  ⊢ s ]" := (nnrs_stmt_type Γc Γ Δc  Δd s) : nnrs.
Notation "[ Γc ⊢ si ▷ τ ]" := (nnrs_type Γc si τ) : nnrs.
