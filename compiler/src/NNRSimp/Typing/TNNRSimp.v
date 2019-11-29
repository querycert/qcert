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
Require Import Bool.
Require Import List.
Require Import Arith.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSimp.
Require Import NNRSimpVars.
Require Import NNRSimpUsage.
Require Import NNRSimpEval.
Require Import NNRSimpSem.
Require Import NNRSimpSemEval.

Section TNNRSimp.

  (** Typing rules for NNRSimp *)
  Context {m:basic_model}.

  Definition pd_tbindings := list (string*rtype).

  Definition preserves_Some {A B} (f:A->option B) (xd yd:A) : Prop
    := forall xd', f xd = Some xd' -> exists yd', f yd = Some yd'.

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

  Definition has_some_parts {A B} {dec:EqDec A eq} (someparts:list A) (l:list (A*option B)) : Prop
    := Forall (fun x => match lookup equiv_dec l x with
                        | None => True
                        | Some None => False
                        | Some (Some _) => True
                        end) someparts.

  
  Lemma has_some_parts_app {A B} {dec:EqDec A eq} l1 l2 (σ:list (A*option B)) :
    has_some_parts (l1 ++ l2) σ <->
    has_some_parts l1 σ /\ has_some_parts l2 σ.
  Proof.
    unfold has_some_parts.
    split.
    - apply Forall_app_inv.
    - intros [??]; apply Forall_app; trivial.
  Qed.
  
  Global Instance has_some_parts_incl_proper {A B dec}: Proper ((@incl A) --> lookup_incl --> impl) (@has_some_parts A B dec).
  Proof.
    intros x y inclxy l1 l2 eql.
    unfold has_some_parts, equiv_dec.
    repeat rewrite Forall_forall.
    intros H ? inn.
    unfold flip in *.
    specialize (inclxy _ inn).
    specialize (H _ inclxy).
    match_option.
    apply eql in eqq.
    rewrite eqq in H.
    match_destr.
  Qed.

  Definition pd_bindings_type 
             (b:pd_bindings)
             (t:pd_tbindings)
    := Forall2 (fun xy1 xy2 =>
                  (fst xy1) = (fst xy2)
                  /\ forall d, snd xy1 = Some d -> d ▹ snd xy2) b t.

  Lemma pd_bindings_type_in_normalized {Γ σ} :
    pd_bindings_type σ Γ ->
    forall d,
      In (Some d) (map snd σ) ->
      data_normalized brand_relation_brands d.
  Proof.
    unfold pd_bindings_type.
    intros typ d inn.
    rewrite in_map_iff in inn.
    destruct inn as [[??][? inn]]; simpl in *; subst.
    apply (Forall2_In_l typ) in inn.
    destruct inn as [[??][?[? dt]]]; simpl in *; subst.
    specialize (dt _ (eq_refl _)).
    eauto.
  Qed.

  Lemma pd_bindings_type_cut_down_to {σ Γ} :
    pd_bindings_type σ Γ ->
    forall l,
      pd_bindings_type (cut_down_to σ l) (cut_down_to Γ l).
  Proof.
    induction 1; simpl; intros.
    - constructor.
    - destruct H as [eqq1 ?].
      rewrite eqq1.
      match_destr.
      constructor.
      + tauto.
      + apply IHForall2.
  Qed.
  
  Section typ.
    Context (Γc:tbindings).

    Reserved Notation "[ Γ  ⊢ e ▷ τ ]".

    Inductive nnrs_imp_expr_type : pd_tbindings -> nnrs_imp_expr -> rtype -> Prop :=
    | type_NNRSimpGetConstant {τ} Γ s :
        tdot Γc s = Some τ ->
        [ Γ ⊢ NNRSimpGetConstant s ▷ τ ]
    | type_NNRSimpVar {τ} Γ v :
        lookup equiv_dec Γ v = (Some τ) ->
        [ Γ ⊢ NNRSimpVar v ▷ τ ]
    | type_NNRSimpConst {τ} Γ c :
        normalize_data brand_relation_brands c ▹ τ ->
        [ Γ ⊢ NNRSimpConst c ▷ τ ]
    | type_NNRSimpBinop  {τ₁ τ₂ τ} Γ b e₁ e₂ :
        binary_op_type b τ₁ τ₂ τ ->
        [ Γ ⊢ e₁ ▷ τ₁ ] ->
        [ Γ ⊢ e₂ ▷ τ₂ ] ->
        [ Γ ⊢ NNRSimpBinop b e₁ e₂ ▷ τ ]
    | type_NNRSimpUnop {τ₁ τ} Γ u e :
        unary_op_type u τ₁ τ ->
        [ Γ ⊢ e ▷ τ₁ ] ->
        [ Γ ⊢ NNRSimpUnop u e ▷ τ ]
    | type_NNRSimpGroupBy {τl k pf} Γ g sl e :
        sublist sl (domain τl) ->
        [ Γ ⊢ e ▷ Coll (Rec k τl pf) ] ->
        [ Γ ⊢ NNRSimpGroupBy g sl e ▷ GroupBy_type g sl k τl pf ]
    where
    "[ Γ ⊢ e ▷ τ ]" := (nnrs_imp_expr_type Γ e τ) : nnrs_imp
    .

    Notation "[ Γ  ⊢ e ▷ τ ]" := (nnrs_imp_expr_type Γ e τ) : nnrs_imp.

    (* Observation: all the contexts are stacklike in their domain,
       and there is no reason to allow strong updates, since there is a phase
       distinction between mutating/reading (and we have a join operator on types)
       So we can model the types of all the contexts as stacks, even though the 
       evaluation semantics models them in a more state-like way.
     *)

    Reserved Notation "[  Γ  ⊢ s ]".

    Inductive nnrs_imp_stmt_type :
      pd_tbindings -> nnrs_imp_stmt -> Prop :=
    | type_NNRSimpSkip Γ  :
        [  Γ ⊢ NNRSimpSkip ]
    | type_NNRSimpSeq Γ s₁ s₂ :
        [  Γ ⊢ s₁ ] -> 
        [  Γ   ⊢ s₂ ]  ->
        [  Γ ⊢ NNRSimpSeq s₁ s₂ ]
    | type_NNRSimpLetDef Γ τ x e₁ s₂ :
        [  Γ  ⊢ e₁ ▷ τ ] -> 
        [  (x,τ)::Γ  ⊢ s₂ ]  ->
        [  Γ  ⊢ NNRSimpLet x (Some e₁) s₂ ]
    | type_NNRSimpLetNone Γ τ x s₂ :
        nnrs_imp_stmt_var_usage s₂ x <> VarMayBeUsedWithoutAssignment ->
        [  (x,τ)::Γ  ⊢ s₂ ]  ->
        [  Γ  ⊢ NNRSimpLet x None s₂ ]
    | type_NNRSimpAssign Γ τ x e :
        [ Γ ⊢ e ▷ τ ] ->
        lookup string_dec Γ x = Some τ ->
        [  Γ   ⊢ NNRSimpAssign x e ]
    | type_NNRSimpFor Γ τ x e₁ s₂ :
        [  Γ  ⊢ e₁ ▷ Coll τ ] -> 
        [  (x,τ)::Γ  ⊢ s₂ ]  ->
        [  Γ ⊢ NNRSimpFor x e₁ s₂ ]
    | type_NNRSimpIf Γ e s₁ s₂ :
        [  Γ  ⊢ e ▷ Bool] -> 
        [  Γ   ⊢ s₁ ] -> 
        [  Γ  ⊢ s₂ ]  ->
        [  Γ ⊢ NNRSimpIf e s₁ s₂ ]
    | type_NNRSimpEither Γ τl τr e x₁ s₁ x₂ s₂ :
        [  Γ  ⊢ e ▷ Either τl τr] -> 
        [  (x₁,τl)::Γ  ⊢ s₁ ] -> 
        [  (x₂,τr)::Γ  ⊢ s₂ ]  ->
        [  Γ  ⊢ NNRSimpEither e x₁ s₁ x₂ s₂ ]
    where
    "[ Γ ⊢ s ]" := (nnrs_imp_stmt_type Γ s) : nnrs_imp
    .

    Notation "[ Γ ⊢ s ]" := (nnrs_imp_stmt_type Γ s) : nnrs_imp.
  End typ.

  Notation "[ Γc ; Γ  ⊢ e ▷ τ ]" := (nnrs_imp_expr_type Γc Γ e τ) : nnrs_imp.
  Notation "[ Γc ; Γ  ⊢ s ]" := (nnrs_imp_stmt_type Γc Γ s) : nnrs_imp.

  Hint Immediate type_NNRSimpSkip.
  Local Open Scope nnrs_imp.
  
  Definition nnrs_imp_type Γc (si:nnrs_imp) τ
    := let (s, ret) := si in
       nnrs_imp_stmt_var_usage s ret <> VarMayBeUsedWithoutAssignment 
       /\ [ Γc ; (ret, τ)::nil  ⊢ s ].

  Notation "[ Γc ⊢ si ▷ τ ]" := (nnrs_imp_type Γc si τ) : nnrs_imp.

  Definition nnrs_imp_returns (si:nnrs_imp)
    := nnrs_imp_stmt_var_usage (fst si) (snd si) = VarMustBeAssigned.

  Lemma typed_nnrs_imp_expr_yields_typed_data {σc Γc} {σ Γ} {e τ} :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    has_some_parts (nnrs_imp_expr_free_vars e) σ ->
    [ Γc ; Γ  ⊢ e ▷ τ ] ->
    exists d,
      nnrs_imp_expr_eval brand_relation_brands σc σ e = Some d
      /\ d ▹ τ.
  Proof.
    intros Γctyp Γtyp hasparts etyp.
    dependent induction etyp; simpl in *.
    - unfold tdot in *.
      apply (Forall2_lookupr_some Γctyp H).
    - invcs hasparts.
      destruct (Forall2_lookup_some Γtyp H
                                    (P:=(fun xy1 xy2 => forall d : data, xy1 = Some d -> d ▹ xy2)))
        as [?[ eqq ?]].
      unfold var in *.
      rewrite eqq in *.
      destruct x; try contradiction.
      unfold id; simpl.
      eauto.
    - eauto.
    - apply Forall_app_inv in hasparts; destruct hasparts as [??].
      destruct IHetyp1 as [?[eqq1 ?]]; trivial.
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

  Lemma typed_nnrs_imp_expr_yields_typed_data_gen {σc Γc} {σ Γ} {e τ} {alreadydefined} :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    has_some_parts alreadydefined σ ->
    [ Γc ; Γ  ⊢ e ▷ τ ] ->
    incl (nnrs_imp_expr_free_vars e) alreadydefined ->
    exists d,
      nnrs_imp_expr_eval brand_relation_brands σc σ e = Some d
      /\ d ▹ τ.
  Proof.
    intros ? pdb hp ? Hinc.
    rewrite <- Hinc in hp.
    eapply typed_nnrs_imp_expr_yields_typed_data; eauto.
  Qed.

  (* Computationally friendly version of this theorem *)
  Theorem typed_nnrs_imp_expr_yields_typed_data_compute {σc Γc} {σ Γ} {e τ} :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    has_some_parts (nnrs_imp_expr_free_vars e) σ ->
    [ Γc ; Γ  ⊢ e ▷ τ ] ->
    {d |
     nnrs_imp_expr_eval brand_relation_brands σc σ e = Some d
     & d ▹ τ}.
  Proof.
    intros Γctyp Γtyp hp etyp.
    generalize (typed_nnrs_imp_expr_yields_typed_data Γctyp Γtyp hp etyp); intros HH.
    destruct (nnrs_imp_expr_eval brand_relation_brands σc σ e).
    - exists d; destruct HH as [?[??]]; simpl; congruence.
    - cut False; [contradiction | ].
      destruct HH as [?[??]]; simpl; congruence.
  Defined.

  
  (* This variant does not ensure progress, but does guarantee type preservation
      and has less hypothesis *)
  Lemma nnrs_imp_expr_eval_preserves_types {σc Γc} {σ Γ} {e τ} :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    [ Γc ; Γ  ⊢ e ▷ τ ] ->
    forall d,
      nnrs_imp_expr_eval brand_relation_brands σc σ e = Some d ->
      d ▹ τ.
  Proof.
    intros Γctyp Γtyp etyp d eqq.
    dependent induction etyp; simpl in *.
    - unfold tdot in *.
      red in Γctyp.
      assert (Γctyp':Forall2
                       (fun (x : string * rtype) (y : string * data) => fst x = fst y /\ (fun x y => data_type y x) (snd x) (snd y))
                       Γc σc).
      {
        apply Forall2_flip in Γctyp.
        simpl in Γctyp.
        revert Γctyp.
        apply Forall2_incl; intuition.
      }
      destruct (Forall2_lookupr_some Γctyp' eqq)
        as [? [eqq1 eqq2]].
      unfold edot in H.
      rewrite eqq1 in H; invcs H.
      trivial.
    - unfold id in eqq.
      apply some_olift in eqq.
      simpl in eqq.
      destruct eqq as [? eqq ?]; subst.
      destruct (Forall2_lookup_some Γtyp H
                                    (P:=(fun xy1 xy2 => forall d : data, xy1 = Some d -> d ▹ xy2)))
        as [?[ eqq1 ?]].
      rewrite eqq1 in eqq; invcs eqq.
      auto.
    - invcs eqq; trivial.
    - apply some_olift2 in eqq.
      destruct eqq as [d1 [d2 d1eq [d2eq beq]]].
      specialize (IHetyp1 Γtyp _ d1eq).
      specialize (IHetyp2 Γtyp _ d2eq).
      destruct (typed_binary_op_yields_typed_data _ _ _ IHetyp1 IHetyp2 H)
        as [? [eqq1 ?]].
      rewrite eqq1 in beq; invcs beq; trivial.
    - apply some_olift in eqq.
      destruct eqq as [d1 d1eq oeq].
      specialize (IHetyp Γtyp _ d1eq).
      destruct (typed_unary_op_yields_typed_data _ _ IHetyp H)
        as [? [eqq1 ?]].
      rewrite eqq1 in oeq; invcs oeq; trivial.
    - match_option_in eqq.
      specialize (IHetyp Γtyp _ eqq0).
      dtype_inverter.
      destruct (typed_group_by_nested_eval_table_yields_typed_data IHetyp g sl H)
        as [? [eqq1 ?]].
      rewrite eqq1 in eqq; invcs eqq; trivial.
  Qed.

  Lemma typed_nnrs_imp_expr_vars_in_ctxt {Γc Γ} {e:nnrs_imp_expr} {τ} :
    [Γc; Γ ⊢ e ▷ τ] ->
    forall x, nnrs_imp_expr_may_use e x = true -> In x (domain Γ).
  Proof.
    intros typexpr; dependent induction typexpr; simpl; intros ? eqq; try discriminate.
    - unfold equiv_decb in eqq.
      match_destr_in eqq; red in e; subst.
      apply lookup_in_domain in H; trivial.
    - apply orb_prop in eqq; intuition.
    - intuition.
    - intuition.
  Qed.
  
  Lemma typed_nnrs_imp_stmt_vars_in_ctxt {Γc Γ} {s:nnrs_imp_stmt} :
    [  Γc ; Γ  ⊢ s ] ->
    (forall x, nnrs_imp_stmt_var_usage s x <> VarNotUsedAndNotAssigned -> In x (domain Γ)).
  Proof.
    intros typs.
    dependent induction typs; simpl; intros v neq; unfold equiv_decb, var in *.
    - congruence.
    - specialize (IHtyps1 v)
      ; specialize (IHtyps2 v)
      ; match_destr_in neq
      ; tauto.
    - match_case_in neq; intros eqq; rewrite eqq in neq.
      + eapply typed_nnrs_imp_expr_vars_in_ctxt; eauto.
      + destruct (x == v); [congruence | ].
        specialize (IHtyps _ neq).
        unfold equiv, complement in *.
        simpl in IHtyps; tauto.
    - destruct (x == v); [congruence | ].
      specialize (IHtyps _ neq).
      unfold equiv, complement in *.
      simpl in IHtyps; tauto.
    - match_case_in neq; intros eqq; rewrite eqq in neq.
      + eapply typed_nnrs_imp_expr_vars_in_ctxt; eauto.
      + destruct (x == v); [| congruence].
        red in e0; subst.
        apply lookup_in_domain in H0; trivial.
    - case_eq (nnrs_imp_expr_may_use e₁ v); intros eqq1; rewrite eqq1 in neq.
      + eapply typed_nnrs_imp_expr_vars_in_ctxt; eauto.
      + destruct (x == v); [congruence | ].
        match_case_in neq; intros eqq2; rewrite eqq2 in neq.
        * congruence.
        * specialize (IHtyps v).
          unfold equiv, complement in *.
          rewrite eqq2 in IHtyps.
          simpl in IHtyps.
          intuition.
        * congruence.
    - case_eq (nnrs_imp_expr_may_use e v); intros eqq1; rewrite eqq1 in neq.
      + eapply typed_nnrs_imp_expr_vars_in_ctxt; eauto.
      + { match_case_in neq; intros eqq2; rewrite eqq2 in neq.
          - match_case_in neq; intros eqq3; rewrite eqq3 in neq
            ; eapply IHtyps1; congruence.
          - eapply IHtyps1; congruence.
          - match_case_in neq; intros eqq3; rewrite eqq3 in neq; try congruence.
            eapply IHtyps2; congruence.
        }
    - case_eq (nnrs_imp_expr_may_use e v); intros eqq1; rewrite eqq1 in neq.
      + eapply typed_nnrs_imp_expr_vars_in_ctxt; eauto.
      + { destruct (x₁ == v).
          + destruct (x₂ == v); [congruence | ].
            specialize (IHtyps2 v); simpl in IHtyps2.
            unfold equiv, complement in *.
            match_destr_in neq; intuition congruence.
          + specialize (IHtyps1 v); simpl in IHtyps1.
            unfold equiv, complement in *.
            match_destr_in neq.
            * destruct (x₂ == v); [congruence | ].
              match_destr_in neq; intuition congruence.
            * intuition congruence.
            * destruct (x₂ == v); [congruence | ].
              specialize (IHtyps2 v); simpl in IHtyps2.
              unfold equiv, complement in *.
              match_destr_in neq; intuition congruence.
        } 
  Qed.

  Lemma nnrs_imp_stmt_env_preserves_some {s σc σ σ' } :
    nnrs_imp_stmt_eval brand_relation_brands σc s σ =
    Some σ' ->
    Forall2 (preserves_Some snd) σ σ'.
  Proof.
    revert σ σ'.
    induction s; simpl; intros σ σ' eqq1; simpl.
    - invcs eqq1; reflexivity.
    - apply some_olift in eqq1.
      destruct eqq1 as [? eqq1 eqq2].
      specialize (IHs1 _ _ eqq1).
      specialize (IHs2 _ _ (symmetry eqq2)).
      etransitivity; eauto.
    - repeat match_option_in eqq1.
      invcs eqq1.
      apply Forall2_preserves_Some_snd_update_first.
    - match_option_in eqq1; subst.
      + apply some_olift in eqq1.
        destruct eqq1 as [? eqq1 eqq2].
        apply some_lift in eqq1.
        destruct eqq1 as [? eqq1 ?]; subst.
        match_option_in eqq2.
        destruct p; try discriminate.
        invcs eqq2.
        specialize (IHs _ _ eqq).
        invcs IHs; trivial.
      + match_option_in eqq1.
        destruct p; try discriminate.
        invcs eqq1.
        specialize (IHs _ _ eqq).
        invcs IHs; trivial.
    - match_option_in eqq1.
      destruct d; try discriminate.
      clear eqq.
      revert σ σ' eqq1.
      induction l; intros σ σ' eqq1.
      + invcs eqq1; reflexivity.
      + match_option_in eqq1.
        destruct p; try discriminate.
        specialize (IHs _ _ eqq).
        specialize (IHl _ _  eqq1).
        invcs IHs.
        etransitivity; eauto.
    - match_option_in eqq1.
      destruct d; try discriminate.
      clear eqq.
      destruct b; eauto.
    - match_option_in eqq1.
      destruct d; try discriminate
      ; clear eqq
      ; match_option_in eqq1
      ; destruct p; simpl in *; try discriminate
      ; invcs eqq1.
      + specialize (IHs1 _ _ eqq).
        invcs IHs1; trivial.
      + specialize (IHs2 _ _ eqq).
        invcs IHs2; trivial.
  Qed.
  
  Lemma nnrs_imp_stmt_preserves_has_some_parts_skip alreadydefined σc s σ₁ σ₂ σ₁' σ₂' :
    nnrs_imp_stmt_eval brand_relation_brands σc s (σ₁++σ₂) = Some (σ₁'++σ₂') ->
    domain σ₁ = domain σ₁' ->
    has_some_parts alreadydefined σ₂ ->
    has_some_parts alreadydefined σ₂'.
  Proof.
    intros evals sd hp.
    generalize (nnrs_imp_stmt_eval_domain_stack evals); intros domeqs.
    assert (sd2:domain σ₂ = domain σ₂').
    {
      repeat rewrite domain_app in domeqs.
      rewrite sd in domeqs.
      apply app_inv_head in domeqs; trivial.
    }
    apply nnrs_imp_stmt_env_preserves_some in evals.
    unfold has_some_parts in *.
    rewrite Forall_forall in *.
    intros x inn.
    specialize (hp _ inn).
    match_option.
    destruct o; trivial.
    - assert (Forall2 (fun d r => fst d = fst r /\ preserves_Some id (snd d) (snd r)) σ₂ σ₂').
      {
        apply Forall2_eq in sd2.
        generalize (Forall2_map_b _ _ _ _ _ sd2); intros F2.
        destruct (Forall2_app_inv evals) as [evals1 evals2].
        { generalize (f_equal (@length var) sd).
          repeat rewrite domain_length; trivial.
        }
        generalize (Forall2_conj F2 evals2).
        apply Forall2_incl.
        unfold preserves_Some, id; trivial.
      }
      destruct (Forall2_lookup_some H eqq) as [? [inn2 pres]].
      rewrite inn2 in hp.
      destruct x0; try contradiction.
      unfold preserves_Some, id in pres.
      destruct (pres _ (eq_refl _)); discriminate.
  Qed.

  Lemma nnrs_imp_stmt_preserves_has_some_parts alreadydefined σc s σ σ' :
    nnrs_imp_stmt_eval brand_relation_brands σc s σ = Some σ' ->
    has_some_parts alreadydefined σ ->
    has_some_parts alreadydefined σ'.
  Proof.
    intros evals hp.
    eapply (nnrs_imp_stmt_preserves_has_some_parts_skip _ _ _ nil _ nil); simpl; eauto.
  Qed.

  Lemma has_some_parts_cons_some {A B} {dec:EqDec A eq} alreadydefined (σ:list (A*option B)) v x :
    has_some_parts alreadydefined σ ->
    has_some_parts (v :: alreadydefined) ((v, Some x) :: σ).
  Proof.
    intros.
    constructor.
    - simpl.
      destruct (v == v); [ | congruence].
      trivial.
    - revert H.
      apply Forall_impl; simpl; intros a inn.
      destruct (a == v); trivial.
  Qed.
  
  Lemma has_some_parts_cons_none {A B} {dec:EqDec A eq} alreadydefined (σ:list (A*option B)) v :
    has_some_parts alreadydefined σ ->
    has_some_parts (remove equiv_dec v alreadydefined) ((v, None) :: σ).
  Proof.
    unfold has_some_parts.
    repeat rewrite Forall_forall.
    intros F x inn.
    apply remove_inv in inn.
    destruct inn as [inn neq].
    simpl.
    destruct (x == v); try congruence.
    apply F; trivial.
  Qed.
  

  Lemma nnrs_imp_stmt_assigns_has_some_parts {σc s σ σ'} :
    nnrs_imp_stmt_eval brand_relation_brands σc s σ = Some σ' ->
    forall ll,
      has_some_parts (filter (fun x => nnrs_imp_stmt_var_usage s x ==b VarMustBeAssigned)
                             ll) σ' .
  Proof.
    intros eqq1 ll.
    unfold has_some_parts.
    rewrite Forall_forall.
    intros x inn.
    apply filter_In in inn.
    destruct inn as [_ eqq2].
    unfold equiv_decb, equiv_dec in eqq2.
    match_destr_in eqq2.
    destruct (nnrs_imp_stmt_eval_must_assign_assigns eqq1 _ e)
      as [? inn].
    unfold var in *.
    rewrite inn; trivial.
  Qed.

  Theorem typed_nnrs_imp_stmt_yields_typed_data {σc σ} {Γc Γ} {alreadydefined} (s:nnrs_imp_stmt) :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    has_some_parts alreadydefined σ ->
    (forall x, nnrs_imp_stmt_var_usage s x = VarMayBeUsedWithoutAssignment ->
               In x alreadydefined) ->
    [  Γc ; Γ  ⊢ s ] ->
    exists σ',
      (nnrs_imp_stmt_eval brand_relation_brands σc s σ) = Some σ'
      /\ pd_bindings_type σ' Γ
      /\ has_some_parts (alreadydefined
                           ++
                           (filter (fun x => nnrs_imp_stmt_var_usage s x ==b VarMustBeAssigned))
                           (domain Γ))
                        σ'.
  Proof.
    intros typσc typσ hasparts enoughdefined typs.
    revert alreadydefined σ typσ hasparts enoughdefined.
    dependent induction typs; simpl; intros alreadydefined σ typσ hasparts enoughdefined.
    - rewrite false_filter_nil.
      + rewrite app_nil_r; eauto.
      + intuition.
    - specialize (IHtyps1 _ _ typσ hasparts).
      cut_to IHtyps1; [ | intros ? eqq1; apply enoughdefined; rewrite eqq1; trivial].
      destruct IHtyps1 as [σ' [eqq1 [typσ' hasparts']]].
      unfold var in *; rewrite eqq1; simpl.
      specialize (IHtyps2 _ _ typσ' hasparts').
      cut_to IHtyps2.
      + destruct IHtyps2 as [σ'' [eqq2 [typσ'' hasparts'']]].
        rewrite eqq2.
        eexists; split; try reflexivity.
        split; trivial.
        unfold has_some_parts in *.
        repeat rewrite Forall_forall in *.
        intros x inn.
        specialize (hasparts'' x).
        repeat rewrite in_app_iff in *.
        destruct inn as [inn|inn]; [tauto | ].
        repeat rewrite filter_In in *.
        match_destr.
        destruct o; trivial.
        intuition.
        destruct (nnrs_imp_stmt_var_usage s₁ x); congruence.
      + intros.
        rewrite in_app_iff, filter_In.
        specialize (enoughdefined x).
        generalize (typed_nnrs_imp_stmt_vars_in_ctxt typs2 x); intros. 
        match_destr_in enoughdefined
        ; intuition congruence.
    - destruct (typed_nnrs_imp_expr_yields_typed_data_gen typσc typσ hasparts H)
        as [d [eqq typd]].
      { intros v inn.
        apply enoughdefined.
        apply nnrs_imp_expr_may_use_free_vars in inn.
        rewrite inn; trivial.
      } 
      rewrite eqq; simpl.
      assert (typσcons:pd_bindings_type ((x,Some d)::σ) ((x, τ) :: Γ)).
      { unfold pd_bindings_type in *; simpl; constructor; simpl; trivial.
        split; trivial. intros ? eqqq; invcs eqqq; eauto. }
      assert (haspartscons:has_some_parts (alreadydefined++[x]) (((x,Some d)::σ))).
      { apply Forall_app; unfold has_some_parts in *; rewrite Forall_forall in *.
        - simpl; intros ? ?.
          destruct (equiv_dec x0 x); trivial.
          apply hasparts; trivial.
        - simpl; intros ? [?|?]; try contradiction.
          destruct (equiv_dec x0 x); trivial.
          congruence.
      }
      destruct (IHtyps _ _ typσcons haspartscons)
        as [σ' [eqq1 [typσ' hasparts']]].
      {
        intros y eqqy.
        specialize (enoughdefined y).
        rewrite eqqy in enoughdefined.
        rewrite in_app_iff; simpl.
        match_destr_in enoughdefined; eauto.
        unfold equiv_decb, var in enoughdefined.
        destruct (x == y); eauto.
      }
      unfold var in *; rewrite eqq1.
      invcs typσ'; simpl in *.
      destruct H3; subst.
      destruct x0; simpl in *.
      eexists; split; try reflexivity.
      split; trivial.
      generalize (nnrs_imp_stmt_preserves_has_some_parts_skip alreadydefined
                                                              σc s₂ ((s, Some d)::nil) σ ((s, o) :: nil) l)
      ; simpl; intros pres.
      specialize (pres eqq1 (eq_refl _) hasparts).
      apply Forall_app; unfold has_some_parts in *; trivial.
      rewrite Forall_forall in *.
      intros x inn; unfold var in *.
      specialize (hasparts' x); simpl in hasparts'.
      apply filter_In in inn.
      destruct inn as [inn eqq2].
      destruct (nnrs_imp_expr_may_use e₁ x); try discriminate.
      unfold equiv_decb in *.
      destruct (s == x); try discriminate.
      match_destr_in eqq2; try discriminate.
      cut_to hasparts'.
      + destruct (x == s); try congruence.
      + apply in_app_iff; right.
        match_destr; simpl; [right | ]
        ; apply filter_In; rewrite e; eauto.
    - assert (typσcons:pd_bindings_type ((x,None)::σ) ((x, τ) :: Γ)).
      { unfold pd_bindings_type in *; simpl; constructor; simpl; trivial.
        split; trivial. intros ? eqqq; invcs eqqq; eauto. }
      assert (haspartscons:has_some_parts (remove equiv_dec x alreadydefined) (((x,None)::σ))).
      { unfold has_some_parts in *; rewrite Forall_forall in *.
        simpl; intros ? inn.
        apply remove_inv in inn.
        destruct inn as [inn neq].
        specialize (hasparts _ inn).
        destruct (equiv_dec x0 x); trivial.
        congruence.
      } 
      destruct (IHtyps _ _ typσcons haspartscons)
        as [σ' [eqq1 [typσ' hasparts']]].
      {
        intros y eqqy.
        apply remove_in_neq; [ congruence | ].
        specialize (enoughdefined y).
        rewrite eqqy in enoughdefined.
        unfold equiv_decb, var in *.
        destruct (x == y); eauto 3.
        congruence.
      }
      unfold var in *; rewrite eqq1.
      invcs typσ'; simpl in *.
      destruct H3; subst.
      destruct x0; simpl in *.
      eexists; split; try reflexivity.
      split; trivial.
      generalize (nnrs_imp_stmt_preserves_has_some_parts_skip alreadydefined
                                                              σc s₂ ((s, None)::nil) σ ((s, o) :: nil) l)
      ; simpl; intros pres.
      specialize (pres eqq1 (eq_refl _) hasparts).
      apply Forall_app; unfold has_some_parts in *; trivial.
      rewrite Forall_forall in *.
      intros x inn; unfold var in *.
      specialize (hasparts' x); simpl in hasparts'.
      apply filter_In in inn.
      destruct inn as [inn eqq2].
      rewrite in_app_iff in hasparts'.
      unfold equiv_decb in *.
      destruct (s == x); try discriminate.
      match_destr_in eqq2; try discriminate.
      destruct (x == s); try congruence.
      apply hasparts'.
      right.
      match_destr; simpl; [right | ]
      ; apply filter_In; rewrite e; eauto.
    - destruct (typed_nnrs_imp_expr_yields_typed_data_gen typσc typσ hasparts H)
        as [d [eqq typd]].
      { intros v inn.
        apply enoughdefined.
        apply nnrs_imp_expr_may_use_free_vars in inn.
        rewrite inn; trivial.
      } 
      rewrite eqq; simpl.
      destruct (Forall2_lookup_some typσ H0
                                    (P:=(fun xy1 xy2 => forall d : data, xy1 = Some d -> d ▹ xy2)))
        as [?[ eqq2 ?]].
      rewrite eqq2.
      eexists; split; try reflexivity.
      split.
      + clear H.
        revert H0 H1 typd.
        revert typσ.
        clear; intros typσ.
        induction typσ; simpl; [constructor | ]; intros.
        destruct H; destruct y; destruct x1; simpl in *; subst.
        destruct (string_dec x s).
        * invcs H0.
          constructor; trivial; simpl.
          split; trivial.
          intros ? eqq3; invcs eqq3; trivial.
        * constructor; simpl; eauto.
          apply IHtypσ; eauto.
      + unfold has_some_parts in *; rewrite Forall_forall in *; intros ? inn.
        rewrite in_app_iff in inn.
        string_dec_to_equiv.
        destruct (x == x1).
        * unfold equiv in *; subst.
          rewrite lookup_update_eq_in; trivial.
          eapply lookup_in_domain; eauto.
        * rewrite lookup_update_neq; trivial.
          { destruct inn as [inn | inn].
            - apply hasparts; trivial.
            - apply filter_In in inn.
              destruct inn as [inn eqq1].
              match_destr_in eqq1.
              unfold equiv_decb, var in *.
              destruct (x == x1); [ congruence | ].
              discriminate.
          } 
    - destruct (typed_nnrs_imp_expr_yields_typed_data_gen typσc typσ hasparts H)
        as [d [eqq typd]].
      { intros v inn.
        apply enoughdefined.
        apply nnrs_imp_expr_may_use_free_vars in inn.
        rewrite inn; trivial.
      } 
      rewrite eqq; simpl.
      clear H eqq.
      invcs typd; rtype_equalizer; subst.
      revert σ typσ hasparts.
      induction dl; intros σ typσ hasparts.
      + eexists; split; try reflexivity.
        split; trivial.
        unfold has_some_parts, var in *.
        repeat rewrite Forall_forall in *.
        intros y inn.
        rewrite in_app_iff in inn.
        specialize (enoughdefined y).
        specialize (hasparts y).
        destruct inn as [inn | inn].
        * apply hasparts; trivial.
        * apply filter_In in inn.
          destruct inn as [inn neq].
          match_destr_in neq.
          unfold equiv_decb in *.
          destruct (x == y); try discriminate.
          destruct (nnrs_imp_stmt_var_usage s₂ y); try discriminate.
      + invcs H1.
        assert (typσcons:pd_bindings_type ((x, Some a)::σ) ((x, τ) :: Γ)).
        { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto.
          intros ? eqqq; invcs eqqq; trivial.
        }
        assert (haspartscons:has_some_parts (alreadydefined++[x]) (((x,Some a)::σ))).
        { apply Forall_app; unfold has_some_parts in *; rewrite Forall_forall in *.
          - simpl; intros ? ?.
            destruct (equiv_dec x0 x); trivial.
            apply hasparts; trivial.
          - simpl; intros ? [?|?]; try contradiction.
            destruct (equiv_dec x0 x); trivial.
            congruence.
        }
        destruct (IHtyps _ _ typσcons haspartscons)
          as [σ' [eqq1 [typσ' hasparts']]].
        {
          intros ? eqq.
          apply in_app_iff; simpl.
          specialize (enoughdefined x0).
          unfold equiv_decb, var in *.
          destruct (x == x0); unfold equiv in *; subst; eauto.
          left.
          apply enoughdefined.
          rewrite eqq.
          match_destr.
        }
        unfold var in *; rewrite eqq1.
        invcs typσ'.
        destruct x0; destruct H4; simpl in *; subst.
        generalize (nnrs_imp_stmt_preserves_has_some_parts_skip alreadydefined
                                                                σc s₂ ((x, Some a)::nil) σ ((x, o) :: nil) l)
        ; simpl; intros pres.
        specialize (pres eqq1 (eq_refl _) hasparts).
        
        specialize (IHdl H3 _ H5 pres).
        destruct IHdl as [σ' [eqq2 [pd2 hp2]]].
        rewrite eqq2.
        eexists; split; try reflexivity.
        split; trivial.
    - destruct (typed_nnrs_imp_expr_yields_typed_data_gen typσc typσ hasparts H)
        as [d [eqq typd]].
      { intros v inn.
        apply enoughdefined.
        apply nnrs_imp_expr_may_use_free_vars in inn.
        rewrite inn; trivial.
      } 
      rewrite eqq; simpl.
      clear H eqq.
      invcs typd.
      destruct b.
      + destruct (IHtyps1 _ _ typσ hasparts)
          as [σ' [eqq1 [typσ' hasparts']]].
        { intros y inn.
          specialize (enoughdefined y).
          match_destr_in enoughdefined; eauto.
          rewrite inn in enoughdefined.
          eauto.
        } 
        rewrite eqq1.
        eexists; split; try reflexivity.
        split; trivial.
        unfold has_some_parts in *; rewrite Forall_forall in *; intros ? inn.
        specialize (hasparts' x).
        repeat rewrite in_app_iff in *.
        apply hasparts'.
        destruct inn as [inn | inn]; [ eauto | ].
        apply filter_In in inn.
        destruct inn as [inn neq].
        match_destr_in neq.
        right; apply filter_In.
        split; trivial.
        unfold equiv_decb, var in *.
        destruct (nnrs_imp_stmt_var_usage s₁ x); simpl; trivial
        ; destruct (nnrs_imp_stmt_var_usage s₂ x); simpl; trivial.
      + destruct (IHtyps2 _ _ typσ hasparts)
          as [σ' [eqq1 [typσ' hasparts']]].
        { intros y inn.
          specialize (enoughdefined y).
          match_destr_in enoughdefined; eauto.
          rewrite inn in enoughdefined.
          match_destr_in enoughdefined; eauto.
        } 
        rewrite eqq1.
        eexists; split; try reflexivity.
        split; trivial.
        unfold has_some_parts in *; rewrite Forall_forall in *; intros ? inn.
        specialize (hasparts' x).
        repeat rewrite in_app_iff in *.
        apply hasparts'.
        destruct inn as [inn | inn]; [ eauto | ].
        apply filter_In in inn.
        destruct inn as [inn neq].
        match_destr_in neq.
        right; apply filter_In.
        split; trivial.
        unfold equiv_decb, var in *.
        destruct (nnrs_imp_stmt_var_usage s₁ x); simpl; trivial
        ; destruct (nnrs_imp_stmt_var_usage s₂ x); simpl; trivial.
    - destruct (typed_nnrs_imp_expr_yields_typed_data_gen typσc typσ hasparts H)
        as [d [eqq typd]].
      { intros v inn.
        apply enoughdefined.
        apply nnrs_imp_expr_may_use_free_vars in inn.
        rewrite inn; trivial.
      } 
      rewrite eqq; simpl.
      clear H eqq.
      invcs typd; rtype_equalizer; subst.
      + assert (typσcons:pd_bindings_type ((x₁, Some d0)::σ) ((x₁, τl) :: Γ)).
        { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto.
          intros ? eqqq; invcs eqqq; trivial.
        }
        assert (haspartscons:has_some_parts (alreadydefined++[x₁]) (((x₁,Some d0)::σ))).
        { apply Forall_app; unfold has_some_parts in *; rewrite Forall_forall in *.
          - simpl; intros ? ?.
            destruct (equiv_dec x x₁); trivial.
            apply hasparts; trivial.
          - simpl; intros ? [?|?]; try contradiction.
            destruct (equiv_dec x x₁); trivial.
            congruence.
        }
        destruct (IHtyps1 _ _ typσcons haspartscons)
          as [σ' [eqq1 [typσ' hasparts']]].
        {
          intros ? eqq.
          apply in_app_iff; simpl.
          specialize (enoughdefined x).
          unfold equiv_decb, var in *.
          destruct (x₁ == x); unfold equiv in *; subst; eauto.
          left.
          apply enoughdefined.
          rewrite eqq.
          match_destr.
        }
        unfold var in *; rewrite eqq1.
        invcs typσ'.
        destruct x; destruct H3; simpl in *; subst.
        generalize (nnrs_imp_stmt_preserves_has_some_parts_skip alreadydefined
                                                                σc s₁ ((x₁, Some d0)::nil) σ ((x₁, o) :: nil) l)
        ; simpl; intros pres.
        specialize (pres eqq1 (eq_refl _) hasparts).
        eexists; split; try reflexivity.
        split; trivial.
        apply Forall_app; unfold has_some_parts in *; trivial.
        rewrite Forall_forall in *.
        intros x inn; unfold var in *.
        specialize (hasparts' x); simpl in hasparts'.
        apply filter_In in inn.
        destruct inn as [inn eqq2].
        rewrite in_app_iff in hasparts'.
        match_destr_in eqq2; try discriminate.
        unfold equiv_decb, var in *.
        destruct (x₁ == x)
        ; destruct (x₂ == x); try discriminate
        ; case_eq (nnrs_imp_stmt_var_usage s₁ x); intros eqq3; try rewrite eqq3 in *; try discriminate
        ; case_eq (nnrs_imp_stmt_var_usage s₂ x);  intros eqq4; try rewrite eqq4 in *; try discriminate.
        destruct (x == x₁); try congruence.
        apply hasparts'.
        right.
        match_destr; simpl; [right | ]
        ; apply filter_In
        ; rewrite eqq3; simpl; eauto.
      + assert (typσcons:pd_bindings_type ((x₂, Some d0)::σ) ((x₂, τr) :: Γ)).
        { unfold pd_bindings_type in *; simpl; constructor; trivial; simpl; split; auto.
          intros ? eqqq; invcs eqqq; trivial.
        }
        assert (haspartscons:has_some_parts (alreadydefined++[x₂]) (((x₂,Some d0)::σ))).
        { apply Forall_app; unfold has_some_parts in *; rewrite Forall_forall in *.
          - simpl; intros ? ?.
            destruct (equiv_dec x x₂); trivial.
            apply hasparts; trivial.
          - simpl; intros ? [?|?]; try contradiction.
            destruct (equiv_dec x x₂); trivial.
            congruence.
        }
        destruct (IHtyps2 _ _ typσcons haspartscons)
          as [σ' [eqq1 [typσ' hasparts']]].
        {
          intros ? eqq.
          apply in_app_iff; simpl.
          specialize (enoughdefined x).
          unfold equiv_decb, var in *.
          destruct (x₂ == x); unfold equiv in *; subst; eauto.
          left.
          apply enoughdefined.
          rewrite eqq.
          repeat match_destr.
        }
        unfold var in *; rewrite eqq1.
        invcs typσ'.
        destruct x; destruct H3; simpl in *; subst.
        generalize (nnrs_imp_stmt_preserves_has_some_parts_skip alreadydefined
                                                                σc s₂ ((x₂, Some d0)::nil) σ ((x₂, o) :: nil) l)
        ; simpl; intros pres.
        specialize (pres eqq1 (eq_refl _) hasparts).
        eexists; split; try reflexivity.
        split; trivial.
        apply Forall_app; unfold has_some_parts in *; trivial.
        rewrite Forall_forall in *.
        intros x inn; unfold var in *.
        specialize (hasparts' x); simpl in hasparts'.
        apply filter_In in inn.
        destruct inn as [inn eqq2].
        rewrite in_app_iff in hasparts'.
        match_destr_in eqq2; try discriminate.
        unfold equiv_decb, var in *.
        destruct (x₁ == x)
        ; destruct (x₂ == x); try discriminate
        ; case_eq (nnrs_imp_stmt_var_usage s₁ x); intros eqq3; try rewrite eqq3 in *; try discriminate
        ; case_eq (nnrs_imp_stmt_var_usage s₂ x);  intros eqq4; try rewrite eqq4 in *; try discriminate.
        destruct (x == x₂); try congruence.
        apply hasparts'.
        right.
        match_destr; simpl; [right | ]
        ; apply filter_In
        ; rewrite eqq4; simpl; eauto.
  Qed.

  (* This variant does not ensure progress, but does guarantee type preservation
      and has less hypothesis *)
  Theorem nnrs_imp_stmt_eval_preserves_types {σc σ} {Γc Γ} (s:nnrs_imp_stmt) :
    bindings_type σc Γc ->
    pd_bindings_type σ Γ ->
    [  Γc ; Γ  ⊢ s ] ->
    forall σ',
      nnrs_imp_stmt_eval brand_relation_brands σc s σ = Some σ' ->
      pd_bindings_type σ' Γ.
  Proof.
    intros typσc typσ typs.
    revert σ typσ.
    dependent induction typs; simpl; intros σ typσ σ' eqq.
    - invcs eqq; eauto.
    - apply some_olift in eqq.
      destruct eqq as [? eqq1 eqq2].
      specialize (IHtyps1 _ typσ _ eqq1).
      specialize (IHtyps2 _ IHtyps1 _ (symmetry eqq2)).
      trivial.
    - apply some_olift in eqq.
      destruct eqq as [? eqq1 eqq2].
      apply some_lift in eqq1.
      destruct eqq1 as [? eqq1 ?]; subst.
      match_option_in eqq2.
      destruct p; try discriminate.
      invcs eqq2.
      apply IHtyps in eqq.
      + invcs eqq; trivial.
      + constructor; trivial; simpl.
        split; trivial.
        intros ? eqq2; invcs eqq2.
        eapply nnrs_imp_expr_eval_preserves_types; eauto.
    - match_option_in eqq.
      destruct p; try discriminate.
      invcs eqq.
      apply IHtyps in eqq0.
      + invcs eqq0; trivial.
      + constructor; trivial; simpl.
        intuition; discriminate.
    - match_option_in eqq.
      match_option_in eqq.
      invcs eqq.
      eapply nnrs_imp_expr_eval_preserves_types in eqq0; eauto.
      clear H.
      unfold pd_bindings_type in *.
      induction typσ; simpl.
      + constructor.
      + destruct x0.
        destruct y.
        simpl in *.
        destruct H as [??]; simpl in *; subst.
        match_destr; constructor; simpl; eauto.
        invcs eqq1.
        split; trivial.
        intros ? eqq1; invcs eqq1.
        invcs H0; trivial.
    - match_option_in eqq.
      eapply nnrs_imp_expr_eval_preserves_types in eqq0; eauto.
      destruct d; try discriminate.
      invcs eqq0; rtype_equalizer; subst.
      revert σ typσ σ' eqq H2.
      induction l; simpl; intros σ typσ σ' eqq eqq1.
      + invcs eqq; trivial.
      + match_option_in eqq.
        invcs eqq1.
        destruct p; try discriminate.
        apply IHtyps in eqq0.
        * apply IHl in eqq; trivial.
          invcs eqq0; trivial.
        * constructor; simpl; eauto.
          split; trivial; intros ? eqq1; invcs eqq1; trivial.
    - match_option_in eqq.
      eapply nnrs_imp_expr_eval_preserves_types in eqq0; eauto.
      invcs eqq0.
      destruct b; eauto.
    - match_option_in eqq.
      eapply nnrs_imp_expr_eval_preserves_types in eqq0; eauto.
      invcs eqq0; rtype_equalizer; subst
      ; match_option_in eqq
      ; destruct p; try discriminate
      ; invcs eqq.
      + eapply IHtyps1 in eqq0.
        * invcs eqq0; trivial.
        * econstructor; simpl; eauto.
          split; trivial; intros ? eqq1; invcs eqq1; trivial.
      + eapply IHtyps2 in eqq0.
        * invcs eqq0; trivial.
        * econstructor; simpl; eauto.
          split; trivial; intros ? eqq1; invcs eqq1; trivial.
  Qed.


  Lemma typed_nnrs_imp_yields_typed_data_aux {σc} {Γc} {τ} {si:nnrs_imp}:
    bindings_type σc Γc ->
    [ Γc ⊢ si ▷ τ ] ->
    exists o,
      nnrs_imp_eval brand_relation_brands σc si = Some o
      /\ (forall d, o = Some d -> d ▹ τ)
      /\ (nnrs_imp_stmt_var_usage (fst si) (snd si) ==b VarMustBeAssigned = true ->
          exists d, o = Some d).
  Proof.
    destruct si as [q ret]; simpl.
    intros typσc [neq typq].
    destruct (@typed_nnrs_imp_stmt_yields_typed_data
                σc [(ret, None)]
                Γc [(ret, τ)] nil q)
      as [σ' [eqq1 [typσ' eqq]]]
    ; simpl; trivial ; try solve[constructor].
    - constructor; trivial.
      simpl; intuition discriminate.
    - generalize (typed_nnrs_imp_stmt_vars_in_ctxt typq); intros.
      simpl in H.
      specialize (H x).
      cut_to H.
      + destruct H; trivial.
        subst.
        congruence.
      + congruence.
    - rewrite eqq1.
      invcs typσ'.
      destruct x; simpl in *.
      eexists; split; try reflexivity.
      intros; subst; intuition.
      unfold has_some_parts in eqq.
      rewrite H1 in eqq.
      simpl in eqq.
      invcs eqq.
      unfold var in *.
      destruct (equiv_dec ret ret); try congruence.
      destruct o; try contradiction.
      eauto.
  Qed.

  Theorem typed_nnrs_imp_yields_typed_data {σc} {Γc} {τ} {si:nnrs_imp}:
    bindings_type σc Γc ->
    [ Γc ⊢ si ▷ τ ] ->
    exists o,
      nnrs_imp_eval brand_relation_brands σc si = Some o
      /\ forall d, o = Some d -> d ▹ τ.
  Proof.
    intros typσc typq.
    destruct (typed_nnrs_imp_yields_typed_data_aux typσc typq)
      as [? [?[??]]].
    eauto.
  Qed.

  Theorem typed_nnrs_imp_yields_typed_data_used {σc} {Γc} {τ} {si:nnrs_imp}:
    nnrs_imp_returns si ->
    bindings_type σc Γc ->
    [ Γc ⊢ si ▷ τ ] ->
    exists d,
      nnrs_imp_eval brand_relation_brands σc si = Some (Some d)
      /\ d ▹ τ.
  Proof.
    intros ma typσc typq.
    destruct (typed_nnrs_imp_yields_typed_data_aux typσc typq)
      as [? [?[??]]].
    rewrite ma in H1.
    destruct H1; trivial.
    subst; eauto.
  Qed.

  (* This variant does not ensure progress, but does guarantee type preservation
      and has less hypothesis *)
  Theorem nnrs_imp_eval_preserves_types {σc} {Γc τ} (si:nnrs_imp) :
    bindings_type σc Γc ->
    [ Γc ⊢ si ▷ τ ] ->
    forall d,
      nnrs_imp_eval brand_relation_brands σc si = Some (Some d) ->
      d ▹ τ.
  Proof.
    intros bt typ d eqq.
    destruct si as [s ret].
    destruct typ as [ne typ].
    assert (pd:pd_bindings_type [(ret, None)]
                                [(ret, τ)]).
    { constructor; simpl; eauto.
      intuition; discriminate.
    } 
    unfold nnrs_imp_eval in eqq.
    match_option_in eqq.
    repeat (destruct p; try discriminate).
    invcs eqq.
    generalize (nnrs_imp_stmt_eval_preserves_types s bt pd typ _ eqq0); intros pd2.
    invcs pd2; simpl in *.
    intuition eauto.
  Qed.
  
  Theorem typed_nnrs_imp_top_yields_typed_data {σc} {Γc} {τ} {si:nnrs_imp}:
    bindings_type σc Γc ->
    [ rec_sort Γc ⊢ si ▷ τ ] ->
    forall d, 
      nnrs_imp_eval_top brand_relation_brands σc si = Some d
      -> d ▹ τ.
  Proof.
    intros bt typ.
    destruct (typed_nnrs_imp_yields_typed_data (bindings_type_sort _ _ bt) typ)
      as [o [eqq dtyp]].
    unfold nnrs_imp_eval_top.
    rewrite eqq; unfold id; simpl; tauto.
  Qed.

  Theorem typed_nnrs_imp_top_yields_typed_data_used {σc} {Γc} {τ} {si:nnrs_imp}:
    nnrs_imp_returns si ->
    bindings_type σc Γc ->
    [ rec_sort Γc ⊢ si ▷ τ ] ->
    exists d,
      nnrs_imp_eval_top brand_relation_brands σc si = Some d
      /\ d ▹ τ.
  Proof.
    intros ma bt typ.
    destruct (typed_nnrs_imp_yields_typed_data_used ma (bindings_type_sort _ _ bt) typ) as [o [eqq dtyp]].
    unfold nnrs_imp_eval_top.
    rewrite eqq; unfold id; simpl.
    eauto.
  Qed.

  Theorem nnrs_imp_top_eval_preserves_types {σc} {Γc τ} (si:nnrs_imp) :
    bindings_type σc Γc ->
    [ rec_sort Γc ⊢ si ▷ τ ] ->
    forall d,
      nnrs_imp_eval_top brand_relation_brands σc si = Some d ->
      d ▹ τ.
  Proof.
    unfold nnrs_imp_eval_top, id.
    intros bt typ d eqq.
    apply some_olift in eqq.
    destruct eqq as [? eqq1 ?]; subst.
    eapply nnrs_imp_eval_preserves_types in eqq1; eauto.
    apply bindings_type_sort; trivial.
  Qed.

  Section sem.
    (* restates type soundness theorems in terms of the semantics.  
       This enables nicer notation :-) *)

    Theorem typed_nnrs_imp_yields_typed_data_sem {σc} {Γc} {τ} {si:nnrs_imp}:
      bindings_type σc Γc ->
      [ Γc ⊢ si ▷ τ ] ->
      exists o,
        [ brand_relation_brands , σc ⊢ si ⇓ o  ]
        /\ forall d, o = Some d -> d ▹ τ.
    Proof.
      intros typΓc typsi.
      destruct (typed_nnrs_imp_yields_typed_data typΓc typsi)
        as [o [ev F]].
      apply nnrs_imp_sem_eval in ev.
      eauto.
    Qed.

    Theorem typed_nnrs_imp_yields_typed_data_used_sem {σc} {Γc} {τ} {si:nnrs_imp}:
      nnrs_imp_returns si ->
      bindings_type σc Γc ->
      [ Γc ⊢ si ▷ τ ] ->
      exists d,
        [ brand_relation_brands , σc ⊢ si ⇓ Some d  ]
        /\ d ▹ τ.
    Proof.
      intros ma typΓc typsi.
      destruct (typed_nnrs_imp_yields_typed_data_used ma typΓc typsi)
        as [o [ev F]].
      apply nnrs_imp_sem_eval in ev.
      eauto.
    Qed.

  End sem.
  
  (* we are only sensitive to the environment up to lookup *)
  Global Instance nnrs_imp_expr_type_lookup_equiv_prop {m:basic_model} :
    Proper (eq ==> lookup_equiv ==> eq ==> eq ==> iff) nnrs_imp_expr_type.
  Proof.
    cut (Proper (eq ==> lookup_equiv ==> eq ==> eq ==> impl) nnrs_imp_expr_type);
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

  Global Instance nnrs_imp_stmt_type_lookup_equiv_prop :
    Proper (eq ==> lookup_equiv  ==> eq ==> iff) nnrs_imp_stmt_type.
  Proof.
    Hint Constructors nnrs_imp_stmt_type.
    
    cut (Proper (eq ==> lookup_equiv ==> eq ==> impl) nnrs_imp_stmt_type)
    ; unfold Proper, respectful, iff, impl; intros; subst;
      [unfold lookup_equiv in *; intuition; eauto | ].
    rename x0 into Γ₁.
    rename y0 into Γ₂.
    rename y1 into s.
    rename H0 into Γeqq.
    rename H2 into typ.
    revert Γ₁ Γ₂ Γeqq typ.
    induction s; simpl; intros Γ₁ Γ₂ Γeqq typ
    ; trivial
    ; invcs typ
    ; try solve [
            econstructor; trivial
            ; [try solve [rewrite <- Γeqq; eauto] | .. ]
            ; first [eapply IHs | eapply IHs1 | eapply IHs2]
            ; eauto; unfold lookup_equiv; simpl; intros; match_destr
          ].
    econstructor; eauto
    ; rewrite <- Γeqq; eauto.
  Qed.

  Lemma nnrs_imp_expr_type_lookup_equiv_on {Γc Γ₁ e τ} :
    [ Γc ; Γ₁  ⊢ e ▷ τ ] ->
    forall Γ₂,
      lookup_equiv_on (nnrs_imp_expr_free_vars e) Γ₁ Γ₂ ->
      [ Γc ; Γ₂  ⊢ e ▷ τ ].
  Proof.
    revert Γ₁ τ.
    induction e; intros Γ₁ τ typ Γ₂ leo
    ; invcs typ; simpl in *; subst; econstructor; eauto 3.
    - rewrite <- leo; simpl; tauto.
    - eapply IHe1; eauto.
      unfold lookup_equiv_on in *; intuition.
    - eapply IHe2; eauto.
      unfold lookup_equiv_on in *; intuition.
  Qed.
  
  Lemma nnrs_imp_stmt_type_lookup_equiv_on {Γc Γ₁ s} :
    [ Γc ; Γ₁  ⊢ s ] ->
    forall Γ₂,
      lookup_equiv_on (nnrs_imp_stmt_free_vars s) Γ₁ Γ₂ ->
      [ Γc ; Γ₂  ⊢ s ].
  Proof.
    revert Γ₁.
    nnrs_imp_stmt_cases (induction s) Case
    ; simpl
    ; intros Γ₁ typ Γ₂ leo
    ; invcs typ.
    - Case "NNRSimpSkip"%string.
      trivial.
    - Case "NNRSimpSeq"%string.
      apply lookup_equiv_on_dom_app in leo.
      econstructor; intuition eauto.
    - Case "NNRSimpAssign"%string.
      econstructor; eauto.
      + eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
        eapply lookup_equiv_on_dom_incl; eauto.
        unfold incl; simpl; tauto.
      + rewrite <- leo; simpl; tauto.
    - Case "NNRSimpLet"%string.
      apply lookup_equiv_on_dom_app in leo.
      econstructor; intuition eauto.
      + eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      + eapply IHs; eauto.
        unfold lookup_equiv_on in *; simpl; intros.
        match_destr.
        apply H0.
        apply remove_in_neq; tauto.
    - Case "NNRSimpLet"%string.
      simpl in leo.
      econstructor; intuition eauto.
      eapply IHs; eauto.
      unfold lookup_equiv_on in *; simpl; intros.
      match_destr.
      apply leo.
      apply remove_in_neq; tauto.
    - Case "NNRSimpFor"%string.
      apply lookup_equiv_on_dom_app in leo.
      econstructor; intuition eauto.
      + eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      + eapply IHs; eauto.
        unfold lookup_equiv_on in *; simpl; intros.
        match_destr.
        apply H0.
        apply remove_in_neq; tauto.
    - Case "NNRSimpIf"%string.
      apply lookup_equiv_on_dom_app in leo.
      destruct leo as [leo1 leo2].
      apply lookup_equiv_on_dom_app in leo2.
      destruct leo2 as [leo2 leo3].
      econstructor; eauto.
      eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
    - Case "NNRSimpEither"%string.
      apply lookup_equiv_on_dom_app in leo.
      destruct leo as [leo1 leo2].
      apply lookup_equiv_on_dom_app in leo2.
      destruct leo2 as [leo2 leo3].
      econstructor.
      + eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      + eapply IHs1; eauto.
        unfold lookup_equiv_on in *; simpl; intros.
        match_destr.
        apply leo2.
        apply remove_in_neq; tauto.
      + eapply IHs2; eauto.
        unfold lookup_equiv_on in *; simpl; intros.
        match_destr.
        apply leo3.
        apply remove_in_neq; tauto.
  Qed.

  Lemma nnrs_imp_expr_type_has_free_vars {Γc Γ e τ} :
    [Γc; Γ ⊢ e ▷ τ] ->
    incl (nnrs_imp_expr_free_vars e) (domain Γ).
  Proof.
    intros typ x inn.
    revert τ typ inn.
    induction e; simpl; intros τ typ inn
    ; try contradiction
    ; invcs typ
    ; repeat rewrite in_app_iff in *
    ; intuition eauto.
    - apply lookup_in_domain in H1.
      subst; trivial.
  Qed.

  Lemma nnrs_imp_stmt_type_has_free_vars {Γc Γ s} :
    [Γc; Γ ⊢ s] ->
    incl (nnrs_imp_stmt_free_vars s) (domain Γ).
  Proof.
    intros typ x inn.
    revert Γ typ inn.
    induction s; simpl; intros Γ typ inn
    ; try contradiction
    ; invcs typ
    ; repeat rewrite in_app_iff in *
    ; intuition eauto
    ; try solve [eapply nnrs_imp_expr_type_has_free_vars; eauto]
    ; simpl in *
    ; try contradiction
    ; try solve [apply remove_inv in H
                 ; intuition eauto
                 ; specialize (IHs _ H4)
                 ; simpl in IHs
                 ; intuition].
    - apply lookup_in_domain in H3.
      subst; trivial.
    - apply remove_inv in H0.
      intuition eauto.
      specialize (IHs1 _ H6).
      simpl in IHs1.
      intuition.
    - apply remove_inv in H0.
      intuition eauto.
      specialize (IHs2 _ H7).
      simpl in IHs2.
      intuition.
  Qed.

  Lemma nnrs_imp_expr_type_impl_free_vars_incl (Γc : tbindings) e₁ e₂ τ:
    (forall (Γ : pd_tbindings),
        [Γc; Γ ⊢ e₁ ▷ τ] ->
        [Γc; Γ ⊢ e₂ ▷ τ]) ->
    forall Γ,
      [Γc; Γ ⊢ e₁ ▷ τ] ->
      incl (nnrs_imp_expr_free_vars e₂) (nnrs_imp_expr_free_vars e₁).
  Proof.
    intros.
    specialize (H (cut_down_to Γ (nnrs_imp_expr_free_vars e₁))).
    cut_to H.
    - rewrite (nnrs_imp_expr_type_has_free_vars H).
      apply cut_down_to_incl_to.
    - eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      symmetry.
      apply cut_down_to_lookup_equiv_on.
  Qed. 
  
  Lemma nnrs_imp_stmt_type_impl_free_vars_incl Γc s₁ s₂:
    (forall (Γ : pd_tbindings),
        [Γc; Γ ⊢ s₁] ->
        [Γc; Γ ⊢ s₂]) ->
    forall Γ,
      [Γc; Γ ⊢ s₁] ->
      incl (nnrs_imp_stmt_free_vars s₂) (nnrs_imp_stmt_free_vars s₁).
  Proof.
    intros.
    specialize (H (cut_down_to Γ (nnrs_imp_stmt_free_vars s₁))).
    cut_to H.
    - rewrite (nnrs_imp_stmt_type_has_free_vars H).
      apply cut_down_to_incl_to.
    - eapply nnrs_imp_stmt_type_lookup_equiv_on; eauto.
      symmetry.
      apply cut_down_to_lookup_equiv_on.
  Qed.

  Section swap.

    Lemma nnrs_imp_expr_type_swap Γc l Γ  e v₁ v₂ τ₁ τ₂ τo:
      v₁ <> v₂ ->
      [  Γc ; l++(v₁,τ₁)::(v₂, τ₂)::Γ ⊢  e ▷ τo  ] ->
      [  Γc ; l++(v₂,τ₂)::(v₁, τ₁)::Γ ⊢  e ▷ τo  ].
    Proof.
      intros.
      eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_destr; simpl.
      destruct (string_eqdec x v₁)
      ; destruct (string_eqdec x v₂)
      ; try congruence.
    Qed.

    Lemma nnrs_imp_stmt_type_swap Γc l Γ s v₁ v₂ τ₁ τ₂:
      v₁ <> v₂ ->
      [ Γc ; l++(v₁,τ₁)::(v₂, τ₂)::Γ  ⊢ s ] ->
      [ Γc ; l++(v₂,τ₂)::(v₁, τ₁)::Γ  ⊢ s ].
    Proof.
      intros.
      eapply nnrs_imp_stmt_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_destr; simpl.
      destruct (string_eqdec x v₁)
      ; destruct (string_eqdec x v₂)
      ; try congruence.
    Qed.

  End swap.

  Section unused.

    Lemma nnrs_imp_expr_type_unused_remove Γc l Γ e v τ τo:
      (In v (domain l) \/
       ~ In v (nnrs_imp_expr_free_vars e)) ->
      [  Γc ; l++(v,τ)::Γ ⊢  e ▷ τo  ] ->
      [  Γc ; l++Γ ⊢ e ▷ τo ].
    Proof.
      intros.
      eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_option; simpl.
      apply lookup_none_nin in eqq.
      destruct (string_eqdec x v); unfold equiv, complement in *
      ; subst; intuition.
    Qed.

    Lemma nnrs_imp_stmt_type_unused_remove Γc l Γ s v τ:
      (In v (domain l) \/
       ~ In v (nnrs_imp_stmt_free_vars s)) ->
      [  Γc ; l++(v,τ)::Γ  ⊢ s  ] ->
      [  Γc ; l++Γ ⊢  s ].
    Proof.
      intros.
      eapply nnrs_imp_stmt_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_option; simpl.
      apply lookup_none_nin in eqq.
      destruct (string_eqdec x v); unfold equiv, complement in *
      ; subst; intuition.
    Qed.

    Lemma nnrs_imp_expr_type_unused_add Γc l Γ e v τo:
      (In v (domain l) \/
       ~ In v (nnrs_imp_expr_free_vars e)) ->
      [  Γc ; l++Γ ⊢ e ▷ τo ] ->
      forall τ,
        [  Γc ; l++(v,τ)::Γ ⊢  e ▷ τo  ].
    Proof.
      intros.
      eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_option; simpl.
      apply lookup_none_nin in eqq.
      destruct (string_eqdec x v); unfold equiv, complement in *
      ; subst; intuition.
    Qed.

    Lemma nnrs_imp_stmt_type_unused_add Γc l Γ s v:
      (In v (domain l) \/
       ~ In v (nnrs_imp_stmt_free_vars s)) ->
      [  Γc ; l++Γ ⊢  s ] ->
      forall τ,
        [  Γc ; l++(v,τ)::Γ  ⊢ s  ].
    Proof.
      intros.
      eapply nnrs_imp_stmt_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_option; simpl.
      apply lookup_none_nin in eqq.
      destruct (string_eqdec x v); unfold equiv, complement in *
      ; subst; intuition.
    Qed.

    Lemma nnrs_imp_expr_type_unused_irrelevant Γc l Γ e v τ₁ τo:
      (In v (domain l) \/
       ~ In v (nnrs_imp_expr_free_vars e)) ->
      [  Γc ; l++(v,τ₁)::Γ ⊢  e ▷ τo  ] ->
      forall τ₂,
        [  Γc ; l++(v,τ₂)::Γ ⊢ e ▷ τo ].
    Proof.
      intros.
      eapply nnrs_imp_expr_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_option; simpl.
      apply lookup_none_nin in eqq.
      destruct (string_eqdec x v); unfold equiv, complement in *
      ; subst; intuition.
    Qed.

    Lemma nnrs_imp_stmt_type_unused_irrelevant Γc l Γ s v τ₁ :
      (In v (domain l) \/
       ~ In v (nnrs_imp_stmt_free_vars s)) ->
      [  Γc ; l++(v,τ₁)::Γ ⊢  s  ] ->
      forall τ₂,
        [  Γc ; l++(v,τ₂)::Γ ⊢ s  ].
    Proof.
      intros.
      eapply nnrs_imp_stmt_type_lookup_equiv_on; eauto.
      red; simpl; intros.
      repeat rewrite lookup_app.
      match_option; simpl.
      apply lookup_none_nin in eqq.
      destruct (string_eqdec x v); unfold equiv, complement in *
      ; subst; intuition.
    Qed.
    
    Section update.
      Lemma nnrs_imp_expr_type_update_first_irrelevant Γc l Γ τo e v :
        (In v (domain l) \/
         ~ In v (nnrs_imp_expr_free_vars e)) ->
        [  Γc ; l++ Γ ⊢  e ▷ τo ] ->
        forall τ,
          [  Γc ; l++ update_first equiv_dec Γ v τ ⊢ e ▷ τo ].
      Proof.
        intros inn typ τ.
        case_eq (lookup equiv_dec Γ v).
        - intros ? inn2.
          destruct (in_update_break_first _ inn2 τ)
            as [?[? [? [eqq2 nin]]]]
          ; subst.
          rewrite eqq2.
          rewrite <- app_ass in typ |- *.
          assert ( In v (domain (l ++ x)) \/ ~ In v (nnrs_imp_expr_free_vars e)).
          {
            rewrite domain_app, in_app_iff; tauto.
          } 
          apply nnrs_imp_expr_type_unused_remove in typ; trivial.
          apply nnrs_imp_expr_type_unused_add; trivial.
        - intros nin.
          rewrite nin_update; trivial.
      Qed.
      
      Lemma nnrs_imp_stmt_type_update_first_irrelevant Γc l Γ s v :
        (In v (domain l) \/
         ~ In v (nnrs_imp_stmt_free_vars s)) ->
        [  Γc ; l++ Γ ⊢  s  ] ->
        forall τ,
          [  Γc ; l++ update_first equiv_dec Γ v τ ⊢ s  ].
      Proof.
        intros inn typ τ.
        case_eq (lookup equiv_dec Γ v).
        - intros ? inn2.
          destruct (in_update_break_first _ inn2 τ)
            as [?[? [? [eqq2 nin]]]]
          ; subst.
          rewrite eqq2.
          rewrite <- app_ass in typ |- *.
          assert ( In v (domain (l ++ x)) \/ ~ In v (nnrs_imp_stmt_free_vars s)).
          {
            rewrite domain_app, in_app_iff; tauto.
          } 
          apply nnrs_imp_stmt_type_unused_remove in typ; trivial.
          apply nnrs_imp_stmt_type_unused_add; trivial.
        - intros nin.
          rewrite nin_update; trivial.
      Qed.

    End update.
  End unused.

End TNNRSimp.

Notation "[ Γc ; Γ  ⊢ e ▷ τ ]" := (nnrs_imp_expr_type Γc Γ e τ) : nnrs_imp.
Notation "[ Γc ; Γ ⊢ s ]" := (nnrs_imp_stmt_type Γc Γ s) : nnrs_imp.
Notation "[ Γc ⊢ si ▷ τ ]" := (nnrs_imp_type Γc si τ) : nnrs_imp.
