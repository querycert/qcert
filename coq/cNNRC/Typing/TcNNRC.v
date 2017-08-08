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

Section TcNNRC.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Program.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import BasicSystem.
  Require Import cNNRC.

  (** Typing rules for NNRC *)
  Context {m:basic_model}.
  Section typ.
    Context (τconstants:tbindings).

    Inductive nnrc_type : tbindings -> nnrc -> rtype -> Prop :=
    | TNNRCGetConstant {τout} tenv s :
        tdot τconstants s = Some τout ->
        nnrc_type tenv (NNRCGetConstant s) τout
    | TNNRCVar {τ} tenv v : lookup equiv_dec tenv v = Some τ -> nnrc_type tenv (NNRCVar v) τ
    | TNNRCConst {τ} tenv c : data_type (normalize_data brand_relation_brands c) τ -> nnrc_type tenv (NNRCConst c) τ
    | TNNRCBinop  {τ₁ τ₂ τ} tenv b e1 e2 :
        binOp_type b τ₁ τ₂ τ ->
        nnrc_type tenv e1 τ₁ ->
        nnrc_type tenv e2 τ₂ ->
        nnrc_type tenv (NNRCBinop b e1 e2) τ
    | TNNRCUnop {τ₁ τ} tenv u e1 :
        unaryOp_type u τ₁ τ ->
        nnrc_type tenv e1 τ₁ ->
        nnrc_type tenv (NNRCUnop u e1) τ
    | TNNRCLet {τ₁ τ₂} v tenv e1 e2 :
        nnrc_type tenv e1 τ₁ ->
        nnrc_type ((v,τ₁)::tenv) e2 τ₂ ->
        nnrc_type tenv (NNRCLet v e1 e2) τ₂
    | TNNRCFor {τ₁ τ₂} v tenv e1 e2 :
        nnrc_type tenv e1 (Coll τ₁) ->
        nnrc_type ((v,τ₁)::tenv) e2 τ₂ ->
        nnrc_type tenv (NNRCFor v e1 e2) (Coll τ₂)
    | TNNRCIf {τ} tenv e1 e2 e3 :
        nnrc_type tenv e1 Bool ->
        nnrc_type tenv e2 τ ->
        nnrc_type tenv e3 τ ->
        nnrc_type tenv (NNRCIf e1 e2 e3) τ
    | TNNRCEither {τ τl τr} tenv ed xl el xr er :
        nnrc_type tenv ed (Either τl τr) ->
        nnrc_type ((xl,τl)::tenv) el τ ->
        nnrc_type ((xr,τr)::tenv) er τ ->
        nnrc_type tenv (NNRCEither ed xl el xr er) τ.

  End typ.
  
  (** Main lemma for the type correctness of NNNRC *)

  Lemma rmap_exists0 v (cenv:bindings) (env:bindings) e2 dl x0 :
    match
      rmap (fun d1 : data => nnrc_core_eval brand_relation_brands cenv ((v, d1) :: env) e2)
           dl
    with
    | Some a' => Some (dcoll a')
    | None => None
    end = Some x0 ->
    exists x1, rmap (fun d1 : data => nnrc_core_eval brand_relation_brands cenv ((v, d1) :: env) e2) dl = Some x1 /\ (dcoll x1) = x0.
  Proof.
    elim (rmap (fun d1 : data => nnrc_core_eval brand_relation_brands cenv ((v, d1) :: env) e2) dl); intros.
    exists a; split; try inversion H1. reflexivity.
    congruence.
    congruence.
  Qed.    

  Theorem typed_nnrc_yields_typed_data {τc} {τ} (cenv env:bindings) (tenv:tbindings) (e:nnrc) :
    bindings_type cenv τc ->
    bindings_type env tenv ->
    nnrc_type τc tenv e τ ->
    (exists x, (nnrc_core_eval brand_relation_brands cenv env e) = Some x /\ (data_type x τ)).
  Proof.
    intro Hcenv; intros.
    revert env H.
    dependent induction H0; simpl; intros.
    - unfold tdot in *.
      unfold edot in *.
      destruct (Forall2_lookupr_some _ _ _ _ Hcenv H) as [? [eqq1 eqq2]].
      rewrite eqq1.
      eauto.
    - unfold bindings_type in *.
      dependent induction H0.
      simpl in *; congruence.
      simpl in *.
      destruct x; simpl in *.
      elim H0; clear H0; intros.
      destruct y; simpl in *.
      rewrite H0 in *; clear H0.
      revert H.
      elim (equiv_dec v s0); intros.
      exists d.
      inversion H.
      rewrite H3 in *; clear H3 H a.
      split; [reflexivity|assumption].
      specialize (IHForall2 H); clear H.
      assumption.
    - exists (normalize_data brand_relation_brands c).
      split; [reflexivity|assumption].
    - specialize (IHnnrc_type1 env H0); specialize (IHnnrc_type2 env H0).
      elim IHnnrc_type1; intros; clear IHnnrc_type1;
      elim IHnnrc_type2; intros; clear IHnnrc_type2.
      elim H1; clear H1; intros.
      elim H2; clear H2; intros.
      rewrite H1; rewrite H2.
      simpl; apply (@typed_binop_yields_typed_data _ _ _ _ _ _ _ _ τ₁ τ₂ τ); assumption.
    - specialize (IHnnrc_type env H1).
      elim IHnnrc_type; intros; clear IHnnrc_type.
      elim H2; clear H2; intros.
      rewrite H2; clear H2.
      simpl; apply (@typed_unop_yields_typed_data _ _ _ _ _ _ _ _ τ₁ τ); assumption.
    - destruct (IHnnrc_type1 _ H) as [?[re1 ?]].
      destruct (IHnnrc_type2 ((v,x)::env)) as [?[re2 ?]].
      + apply Forall2_cons; intuition.
      + unfold var in *.
        rewrite re1, re2.
        eauto.
    - specialize (IHnnrc_type1 env H).
      elim IHnnrc_type1; intros; clear IHnnrc_type1.
      elim H0; clear H0; intros.
      rewrite H0; clear H0; simpl.
      dependent induction H1.
      rewrite Forall_forall in *.
      induction dl; simpl in *.
      + exists (dcoll []).
        split; [reflexivity|apply dtcoll; apply Forall_nil].
      + assert (forall x : data, In x dl -> data_type x r)
          by (intros; apply (H0 x0); right; assumption).
        specialize (IHdl H1); clear H1.
        elim IHdl; intros; clear IHdl.
        elim H1; clear H1; intros.
        unfold lift in H1.
        unfold var in *.
        generalize (rmap_exists0 v cenv env e2 dl x0 H1); intros.
        elim H3; clear H3; intros.
        elim H3; clear H3; intros.
        rewrite H3.
        rewrite <- H4 in *; clear H1 H3 H4; simpl.
        specialize (IHnnrc_type2 ((v,a)::env)).
        assert (bindings_type ((v, a) :: env) ((v, τ₁) :: tenv)).
        unfold bindings_type.
        apply Forall2_cons; try assumption.
        simpl; split; try reflexivity.
        assert (r = τ₁) by (apply rtype_fequal; assumption).
        rewrite H1 in *; clear H1 x.
        apply (H0 a); left; reflexivity.
        specialize (IHnnrc_type2 H1); clear H1.
        elim IHnnrc_type2; clear IHnnrc_type2; intros.
        elim H1; clear H1; intros.
        rewrite H1; simpl.
        exists (dcoll (x2::x1)); split; try reflexivity.
        apply dtcoll.
        rewrite Forall_forall; simpl; intros.
        elim H4; clear H4; intros.
        rewrite H4 in *; assumption.
        dependent induction H2.
        rewrite Forall_forall in *.
        assert (r0 = τ₂) by (apply rtype_fequal; assumption).
        rewrite H5 in *; clear H5.
        apply (H1 x4); assumption.
    - specialize (IHnnrc_type1 env H); specialize (IHnnrc_type2 env H); specialize (IHnnrc_type3 env H).
      elim IHnnrc_type1; intros; clear IHnnrc_type1;
      elim IHnnrc_type2; intros; clear IHnnrc_type2;
      elim IHnnrc_type3; intros; clear IHnnrc_type3.
      elim H0; clear H0; intros.
      elim H1; clear H1; intros.
      elim H2; clear H2; intros.
      rewrite H0.
      simpl.
      dependent induction H3.
      destruct b.
      + rewrite H1.
        exists x0; split; [reflexivity|assumption].
      + rewrite H2.
        exists x1; split; [reflexivity|assumption].
    - destruct (IHnnrc_type1 _ H) as [dd [evald typd]].
      apply data_type_Either_inv in typd.
      rewrite evald.
      destruct typd as [[ddl[? typd]]|[ddr[? typd]]]; subst.
      + destruct (IHnnrc_type2 ((xl,ddl)::env));
           unfold bindings_type in *; auto.
      + destruct (IHnnrc_type3 ((xr,ddr)::env));
           unfold bindings_type in *; auto.
  Qed.

  (* we are only sensitive to the environment up to lookup *)
  Global Instance nnrc_type_lookup_equiv_prop {m:basic_model} :
    Proper (eq ==> lookup_equiv ==> eq ==> eq ==> iff) nnrc_type.
  Proof.
    cut (Proper (eq ==> lookup_equiv ==> eq ==> eq ==> impl) nnrc_type);
    unfold Proper, respectful, lookup_equiv, iff, impl; intros; subst;
      [intuition; eauto | ].
    rename y1 into e.
    rename y2 into τ.
    rename x0 into b1.
    rename y0 into b2.
    revert b1 b2 τ H0 H3.
    induction e; simpl; inversion 2; subst; econstructor; eauto 3.
    - rewrite <- H0; trivial.
    - eapply IHe2; try eassumption; intros.
      simpl; match_destr.
    - eapply IHe2; try eassumption; intros.
      simpl; match_destr.
    - eapply IHe2; try eassumption; intros.
      simpl; match_destr.
    - eapply IHe3; try eassumption; intros.
      simpl; match_destr.
  Qed.

End TcNNRC.

Ltac nnrc_inverter := 
  match goal with
    | [H:Coll _ = Coll _ |- _] => inversion H; clear H
    | [H: proj1_sig ?τ₁ = Coll₀ (proj1_sig ?τ₂) |- _] => rewrite (Coll_right_inv τ₁ τ₂) in H; subst
    | [H:  Coll₀ (proj1_sig ?τ₂) = proj1_sig ?τ₁ |- _] => symmetry in H
    (* Note: do not generalize too hastily on unaryOp/binOp constructors *)
    | [H:nnrc_type _ _ (NNRCVar _) _ |- _ ] => inversion H; clear H
    | [H:nnrc_type _ _ (NNRCConst _) _ |- _ ] => inversion H; clear H
    | [H:nnrc_type _ _ (NNRCBinop _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nnrc_type _ _ (NNRCUnop _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nnrc_type _ _ (NNRCLet _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nnrc_type _ _ (NNRCFor _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nnrc_type _ _ (NNRCIf _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nnrc_type _ _ (NNRCEither _ _ _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H: (_,_)  = (_,_) |- _ ] => inversion H; clear H
    | [H: map (fun x2 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x2, proj1_sig (snd x2))) ?x0 = nil |- _] => apply (map_rtype_nil x0) in H; simpl in H; subst
    | [H: (map
             (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                (fst x, proj1_sig (snd x))) _)
          = 
          (map
             (fun x' : string * {τ₀' : rtype₀ | wf_rtype₀ τ₀' = true} =>
                (fst x', proj1_sig (snd x'))) _) |- _ ] =>
      apply map_rtype_fequal in H; trivial
    | [H:Rec _ _ _ = Rec _ _ _ |- _ ] => generalize (Rec_inv H); clear H; intro H; try subst
    | [H: context [(_::nil) = map 
                                (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                   (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
                                                                                         
    | [H: context [map 
                     (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                        (fst x, proj1_sig (snd x))) _ = (_::nil) ] |- _] => apply map_eq_cons in H;
                                                                            destruct H as [? [? [? [??]]]]
    | [H:nnrc_type _ _ _ (snd ?x) |- _ ] => destruct x
    | [H: Coll₀ _ = Coll₀ _ |- _ ] => inversion H; clear H
    | [H: Rec₀ _ _ = Rec₀ _ _ |- _ ] => inversion H; clear H
    | [H:unaryOp_type AColl _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type AFlatten _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ARec _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ADot _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ARecProject _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ARecRemove _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type ALeft _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type ARight _ _ |- _ ] => inversion H; clear H; subst
    | [H:binOp_type AConcat _ _ _ |- _ ] => inversion H; clear H
    | [H:binOp_type AAnd _ _ _ |- _ ] => inversion H; clear H
    | [H:binOp_type AMergeConcat _ _ _ |- _ ] => inversion H; clear H
    | [H:context [@equiv_dec ?a ?b ?c ?d ?v ?v] |- _]
      => destruct (@equiv_dec a b c d v v); [ | congruence]
    | [H:context [string_eqdec ?v ?v] |- _]
      => destruct (string_eqdec v v); [ | congruence]
    | [H:context [string_dec ?v ?v] |- _]
      => destruct (string_dec v v); [ | congruence]
    | [H:context [string_dec ?v ?v] |- _]
      => destruct (string_dec v v); [ | congruence]
    | [|- context [@equiv_dec ?a ?b ?c ?d ?v ?v] ]
      => destruct (@equiv_dec a b c d v v); [ | congruence]
    | [|- context [string_eqdec ?v ?v]]
      => destruct (string_eqdec v v); [ | congruence]
    | [|- context [string_dec ?v ?v]]
      => destruct (string_dec v v); [ | congruence]
    | [|- context [string_dec ?v ?v]]
      => destruct (string_dec v v); [ | congruence]
    | [H:equiv ?v ?v |- _] => clear H
    | [H:?v = ?v |- _] => clear H
    | [H:Some _ = Some _ |- _ ]
      => inversion H; clear H
  end; try rtype_equalizer; try assumption; try subst; simpl in *; try nnrc_inverter.

  Ltac nnrc_input_well_typed :=
  repeat progress
         match goal with
           | [HO:nnrc_type ?Γc ?Γ ?op ?τout,
              HC:bindings_type ?cenv ?Γc,
              HE:bindings_type ?env ?Γ
              |- context [(nnrc_core_eval brand_relation_brands ?cenv ?env ?op)]] =>
             let xout := fresh "dout" in
             let xtype := fresh "τout" in
             let xeval := fresh "eout" in
             destruct (typed_nnrc_yields_typed_data cenv env Γ op HC HE HO)
               as [xout [xeval xtype]]; rewrite xeval in *; simpl
         end.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
