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
  Require Import EquivDec Morphisms.

  Require Import Utils BasicSystem.
  Require Import NNRC.

  Section TNRC.

  (** Typing rules for NNRC *)
  Section typ.

    Context {m:basic_model}.

  Inductive nrc_type : tbindings -> nrc -> rtype -> Prop :=
  | TNRCVar {τ} tenv v : lookup equiv_dec tenv v = Some τ -> nrc_type tenv (NRCVar v) τ
  | TNRCConst {τ} tenv c : data_type (normalize_data brand_relation_brands c) τ -> nrc_type tenv (NRCConst c) τ
  | TNRCBinop  {τ₁ τ₂ τ} tenv b e1 e2 :
      binOp_type b τ₁ τ₂ τ ->
      nrc_type tenv e1 τ₁ ->
      nrc_type tenv e2 τ₂ ->
      nrc_type tenv (NRCBinop b e1 e2) τ
  | TNRCUnop {τ₁ τ} tenv u e1 :
      unaryOp_type u τ₁ τ ->
      nrc_type tenv e1 τ₁ ->
      nrc_type tenv (NRCUnop u e1) τ
  | TNRCLet {τ₁ τ₂} v tenv e1 e2 :
      nrc_type tenv e1 τ₁ ->
      nrc_type ((v,τ₁)::tenv) e2 τ₂ ->
      nrc_type tenv (NRCLet v e1 e2) τ₂
  | TNRCFor {τ₁ τ₂} v tenv e1 e2 :
      nrc_type tenv e1 (Coll τ₁) ->
      nrc_type ((v,τ₁)::tenv) e2 τ₂ ->
      nrc_type tenv (NRCFor v e1 e2) (Coll τ₂)
  | TNRCIf {τ} tenv e1 e2 e3 :
      nrc_type tenv e1 Bool ->
      nrc_type tenv e2 τ ->
      nrc_type tenv e3 τ ->
      nrc_type tenv (NRCIf e1 e2 e3) τ
  | TNRCEither {τ τl τr} tenv ed xl el xr er :
      nrc_type tenv ed (Either τl τr) ->
      nrc_type ((xl,τl)::tenv) el τ ->
      nrc_type ((xr,τr)::tenv) er τ ->
      nrc_type tenv (NRCEither ed xl el xr er) τ.

  End typ.

  (** Main lemma for the type correctness of NNRC *)

  Theorem typed_nrc_yields_typed_data {m:basic_model} {τ} (env:bindings) (tenv:tbindings) (e:nrc) :
    bindings_type env tenv ->
    nrc_type tenv e τ ->
    (exists x, (nrc_eval brand_relation_brands env e) = Some x /\ (data_type x τ)).
  Proof.
    intros.
    revert env H.
    dependent induction H0; simpl; intros.
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
    - specialize (IHnrc_type1 env H0); specialize (IHnrc_type2 env H0).
      elim IHnrc_type1; intros; clear IHnrc_type1;
      elim IHnrc_type2; intros; clear IHnrc_type2.
      elim H1; clear H1; intros.
      elim H2; clear H2; intros.
      rewrite H1; rewrite H2.
      simpl; apply (@typed_binop_yields_typed_data _ _ _ _ _ _ _ _ τ₁ τ₂ τ); assumption.
    - specialize (IHnrc_type env H1).
      elim IHnrc_type; intros; clear IHnrc_type.
      elim H2; clear H2; intros.
      rewrite H2; clear H2.
      simpl; apply (@typed_unop_yields_typed_data _ _ _ _ _ _ _ _ τ₁ τ); assumption.
    - destruct (IHnrc_type1 _ H) as [?[re1 ?]].
      destruct (IHnrc_type2 ((v,x)::env)) as [?[re2 ?]].
      + apply Forall2_cons; intuition.
      + unfold var in *.
        rewrite re1, re2.
        eauto.
    - specialize (IHnrc_type1 env H).
      elim IHnrc_type1; intros; clear IHnrc_type1.
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
        assert (exists x1, rmap (fun d1 : data => nrc_eval brand_relation_brands ((v, d1) :: env) e2) dl = Some x1 /\ (dcoll x1) = x0).
        revert H1.
        elim (rmap (fun d1 : data => nrc_eval brand_relation_brands ((v, d1) :: env) e2) dl); intros.
        exists a0; split; try inversion H1; reflexivity.
        congruence.
        elim H3; clear H3; intros.
        elim H3; clear H3; intros.
        rewrite H3.
        rewrite <- H4 in *; clear H1 H3 H4; simpl.
        specialize (IHnrc_type2 ((v,a)::env)).
        assert (bindings_type ((v, a) :: env) ((v, τ₁) :: tenv)).
        unfold bindings_type.
        apply Forall2_cons; try assumption.
        simpl; split; try reflexivity.
        assert (r = τ₁) by (apply rtype_fequal; assumption).
        rewrite H1 in *; clear H1 x.
        apply (H0 a); left; reflexivity.
        specialize (IHnrc_type2 H1); clear H1.
        elim IHnrc_type2; clear IHnrc_type2; intros.
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
    - specialize (IHnrc_type1 env H); specialize (IHnrc_type2 env H); specialize (IHnrc_type3 env H).
      elim IHnrc_type1; intros; clear IHnrc_type1;
      elim IHnrc_type2; intros; clear IHnrc_type2;
      elim IHnrc_type3; intros; clear IHnrc_type3.
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
    - destruct (IHnrc_type1 _ H) as [dd [evald typd]].
      apply data_type_Either_inv in typd.
      rewrite evald.
      destruct typd as [[ddl[? typd]]|[ddr[? typd]]]; subst.
      + destruct (IHnrc_type2 ((xl,ddl)::env));
           unfold bindings_type in *; auto.
      + destruct (IHnrc_type3 ((xr,ddr)::env));
           unfold bindings_type in *; auto.
  Qed.

    (* we are only sensitive to the environment up to lookup *)
  Global Instance nrc_type_lookup_equiv_prop {m:basic_model} :
    Proper (lookup_equiv ==> eq ==> eq ==> iff) nrc_type.
  Proof.
    cut (Proper (lookup_equiv ==> eq ==> eq ==> impl) nrc_type);
    unfold Proper, respectful, lookup_equiv, iff, impl; intros; subst;
      [intuition; eauto | ].
    rename y0 into e.
    rename y1 into τ.
    rename x into b1.
    rename y into b2.
    revert b1 b2 τ H H2.
    induction e; simpl; inversion 2; subst; econstructor; eauto 3.
    - rewrite <- H; trivial.
    - eapply IHe2; try eassumption; intros.
      simpl; match_destr.
    - eapply IHe2; try eassumption; intros.
      simpl; match_destr.
    - eapply IHe2; try eassumption; intros.
      simpl; match_destr.
    - eapply IHe3; try eassumption; intros.
      simpl; match_destr.
  Qed.

End TNRC.

    Ltac nrc_inverter := 
  match goal with
    | [H:Coll _ = Coll _ |- _] => inversion H; clear H
    | [H: proj1_sig ?τ₁ = Coll₀ (proj1_sig ?τ₂) |- _] => rewrite (Coll_right_inv τ₁ τ₂) in H; subst
    | [H:  Coll₀ (proj1_sig ?τ₂) = proj1_sig ?τ₁ |- _] => symmetry in H
    (* Note: do not generalize too hastily on unaryOp/binOp constructors *)
    | [H:nrc_type _ (NRCVar _) _ |- _ ] => inversion H; clear H
    | [H:nrc_type _ (NRCConst _) _ |- _ ] => inversion H; clear H
    | [H:nrc_type _ (NRCBinop _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nrc_type _ (NRCUnop _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nrc_type _ (NRCLet _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nrc_type _ (NRCFor _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nrc_type _ (NRCIf _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H:nrc_type _ (NRCEither _ _ _ _ _ ) _ |- _ ] => inversion H; clear H
    | [H: (_,_)  = (_,_) |- _ ] => inversion H; clear H
    | [H: map (fun x2 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x2, proj1_sig (snd x2))) ?x0 = nil |- _] => apply (map_rtype_nil x0) in H; simpl in H; subst
    | [H: (map
             (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                (fst x, proj1_sig (snd x))) _)
          = 
          (map
             (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                (fst x, proj1_sig (snd x))) _) |- _ ] =>
      apply map_rtype_fequal in H; trivial
    | [H:Rec _ _ _ = Rec _ _ _ |- _ ] => generalize (Rec_inv H); clear H; intro H; try subst
    | [H: context [(_::nil) = map 
                                (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                   (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
                                                                                         
    | [H: context [map 
                     (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                        (fst x, proj1_sig (snd x))) _ = (_::nil) ] |- _] => apply map_eq_cons in H;
                                                                            destruct H as [? [? [? [??]]]]
    | [H:nrc_type _ _ (snd ?x) |- _ ] => destruct x
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
  end; try rtype_equalizer; try assumption; try subst; simpl in *; try nrc_inverter.

  Ltac nrc_input_well_typed :=
  repeat progress
         match goal with
           | [HO:nrc_type ?Γ ?op ?τout,
              HE:bindings_type ?env ?Γ
              |- context [(nrc_eval brand_relation_brands ?env ?op)]] =>
             let xout := fresh "dout" in
             let xtype := fresh "τout" in
             let xeval := fresh "eout" in
             destruct (typed_nrc_yields_typed_data env Γ op HE HO)
               as [xout [xeval xtype]]; rewrite xeval in *; simpl
         end.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
