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

(*******************************
 * Algebra contexts *
 *******************************)

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import String.
Require Import NPeano.
Require Import Arith.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRARuntime.
Require Import NRAOptim.
Require Import cNRAEnv.
Require Import cNRAEnvIgnore.
Require Import cNRAEnvEq.
Require Import cNRAEnvContext.

Section cNRAEnvContext.
(*
    Lemma aec_substs_prop_part2 c ps1 ps2 :
    Forall2 (fun xy1 xy2 => (fst xy1) = (fst xy2)
                            /\ nraenv_core_eq (snd xy1) (snd xy2)) ps1 ps2
    -> nraenv_core_ctxt_equiv_strict (aec_substs c ps1) (aec_substs c ps2).
    Proof.
    intros F; revert c.
    induction F; simpl.
    - reflexivity. 
    - destruct x; destruct y; destruct H; simpl in *. subst.
      intros. rewrite IHF.
      rewrite H0.
      reflexivity.
    Qed.
*)

  Context {fruntime:foreign_runtime}.

  Fixpoint lift_nra_context (c:nra_ctxt) : nraenv_core_ctxt :=
    match c with
      | CNRAHole x'
        => CcNRAEnvHole x'
      | CNRAPlug a
        => CcNRAEnvPlug (nraenv_core_of_nra a)
      | CNRABinop b c1 c2
        => CcNRAEnvBinop b (lift_nra_context c1) (lift_nra_context c2)
      | CNRAUnop u c
        => CcNRAEnvUnop u (lift_nra_context c)
      | CNRAMap c1 c2
        => CcNRAEnvMap (lift_nra_context c1) (lift_nra_context c2)
      | CNRAMapProduct c1 c2
        => CcNRAEnvMapProduct (lift_nra_context c1) (lift_nra_context c2)
      | CNRAProduct c1 c2
        => CcNRAEnvProduct (lift_nra_context c1) (lift_nra_context c2)
      | CNRASelect c1 c2
        => CcNRAEnvSelect (lift_nra_context c1) (lift_nra_context c2)
      | CNRADefault c1 c2
        => CcNRAEnvDefault (lift_nra_context c1) (lift_nra_context c2)
      | CNRAEither c1 c2
        => CcNRAEnvEither (lift_nra_context c1) (lift_nra_context c2)
      | CNRAEitherConcat c1 c2
        => CcNRAEnvEitherConcat (lift_nra_context c1) (lift_nra_context c2)
      | CNRAApp c1 c2
        => CcNRAEnvApp (lift_nra_context c1) (lift_nra_context c2)
    end.

  Lemma aec_simplify_lift_commute c :
    aec_simplify (lift_nra_context c) = lift_nra_context (ac_simplify c).
  Proof.
    induction c; simpl; trivial
    ; try rewrite IHc; try rewrite IHc1; try rewrite IHc2
    ; first [destruct (ac_simplify c) | destruct (ac_simplify c1); simpl; trivial
    ; destruct (ac_simplify c2)]; simpl; trivial.
  Qed.
  
  Lemma  aec_holes_lift c:
    aec_holes (lift_nra_context c) = ac_holes c.
  Proof.
    induction c; simpl; try congruence.
  Qed.

  Lemma lift_nra_context_subst c n a :
    lift_nra_context (ac_subst c n a) =
    aec_subst (lift_nra_context c) n (nraenv_core_of_nra a).
  Proof.
    induction c; simpl; try congruence.
    match_destr.
  Qed.

  Lemma lift_nra_context_substs c ps :
    lift_nra_context (ac_substs c ps) =
    aec_substs (lift_nra_context c)
               (map (fun xy => (fst xy, nraenv_core_of_nra (snd xy))) ps).
  Proof.
    revert c.
    induction ps; simpl; trivial.
    destruct a; simpl; intros.
    rewrite IHps, lift_nra_context_subst.
    trivial.
  Qed.

  Definition nraenv_core_eq_under h c env (op1 op2:nraenv_core) : Prop :=
        (forall (x:data)
                (dn_x:data_normalized h x),
          h ⊢ₑ op1 @ₑ x ⊣ c;env = h ⊢ₑ op2 @ₑ x ⊣ c;env)%nraenv_core.

  Definition nraenv_core_ctxt_equiv_under h c env (c1 c2 : nraenv_core_ctxt)
    := forall (ps:list (nat * nraenv_core)),
      match aec_simplify (aec_substs c1 ps),
            aec_simplify (aec_substs c2 ps)
      with
      | CcNRAEnvPlug a1, CcNRAEnvPlug a2 => nraenv_core_eq_under h c env a1 a2
      | _, _ => True
      end.

  Lemma nraenv_core_eq_under_equiv (op1 op2:nraenv_core) : 
    (forall h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env), nraenv_core_eq_under h c env op1 op2) <->
    nraenv_core_eq op1 op2.
  Proof.
    unfold nraenv_core_eq, nraenv_core_eq_under; intuition.
  Qed.

  Lemma nraenv_core_ctxt_equiv_under_equiv (op1 op2:nraenv_core_ctxt) : 
    (forall h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env), nraenv_core_ctxt_equiv_under h c env op1 op2) <->
    nraenv_core_ctxt_equiv nraenv_core_eq op1 op2.
  Proof.
    unfold nraenv_core_ctxt_equiv, nraenv_core_ctxt_equiv_under; split; intros.
    -match_case; match_case; intros.
     apply nraenv_core_eq_under_equiv; intros h dl env dn_c dn_env.
     specialize (H h dl env dn_c dn_env ps). rewrite H0, H1 in H. trivial.
    - specialize (H ps). match_destr; match_destr.
      apply nraenv_core_eq_under_equiv; auto.
  Qed.

  Lemma roundtrip_env e h c env :
    Forall (fun x => data_normalized h (snd x)) c ->
    data_normalized h env ->
    nraenv_core_eq_under h c env 
                    ((nraenv_core_of_nra (nra_of_nraenv_core e )
                                    ◯ (‵[| ("PBIND", ‵(env))|] ⊕ ‵[| ("PDATA", ID)|]))%nraenv_core)
                    e.
  Proof.
    red; intros.
    simpl.
    rewrite <- nraenv_core_eval_of_nra.
    rewrite unfold_env_nra.
    unfold nra_context_data.
    f_equal.
    f_equal.
    rewrite (normalize_normalized_eq h H0).
    trivial.
  Qed.

  Instance ae_under_equiv h c env : Equivalence (nraenv_core_eq_under h c env).
  Proof.
    unfold nraenv_core_eq_under.
    constructor; red; intros.
    - reflexivity.
    - symmetry; auto.
    - transitivity ((h ⊢ₑ y @ₑ x0 ⊣ c;env)%nraenv_core); eauto.
  Qed.

  Ltac goal_eq_simpler
    := repeat match goal with
              | [|- lift dcoll _ = lift dcoll _ ] => f_equal
              | [|- lift_oncoll _ ?x = lift_oncoll _ ?x ] => apply lift_oncoll_ext; intros
              | [|- lift_map _ ?x = lift_map _ ?x ] => apply lift_map_ext; intros
              | [|- omap_product _ ?x = omap_product _ ?x ] => apply omap_product_ext; intros
              | [|- olift _ ?x = olift _ ?x ] => apply olift_ext; intros
              | [|- lift_filter _ ?x = lift_filter _ ?x ] => apply lift_filter_ext; intros
              end; try subst.

  Ltac dn_inverter
    := repeat match goal with
              | [H: data_normalized _ (dleft _) |- _ ] => inversion H; clear H; try subst
              | [H: data_normalized _ (dright _) |- _ ] => inversion H; clear H; try subst
              end.

  Hint Resolve nraenv_core_eval_normalized.
  Hint Resolve data_normalized_dcoll_in.

  Instance aeu_Binop_proper h c env :
    Proper
      (eq ==>
          nraenv_core_eq_under h c env ==>
          nraenv_core_eq_under h c env ==>
          nraenv_core_eq_under h c env) cNRAEnvBinop.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H, H0, H1 by trivial; trivial.
  Qed.

  Instance aeu_Unop_proper h c env :
    Proper
      (eq ==>
          nraenv_core_eq_under h c env ==>
          nraenv_core_eq_under h c env) cNRAEnvUnop.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H, H0 by trivial.
    trivial.
  Qed.

  Instance aeu_Map_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvMap.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_MapProduct_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvMapProduct.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_Product_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvProduct.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H, H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_Select_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvSelect.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
    rewrite H; eauto.
  Qed.

  Instance aeu_Default_proper h c env :
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvDefault.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H, H0 by trivial.
    trivial.
  Qed.
   
  Instance aeu_Either_proper h c env :
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvEither.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    match_destr; dn_inverter; eauto.
  Qed.

  Instance aeu_EitherConcat_proper h c env :
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvEitherConcat.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
    rewrite H; eauto.
  Qed.

  Instance aeu_App_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env ==>
                       nraenv_core_eq_under h c env) cNRAEnvApp.
  Proof.
    unfold Proper, respectful, nraenv_core_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.
  
  Instance aec_under_refl h c env : Reflexive (nraenv_core_ctxt_equiv_under h c env).
  Proof.
    red; unfold nraenv_core_ctxt_equiv_under; intros.
    match_destr.
    reflexivity.
  Qed.

  Instance aecu_Plug_proper h c env : Proper (nraenv_core_eq_under h c env ==> nraenv_core_ctxt_equiv_under h c env) CcNRAEnvPlug.
  Proof.
    unfold Proper, respectful, nraenv_core_ctxt_equiv_under, nraenv_core_eq_under; intros.
    autorewrite with aec_substs.
    simpl.
    trivial.
  Qed.
   
  Instance aecu_Binop_proper h c env :
    Proper
      (eq ==>
          nraenv_core_ctxt_equiv_under h c env ==>
          nraenv_core_ctxt_equiv_under h c env ==>
          nraenv_core_ctxt_equiv_under h c env) CcNRAEnvBinop.
  Proof.
    unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
    intros; subst.
    autorewrite with aec_substs; simpl.
    specialize (H0 ps); specialize (H1 ps).
    do 2 (match_destr_in H0; match_destr_in H1).
    apply aeu_Binop_proper; trivial.
  Qed.

  Instance aecu_Unop_proper h c env :
    Proper
      (eq ==>
          nraenv_core_ctxt_equiv_under h c env ==>
          nraenv_core_ctxt_equiv_under h c env) CcNRAEnvUnop.
  Proof.
    unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
    intros; subst.
    autorewrite with aec_substs; simpl.
    specialize (H0 ps).
    do 2 (match_destr_in H0).
    apply aeu_Unop_proper; trivial.
  Qed.

   Instance aecu_Map_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvMap.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Map_proper; trivial.
   Qed.

   Instance aecu_MapProduct_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvMapProduct.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_MapProduct_proper; trivial.
   Qed.

   Instance aecu_Product_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvProduct.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Product_proper; trivial.
   Qed.

   Instance aecu_Select_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) : 
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvSelect.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Select_proper; trivial.
   Qed.

   Instance aecu_Default_proper h c env :
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvDefault.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Default_proper; trivial.
   Qed.
   
   Instance aecu_Either_proper h c env :
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvEither.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Either_proper; trivial.
   Qed.

   Instance aecu_EitherConcat_proper h c env :
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvEitherConcat.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_EitherConcat_proper; trivial.
   Qed.

   Instance aecu_App_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env ==>
                        nraenv_core_ctxt_equiv_under h c env) CcNRAEnvApp.
   Proof.
     unfold Proper, respectful, nraenv_core_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_App_proper; trivial.
   Qed.

 Lemma aec_substs_under_prop_part2 h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) e ps1 ps2 :
     Forall2 (fun xy1 xy2 => (fst xy1) = (fst xy2)
            /\ nraenv_core_eq_under h c env (snd xy1) (snd xy2)) ps1 ps2
     -> nraenv_core_ctxt_equiv_under
          h c env
          (aec_substs (lift_nra_context e) ps1)
          (aec_substs (lift_nra_context e) ps2).
   Proof.
     induction e; simpl; intros f2; autorewrite with aec_substs.
     - induction f2; simpl.
       + reflexivity.
       + destruct x; destruct y; destruct H; simpl in *; subst.
          match_destr.
          autorewrite with aec_substs.
          apply aecu_Plug_proper; trivial.
     - reflexivity.
     - apply aecu_Binop_proper; auto.
     - apply aecu_Unop_proper; auto.
     - apply aecu_Map_proper; auto.
     - apply aecu_MapProduct_proper; auto.
     - apply aecu_Product_proper; auto.
     - apply aecu_Select_proper; auto.
     - apply aecu_Default_proper; auto.
     - apply aecu_Either_proper; auto.
     - apply aecu_EitherConcat_proper; auto.
     - apply aecu_App_proper; auto.
   Qed.

   Lemma f2_roundtrip h c env ps 
     (dn_c:Forall (fun x => data_normalized h (snd x)) c)
       (dn_env:data_normalized h env) :
   Forall2
           (fun xy1 xy2 : nat * nraenv_core =>
            fst xy1 = fst xy2 /\ nraenv_core_eq_under h c env (snd xy1) (snd xy2))
           (map
              (fun x : nat * nraenv_core =>
               (fst x,
               (nraenv_core_of_nra (nra_of_nraenv_core (snd x))
                ◯ (‵[| ("PBIND", ‵(env))|] ⊕ ‵[| ("PDATA", ID)|]))%nraenv_core))
              ps) ps.
   Proof.
     induction ps; simpl; trivial.
     - constructor; auto 2.
       simpl. split; trivial.
       apply roundtrip_env; trivial.
   Qed.

   Global Instance lift_nra_context_proper : Proper (nra_ctxt_equiv nra_eq ==> nraenv_core_ctxt_equiv nraenv_core_eq) lift_nra_context.
  Proof.
    unfold Proper, respectful.
    intros c1 c2 H.
    apply <- nraenv_core_ctxt_equiv_strict_equiv.

    red; intros ps Hsort Hequiv.
    match_case; match_case; intros.
    red; intros h dl dnc env dnenv d dnd.
    specialize (H (map (fun xy => (fst xy,
                                   (NRAApp (nra_of_nraenv_core (snd xy)) (make_fixed_nra_context_data env)))) ps)).
    
      symmetry in Hequiv.
       generalize (equivlist_in Hequiv); intros Hin.
       assert (c1incl:incl (ac_holes c1) (domain ps)).
       { intros x xin; apply (Hin x); rewrite in_app_iff;
         repeat rewrite aec_holes_lift; intuition. }       
       assert (c2incl:incl (ac_holes c2) (domain ps)).
       { intros x xin; apply (Hin x); rewrite in_app_iff;
         repeat rewrite aec_holes_lift; intuition. }
       repeat rewrite map_map in H.
       simpl in H.
       generalize (ac_holes_saturated_subst (fun x => (nra_of_nraenv_core x ◯ make_fixed_nra_context_data env)%nra) c1 ps c1incl);
         intros c1nholes.
       generalize (ac_holes_saturated_subst (fun x => (nra_of_nraenv_core x ◯ make_fixed_nra_context_data env)%nra) c2 ps c2incl);
         intros c2nholes.
       destruct (ac_simplify_nholes _ c1nholes) as [c1s c1seq].
       destruct (ac_simplify_nholes _ c2nholes) as [c2s c2seq].
       generalize (aec_simplify_lift_commute (ac_substs c1
             (map
                (fun xy : nat * nraenv_core =>
                   (fst xy, NRAApp (nra_of_nraenv_core (snd xy)) (make_fixed_nra_context_data env))) ps)));
        intros leq1.
      generalize (aec_simplify_lift_commute (ac_substs c2
             (map
                (fun xy : nat * nraenv_core =>
                   (fst xy, NRAApp (nra_of_nraenv_core (snd xy)) (make_fixed_nra_context_data env))) ps)));
        intros leq2.
      rewrite lift_nra_context_substs in leq1, leq2.
      rewrite map_map in leq1, leq2. simpl in leq1, leq2.
      rewrite c1seq, c2seq in *.
      intros.
      generalize
        (aec_substs_under_prop_part2 h dl env dnc dnenv c1
                                     (map (fun x => (fst x, 
                                     ((nraenv_core_of_nra (nra_of_nraenv_core (snd x)))
                                        ◯ (‵[| ("PBIND", ‵(env))|] ⊕ ‵[| ("PDATA", ID)|]))%nraenv_core)) ps) ps (f2_roundtrip _ _ _ _ dnc dnenv)); intros s1eq.

      generalize
        (aec_substs_under_prop_part2 h dl env dnc dnenv c2
                                     (map (fun x => (fst x, 
                                     ((nraenv_core_of_nra (nra_of_nraenv_core (snd x)))
                                        ◯ (‵[| ("PBIND", ‵(env))|] ⊕ ‵[| ("PDATA", ID)|]))%nraenv_core)) ps) ps (f2_roundtrip _ _ _ _ dnc dnenv)); intros s2eq.
      simpl in s1eq, s2eq.
      simpl in *.
      specialize (s1eq nil); specialize (s2eq nil).
      simpl in s1eq, s2eq.
      rewrite leq1, H1 in s1eq.
      rewrite leq2, H0 in s2eq.
      assert (cseq: ((nraenv_core_of_nra c1s) ≡ₑ (nraenv_core_of_nra c2s))%nraenv_core).
      { apply nraenv_core_of_nra_proper. trivial. }
      rewrite <- nraenv_core_eq_under_equiv in cseq.
      specialize (cseq h dl env).
      rewrite s1eq, s2eq in cseq.
      red in cseq.
      apply cseq; auto.
  Qed.

  Global Instance lift_nra_context_strict_proper : Proper (nra_ctxt_equiv_strict nra_eq ==> nraenv_core_ctxt_equiv_strict nraenv_core_eq) lift_nra_context.
  Proof.
    unfold Proper, respectful.
    intros c1 c2 H.
    apply nraenv_core_ctxt_equiv_strict_equiv.
    apply nra_ctxt_equiv_strict_equiv in H.
    apply lift_nra_context_proper; trivial.
  Qed.

  Local Open Scope nra_ctxt.
  Local Open Scope nraenv_core_ctxt.

  (** This is just a restatement of lift_nra_context_proper
        which visually looks more like the paper version.
        For the mechanization, lift_nra_context_proper 
        is nicer, since it explicitly states that lift_nra_context
        is a morphism between the two equivalences
        and registers that relationship with the rewriting infrastructure
        of Coq.
   *)
  Theorem contextual_equivalence_lifting (c₁ c₂:nra_ctxt) :
    c₁ ≡ₐ c₂ -> lift_nra_context c₁ ≡ₑ lift_nra_context c₂.
  Proof.
    apply lift_nra_context_proper.
  Qed.

End cNRAEnvContext.

