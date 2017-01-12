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

Section cNRAEnvContext.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Require Import List.
  Require Import String.
  Require Import NPeano.
  Require Import Arith.

  Require Import Utils BasicRuntime.
  Require Import NRARuntime NRAOptim.
  Require Import cNRAEnv cNRAEnvIgnore cNRAEnvEq cNRAEnvContext.

(*
    Lemma aec_substs_prop_part2 c ps1 ps2 :
    Forall2 (fun xy1 xy2 => (fst xy1) = (fst xy2)
                            /\ cnraenv_eq (snd xy1) (snd xy2)) ps1 ps2
    -> cnraenv_ctxt_equiv_strict (aec_substs c ps1) (aec_substs c ps2).
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

  Fixpoint lift_nra_context (c:nra_ctxt) : cnraenv_ctxt :=
    match c with
      | CHole x'
        => CNHole x'
      | CPlug a
        => CNPlug (cnraenv_of_nra a)
      | CABinop b c1 c2
        => CANBinop b (lift_nra_context c1) (lift_nra_context c2)
      | CAUnop u c
        => CANUnop u (lift_nra_context c)
      | CAMap c1 c2
        => CANMap (lift_nra_context c1) (lift_nra_context c2)
      | CAMapConcat c1 c2
        => CANMapConcat (lift_nra_context c1) (lift_nra_context c2)
      | CAProduct c1 c2
        => CANProduct (lift_nra_context c1) (lift_nra_context c2)
      | CASelect c1 c2
        => CANSelect (lift_nra_context c1) (lift_nra_context c2)
      | CADefault c1 c2
        => CANDefault (lift_nra_context c1) (lift_nra_context c2)
      | CAEither c1 c2
        => CANEither (lift_nra_context c1) (lift_nra_context c2)
      | CAEitherConcat c1 c2
        => CANEitherConcat (lift_nra_context c1) (lift_nra_context c2)
      | CAApp c1 c2
        => CANApp (lift_nra_context c1) (lift_nra_context c2)
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
    aec_subst (lift_nra_context c) n (cnraenv_of_nra a).
  Proof.
    induction c; simpl; try congruence.
    match_destr.
  Qed.

  Lemma lift_nra_context_substs c ps :
    lift_nra_context (ac_substs c ps) =
    aec_substs (lift_nra_context c)
               (map (fun xy => (fst xy, cnraenv_of_nra (snd xy))) ps).
  Proof.
    revert c.
    induction ps; simpl; trivial.
    destruct a; simpl; intros.
    rewrite IHps, lift_nra_context_subst.
    trivial.
  Qed.

  Definition cnraenv_eq_under h c env (op1 op2:cnraenv) : Prop :=
        (forall (x:data)
                (dn_x:data_normalized h x),
          h ⊢ₑ op1 @ₑ x ⊣ c;env = h ⊢ₑ op2 @ₑ x ⊣ c;env)%cnraenv.

  Definition cnraenv_ctxt_equiv_under h c env (c1 c2 : cnraenv_ctxt)
    := forall (ps:list (nat * cnraenv)),
      match aec_simplify (aec_substs c1 ps),
            aec_simplify (aec_substs c2 ps)
      with
      | CNPlug a1, CNPlug a2 => cnraenv_eq_under h c env a1 a2
      | _, _ => True
      end.

  Lemma cnraenv_eq_under_equiv (op1 op2:cnraenv) : 
    (forall h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env), cnraenv_eq_under h c env op1 op2) <->
    cnraenv_eq op1 op2.
  Proof.
    unfold cnraenv_eq, cnraenv_eq_under; intuition.
  Qed.

  Lemma cnraenv_ctxt_equiv_under_equiv (op1 op2:cnraenv_ctxt) : 
    (forall h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env), cnraenv_ctxt_equiv_under h c env op1 op2) <->
    cnraenv_ctxt_equiv cnraenv_eq op1 op2.
  Proof.
    unfold cnraenv_ctxt_equiv, cnraenv_ctxt_equiv_under; split; intros.
    -match_case; match_case; intros.
     apply cnraenv_eq_under_equiv; intros h dl env dn_c dn_env.
     specialize (H h dl env dn_c dn_env ps). rewrite H0, H1 in H. trivial.
    - specialize (H ps). match_destr; match_destr.
      apply cnraenv_eq_under_equiv; auto.
  Qed.

  Lemma roundtrip_env e h c env :
    Forall (fun x => data_normalized h (snd x)) c ->
    data_normalized h env ->
    cnraenv_eq_under h c env 
                    ((cnraenv_of_nra (nra_of_cnraenv e )
                                    ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[|("PCONST", ‵(drec (rec_sort c)))|] ⊕‵[| ("PDATA", ID)|])))%cnraenv)
                    e.
  Proof.
    red; intros.
    simpl.
    rewrite <- cnraenv_eval_of_nra.
    rewrite unfold_env_nra_sort.
    rewrite (map_normalize_normalized_eq h (rec_sort c)).
    - rewrite drec_sort_idempotent.
      rewrite (normalize_normalized_eq h H0).
      reflexivity.
    - apply Forall_sorted; eauto.
  Qed.

  Instance ae_under_equiv h c env : Equivalence (cnraenv_eq_under h c env).
  Proof.
    unfold cnraenv_eq_under.
    constructor; red; intros.
    - reflexivity.
    - symmetry; auto.
    - transitivity ((h ⊢ₑ y @ₑ x0 ⊣ c;env)%cnraenv); eauto.
  Qed.

  Ltac goal_eq_simpler
    := repeat match goal with
              | [|- lift dcoll _ = lift dcoll _ ] => f_equal
              | [|- lift_oncoll _ ?x = lift_oncoll _ ?x ] => apply lift_oncoll_ext; intros
              | [|- rmap _ ?x = rmap _ ?x ] => apply rmap_ext; intros
              | [|- rmap_concat _ ?x = rmap_concat _ ?x ] => apply rmap_concat_ext; intros
              | [|- olift _ ?x = olift _ ?x ] => apply olift_ext; intros
              | [|- lift_filter _ ?x = lift_filter _ ?x ] => apply lift_filter_ext; intros
              end; try subst.

  Ltac dn_inverter
    := repeat match goal with
              | [H: data_normalized _ (dleft _) |- _ ] => inversion H; clear H; try subst
              | [H: data_normalized _ (dright _) |- _ ] => inversion H; clear H; try subst
              end.

  Hint Resolve cnraenv_eval_normalized.
  Hint Resolve data_normalized_dcoll_in.

  Instance aeu_Binop_proper h c env :
    Proper
      (eq ==>
          cnraenv_eq_under h c env ==>
          cnraenv_eq_under h c env ==>
          cnraenv_eq_under h c env) ANBinop.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H, H0, H1 by trivial; trivial.
  Qed.

  Instance aeu_Unop_proper h c env :
    Proper
      (eq ==>
          cnraenv_eq_under h c env ==>
          cnraenv_eq_under h c env) ANUnop.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H, H0 by trivial.
    trivial.
  Qed.

  Instance aeu_Map_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANMap.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_MapConcat_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANMapConcat.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_Product_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANProduct.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_Select_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANSelect.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
    rewrite H; eauto.
  Qed.

  Instance aeu_Default_proper h c env :
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANDefault.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H, H0 by trivial.
    trivial.
  Qed.
   
  Instance aeu_Either_proper h c env :
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANEither.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    match_destr; dn_inverter; eauto.
  Qed.

  Instance aeu_EitherConcat_proper h c env :
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANEitherConcat.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
    rewrite H; eauto.
  Qed.

  Instance aeu_App_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env ==>
                       cnraenv_eq_under h c env) ANApp.
  Proof.
    unfold Proper, respectful, cnraenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.
  
  Instance aec_under_refl h c env : Reflexive (cnraenv_ctxt_equiv_under h c env).
  Proof.
    red; unfold cnraenv_ctxt_equiv_under; intros.
    match_destr.
    reflexivity.
  Qed.

  Instance aecu_Plug_proper h c env : Proper (cnraenv_eq_under h c env ==> cnraenv_ctxt_equiv_under h c env) CNPlug.
  Proof.
    unfold Proper, respectful, cnraenv_ctxt_equiv_under, cnraenv_eq_under; intros.
    autorewrite with aec_substs.
    simpl.
    trivial.
  Qed.
   
  Instance aecu_Binop_proper h c env :
    Proper
      (eq ==>
          cnraenv_ctxt_equiv_under h c env ==>
          cnraenv_ctxt_equiv_under h c env ==>
          cnraenv_ctxt_equiv_under h c env) CANBinop.
  Proof.
    unfold Proper, respectful, cnraenv_ctxt_equiv_under.
    intros; subst.
    autorewrite with aec_substs; simpl.
    specialize (H0 ps); specialize (H1 ps).
    do 2 (match_destr_in H0; match_destr_in H1).
    apply aeu_Binop_proper; trivial.
  Qed.

  Instance aecu_Unop_proper h c env :
    Proper
      (eq ==>
          cnraenv_ctxt_equiv_under h c env ==>
          cnraenv_ctxt_equiv_under h c env) CANUnop.
  Proof.
    unfold Proper, respectful, cnraenv_ctxt_equiv_under.
    intros; subst.
    autorewrite with aec_substs; simpl.
    specialize (H0 ps).
    do 2 (match_destr_in H0).
    apply aeu_Unop_proper; trivial.
  Qed.

   Instance aecu_Map_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANMap.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Map_proper; trivial.
   Qed.

   Instance aecu_MapConcat_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANMapConcat.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_MapConcat_proper; trivial.
   Qed.

   Instance aecu_Product_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANProduct.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Product_proper; trivial.
   Qed.

   Instance aecu_Select_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) : 
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANSelect.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Select_proper; trivial.
   Qed.

   Instance aecu_Default_proper h c env :
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANDefault.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Default_proper; trivial.
   Qed.
   
   Instance aecu_Either_proper h c env :
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANEither.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Either_proper; trivial.
   Qed.

   Instance aecu_EitherConcat_proper h c env :
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANEitherConcat.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_EitherConcat_proper; trivial.
   Qed.

   Instance aecu_App_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env ==>
                        cnraenv_ctxt_equiv_under h c env) CANApp.
   Proof.
     unfold Proper, respectful, cnraenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_App_proper; trivial.
   Qed.

 Lemma aec_substs_under_prop_part2 h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) e ps1 ps2 :
     Forall2 (fun xy1 xy2 => (fst xy1) = (fst xy2)
            /\ cnraenv_eq_under h c env (snd xy1) (snd xy2)) ps1 ps2
     -> cnraenv_ctxt_equiv_under
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
     - apply aecu_MapConcat_proper; auto.
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
           (fun xy1 xy2 : nat * cnraenv =>
            fst xy1 = fst xy2 /\ cnraenv_eq_under h c env (snd xy1) (snd xy2))
           (map
              (fun x : nat * cnraenv =>
               (fst x,
               (cnraenv_of_nra (nra_of_cnraenv (snd x))
                ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[| ("PCONST", ‵(drec (rec_sort c)))|] ⊕ ‵[| ("PDATA", ID)|])))%cnraenv))
              ps) ps.
   Proof.
     induction ps; simpl; trivial.
     - constructor; auto 2.
       simpl. split; trivial.
       apply roundtrip_env; trivial.
   Qed.

   Global Instance lift_nra_context_proper : Proper (nra_ctxt_equiv nra_eq ==> cnraenv_ctxt_equiv cnraenv_eq) lift_nra_context.
  Proof.
    unfold Proper, respectful.
    intros c1 c2 H.
    apply <- cnraenv_ctxt_equiv_strict_equiv.

    red; intros ps Hsort Hequiv.
    match_case; match_case; intros.
    red; intros h dl dnc env dnenv d dnd.
    specialize (H (map (fun xy => (fst xy,
                                   (AApp (nra_of_cnraenv (snd xy)) (make_fixed_pat_context_data (drec (rec_sort dl)) env)))) ps)).
    
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
       generalize (ac_holes_saturated_subst (fun x => (nra_of_cnraenv x ◯ make_fixed_pat_context_data (drec (rec_sort dl)) env)%nra) c1 ps c1incl);
         intros c1nholes.
       generalize (ac_holes_saturated_subst (fun x => (nra_of_cnraenv x ◯ make_fixed_pat_context_data (drec (rec_sort dl)) env)%nra) c2 ps c2incl);
         intros c2nholes.
       destruct (ac_simplify_nholes _ c1nholes) as [c1s c1seq].
       destruct (ac_simplify_nholes _ c2nholes) as [c2s c2seq].
       generalize (aec_simplify_lift_commute (ac_substs c1
             (map
                (fun xy : nat * cnraenv =>
                   (fst xy, AApp (nra_of_cnraenv (snd xy)) (make_fixed_pat_context_data (drec (rec_sort dl)) env))) ps)));
        intros leq1.
      generalize (aec_simplify_lift_commute (ac_substs c2
             (map
                (fun xy : nat * cnraenv =>
                   (fst xy, AApp (nra_of_cnraenv (snd xy)) (make_fixed_pat_context_data (drec (rec_sort dl)) env))) ps)));
        intros leq2.
      rewrite lift_nra_context_substs in leq1, leq2.
      rewrite map_map in leq1, leq2. simpl in leq1, leq2.
      rewrite c1seq, c2seq in *.
      intros.
      generalize
        (aec_substs_under_prop_part2 h dl env dnc dnenv c1
                                     (map (fun x => (fst x, 
                                     ((cnraenv_of_nra (nra_of_cnraenv (snd x)))
                                        ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[| ("PCONST", ‵((drec (rec_sort dl))))|] ⊕ ‵[| ("PDATA", ID)|])))%cnraenv)) ps) ps (f2_roundtrip _ _ _ _ dnc dnenv)); intros s1eq.

      generalize
        (aec_substs_under_prop_part2 h dl env dnc dnenv c2
                                     (map (fun x => (fst x, 
                                     ((cnraenv_of_nra (nra_of_cnraenv (snd x)))
                                        ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[| ("PCONST", ‵((drec (rec_sort dl))))|]⊕ ‵[| ("PDATA", ID)|])))%cnraenv)) ps) ps (f2_roundtrip _ _ _ _ dnc dnenv)); intros s2eq.
      simpl in s1eq, s2eq.
      simpl in *.
      specialize (s1eq nil); specialize (s2eq nil).
      simpl in s1eq, s2eq.
      rewrite leq1, H1 in s1eq.
      rewrite leq2, H0 in s2eq.
      assert (cseq: ((cnraenv_of_nra c1s) ≡ₑ (cnraenv_of_nra c2s))%cnraenv).
      { apply cnraenv_of_nra_proper. trivial. }
      rewrite <- cnraenv_eq_under_equiv in cseq.
      specialize (cseq h dl env).
      rewrite s1eq, s2eq in cseq.
      red in cseq.
      apply cseq; auto.
  Qed.

  Global Instance lift_nra_context_strict_proper : Proper (nra_ctxt_equiv_strict nra_eq ==> cnraenv_ctxt_equiv_strict cnraenv_eq) lift_nra_context.
  Proof.
    unfold Proper, respectful.
    intros c1 c2 H.
    apply cnraenv_ctxt_equiv_strict_equiv.
    apply nra_ctxt_equiv_strict_equiv in H.
    apply lift_nra_context_proper; trivial.
  Qed.

  Local Open Scope nra_ctxt.
  Local Open Scope cnraenv_ctxt.

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

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
