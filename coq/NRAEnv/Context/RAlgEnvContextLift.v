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

Section RAlgEnvContext.

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
  Require Import RAlgEnv RAlgEnvIgnore RAlgEnvEq RAlgEnvContext.

(*
    Lemma aec_substs_prop_part2 c ps1 ps2 :
    Forall2 (fun xy1 xy2 => (fst xy1) = (fst xy2)
                            /\ algenv_eq (snd xy1) (snd xy2)) ps1 ps2
    -> algenv_ctxt_equiv_strict (aec_substs c ps1) (aec_substs c ps2).
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

  Fixpoint lift_alg_context (c:alg_ctxt) : algenv_ctxt :=
    match c with
      | CHole x'
        => CNHole x'
      | CPlug a
        => CNPlug (algenv_of_alg a)
      | CABinop b c1 c2
        => CANBinop b (lift_alg_context c1) (lift_alg_context c2)
      | CAUnop u c
        => CANUnop u (lift_alg_context c)
      | CAMap c1 c2
        => CANMap (lift_alg_context c1) (lift_alg_context c2)
      | CAMapConcat c1 c2
        => CANMapConcat (lift_alg_context c1) (lift_alg_context c2)
      | CAProduct c1 c2
        => CANProduct (lift_alg_context c1) (lift_alg_context c2)
      | CASelect c1 c2
        => CANSelect (lift_alg_context c1) (lift_alg_context c2)
      | CADefault c1 c2
        => CANDefault (lift_alg_context c1) (lift_alg_context c2)
      | CAEither c1 c2
        => CANEither (lift_alg_context c1) (lift_alg_context c2)
      | CAEitherConcat c1 c2
        => CANEitherConcat (lift_alg_context c1) (lift_alg_context c2)
      | CAApp c1 c2
        => CANApp (lift_alg_context c1) (lift_alg_context c2)
    end.

  Lemma aec_simplify_lift_commute c :
    aec_simplify (lift_alg_context c) = lift_alg_context (ac_simplify c).
  Proof.
    induction c; simpl; trivial
    ; try rewrite IHc; try rewrite IHc1; try rewrite IHc2
    ; first [destruct (ac_simplify c) | destruct (ac_simplify c1); simpl; trivial
    ; destruct (ac_simplify c2)]; simpl; trivial.
  Qed.
  
  Lemma  aec_holes_lift c:
    aec_holes (lift_alg_context c) = ac_holes c.
  Proof.
    induction c; simpl; try congruence.
  Qed.

  Lemma lift_alg_context_subst c n a :
    lift_alg_context (ac_subst c n a) =
    aec_subst (lift_alg_context c) n (algenv_of_alg a).
  Proof.
    induction c; simpl; try congruence.
    match_destr.
  Qed.

  Lemma lift_alg_context_substs c ps :
    lift_alg_context (ac_substs c ps) =
    aec_substs (lift_alg_context c)
               (map (fun xy => (fst xy, algenv_of_alg (snd xy))) ps).
  Proof.
    revert c.
    induction ps; simpl; trivial.
    destruct a; simpl; intros.
    rewrite IHps, lift_alg_context_subst.
    trivial.
  Qed.

  Definition algenv_eq_under h c env (op1 op2:algenv) : Prop :=
        (forall (x:data)
                (dn_x:data_normalized h x),
          h ⊢ₑ op1 @ₑ x ⊣ c;env = h ⊢ₑ op2 @ₑ x ⊣ c;env)%algenv.

  Definition algenv_ctxt_equiv_under h c env (c1 c2 : algenv_ctxt)
    := forall (ps:list (nat * algenv)),
      match aec_simplify (aec_substs c1 ps),
            aec_simplify (aec_substs c2 ps)
      with
      | CNPlug a1, CNPlug a2 => algenv_eq_under h c env a1 a2
      | _, _ => True
      end.

  Lemma algenv_eq_under_equiv (op1 op2:algenv) : 
    (forall h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env), algenv_eq_under h c env op1 op2) <->
    algenv_eq op1 op2.
  Proof.
    unfold algenv_eq, algenv_eq_under; intuition.
  Qed.

  Lemma algenv_ctxt_equiv_under_equiv (op1 op2:algenv_ctxt) : 
    (forall h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env), algenv_ctxt_equiv_under h c env op1 op2) <->
    algenv_ctxt_equiv algenv_eq op1 op2.
  Proof.
    unfold algenv_ctxt_equiv, algenv_ctxt_equiv_under; split; intros.
    -match_case; match_case; intros.
     apply algenv_eq_under_equiv; intros h c env dn_c dn_env.
     specialize (H h c env dn_c dn_env ps). rewrite H0, H1 in H. trivial.
    - specialize (H ps). match_destr; match_destr.
      apply algenv_eq_under_equiv; auto.
  Qed.

  Lemma roundtrip_env e h c env :
    Forall (fun x => data_normalized h (snd x)) c ->
    data_normalized h env ->
    algenv_eq_under h c env 
                    ((algenv_of_alg (alg_of_algenv e )
                                    ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[|("PCONST", ‵(drec (rec_sort c)))|] ⊕‵[| ("PDATA", ID)|])))%algenv)
                    e.
  Proof.
    red; intros.
    simpl.
    rewrite <- fun_of_algenv_of_alg.
    rewrite unfold_env_alg_sort.
    rewrite (map_normalize_normalized_eq h (rec_sort c)).
    - rewrite drec_sort_idempotent.
      rewrite (normalize_normalized_eq h H0).
      reflexivity.
    - apply Forall_sorted; eauto.
  Qed.

  Instance ae_under_equiv h c env : Equivalence (algenv_eq_under h c env).
  Proof.
    unfold algenv_eq_under.
    constructor; red; intros.
    - reflexivity.
    - symmetry; auto.
    - transitivity ((h ⊢ₑ y @ₑ x0 ⊣ c;env)%algenv); eauto.
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

  Hint Resolve fun_of_algenv_normalized.
  Hint Resolve data_normalized_dcoll_in.

  Instance aeu_Binop_proper h c env :
    Proper
      (eq ==>
          algenv_eq_under h c env ==>
          algenv_eq_under h c env ==>
          algenv_eq_under h c env) ANBinop.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H, H0, H1 by trivial; trivial.
  Qed.

  Instance aeu_Unop_proper h c env :
    Proper
      (eq ==>
          algenv_eq_under h c env ==>
          algenv_eq_under h c env) ANUnop.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H, H0 by trivial.
    trivial.
  Qed.

  Instance aeu_Map_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANMap.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_MapConcat_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANMapConcat.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_Product_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANProduct.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H by trivial.
    goal_eq_simpler; eauto.
  Qed.

  Instance aeu_Select_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANSelect.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
    rewrite H; eauto.
  Qed.

  Instance aeu_Default_proper h c env :
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANDefault.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H, H0 by trivial.
    trivial.
  Qed.
   
  Instance aeu_Either_proper h c env :
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANEither.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    match_destr; dn_inverter; eauto.
  Qed.

  Instance aeu_EitherConcat_proper h c env :
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANEitherConcat.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
    rewrite H; eauto.
  Qed.

  Instance aeu_App_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
    Proper
      (algenv_eq_under h c env ==>
                       algenv_eq_under h c env ==>
                       algenv_eq_under h c env) ANApp.
  Proof.
    unfold Proper, respectful, algenv_eq_under; simpl; intros.
    rewrite H0 by trivial.
    goal_eq_simpler; eauto.
  Qed.
  
  Instance aec_under_refl h c env : Reflexive (algenv_ctxt_equiv_under h c env).
  Proof.
    red; unfold algenv_ctxt_equiv_under; intros.
    match_destr.
    reflexivity.
  Qed.

  Instance aecu_Plug_proper h c env : Proper (algenv_eq_under h c env ==> algenv_ctxt_equiv_under h c env) CNPlug.
  Proof.
    unfold Proper, respectful, algenv_ctxt_equiv_under, algenv_eq_under; intros.
    autorewrite with aec_substs.
    simpl.
    trivial.
  Qed.
   
  Instance aecu_Binop_proper h c env :
    Proper
      (eq ==>
          algenv_ctxt_equiv_under h c env ==>
          algenv_ctxt_equiv_under h c env ==>
          algenv_ctxt_equiv_under h c env) CANBinop.
  Proof.
    unfold Proper, respectful, algenv_ctxt_equiv_under.
    intros; subst.
    autorewrite with aec_substs; simpl.
    specialize (H0 ps); specialize (H1 ps).
    do 2 (match_destr_in H0; match_destr_in H1).
    apply aeu_Binop_proper; trivial.
  Qed.

  Instance aecu_Unop_proper h c env :
    Proper
      (eq ==>
          algenv_ctxt_equiv_under h c env ==>
          algenv_ctxt_equiv_under h c env) CANUnop.
  Proof.
    unfold Proper, respectful, algenv_ctxt_equiv_under.
    intros; subst.
    autorewrite with aec_substs; simpl.
    specialize (H0 ps).
    do 2 (match_destr_in H0).
    apply aeu_Unop_proper; trivial.
  Qed.

   Instance aecu_Map_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env):
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANMap.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Map_proper; trivial.
   Qed.

   Instance aecu_MapConcat_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANMapConcat.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_MapConcat_proper; trivial.
   Qed.

   Instance aecu_Product_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANProduct.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Product_proper; trivial.
   Qed.

   Instance aecu_Select_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) : 
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANSelect.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Select_proper; trivial.
   Qed.

   Instance aecu_Default_proper h c env :
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANDefault.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Default_proper; trivial.
   Qed.
   
   Instance aecu_Either_proper h c env :
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANEither.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_Either_proper; trivial.
   Qed.

   Instance aecu_EitherConcat_proper h c env :
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANEitherConcat.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_EitherConcat_proper; trivial.
   Qed.

   Instance aecu_App_proper h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) :
     Proper
       (algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env ==>
                        algenv_ctxt_equiv_under h c env) CANApp.
   Proof.
     unfold Proper, respectful, algenv_ctxt_equiv_under.
     intros; subst.
     autorewrite with aec_substs; simpl.
     specialize (H ps); specialize (H0 ps).
     do 2 (match_destr_in H; match_destr_in H0).
     apply aeu_App_proper; trivial.
   Qed.

 Lemma aec_substs_under_prop_part2 h c env (dn_c:Forall (fun x => data_normalized h (snd x)) c) (dn_env:data_normalized h env) e ps1 ps2 :
     Forall2 (fun xy1 xy2 => (fst xy1) = (fst xy2)
            /\ algenv_eq_under h c env (snd xy1) (snd xy2)) ps1 ps2
     -> algenv_ctxt_equiv_under
          h c env
          (aec_substs (lift_alg_context e) ps1)
          (aec_substs (lift_alg_context e) ps2).
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
           (fun xy1 xy2 : nat * algenv =>
            fst xy1 = fst xy2 /\ algenv_eq_under h c env (snd xy1) (snd xy2))
           (map
              (fun x : nat * algenv =>
               (fst x,
               (algenv_of_alg (alg_of_algenv (snd x))
                ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[| ("PCONST", ‵(drec (rec_sort c)))|] ⊕ ‵[| ("PDATA", ID)|])))%algenv))
              ps) ps.
   Proof.
     induction ps; simpl; trivial.
     - constructor; auto 2.
       simpl. split; trivial.
       apply roundtrip_env; trivial.
   Qed.

   Global Instance lift_alg_context_proper : Proper (alg_ctxt_equiv alg_eq ==> algenv_ctxt_equiv algenv_eq) lift_alg_context.
  Proof.
    unfold Proper, respectful.
    intros c1 c2 H.
    apply <- algenv_ctxt_equiv_strict_equiv.

    red; intros ps Hsort Hequiv.
    match_case; match_case; intros.
    red; intros h c dnc env dnenv d dnd.
    specialize (H (map (fun xy => (fst xy,
                                   (AApp (alg_of_algenv (snd xy)) (make_fixed_pat_context_data (drec (rec_sort c)) env)))) ps)).
    
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
       generalize (ac_holes_saturated_subst (fun x => (alg_of_algenv x ◯ make_fixed_pat_context_data (drec (rec_sort c)) env)%alg) c1 ps c1incl);
         intros c1nholes.
       generalize (ac_holes_saturated_subst (fun x => (alg_of_algenv x ◯ make_fixed_pat_context_data (drec (rec_sort c)) env)%alg) c2 ps c2incl);
         intros c2nholes.
       destruct (ac_simplify_nholes _ c1nholes) as [c1s c1seq].
       destruct (ac_simplify_nholes _ c2nholes) as [c2s c2seq].
       generalize (aec_simplify_lift_commute (ac_substs c1
             (map
                (fun xy : nat * algenv =>
                   (fst xy, AApp (alg_of_algenv (snd xy)) (make_fixed_pat_context_data (drec (rec_sort c)) env))) ps)));
        intros leq1.
      generalize (aec_simplify_lift_commute (ac_substs c2
             (map
                (fun xy : nat * algenv =>
                   (fst xy, AApp (alg_of_algenv (snd xy)) (make_fixed_pat_context_data (drec (rec_sort c)) env))) ps)));
        intros leq2.
      rewrite lift_alg_context_substs in leq1, leq2.
      rewrite map_map in leq1, leq2. simpl in leq1, leq2.
      rewrite c1seq, c2seq in *.
      intros.
      generalize
        (aec_substs_under_prop_part2 h c env dnc dnenv c1
                                     (map (fun x => (fst x, 
                                     ((algenv_of_alg (alg_of_algenv (snd x)))
                                        ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[| ("PCONST", ‵((drec (rec_sort c))))|] ⊕ ‵[| ("PDATA", ID)|])))%algenv)) ps) ps (f2_roundtrip _ _ _ _ dnc dnenv)); intros s1eq.

      generalize
        (aec_substs_under_prop_part2 h c env dnc dnenv c2
                                     (map (fun x => (fst x, 
                                     ((algenv_of_alg (alg_of_algenv (snd x)))
                                        ◯ (‵[| ("PBIND", ‵(env))|] ⊕ (‵[| ("PCONST", ‵((drec (rec_sort c))))|]⊕ ‵[| ("PDATA", ID)|])))%algenv)) ps) ps (f2_roundtrip _ _ _ _ dnc dnenv)); intros s2eq.
      simpl in s1eq, s2eq.
      simpl in *.
      specialize (s1eq nil); specialize (s2eq nil).
      simpl in s1eq, s2eq.
      rewrite leq1, H1 in s1eq.
      rewrite leq2, H0 in s2eq.
      assert (cseq: ((algenv_of_alg c1s) ≡ₑ (algenv_of_alg c2s))%algenv).
      { apply algenv_of_alg_proper. trivial. }
      rewrite <- algenv_eq_under_equiv in cseq.
      specialize (cseq h c env).
      rewrite s1eq, s2eq in cseq.
      red in cseq.
      apply cseq; auto.
  Qed.

  Global Instance lift_alg_context_strict_proper : Proper (alg_ctxt_equiv_strict alg_eq ==> algenv_ctxt_equiv_strict algenv_eq) lift_alg_context.
  Proof.
    unfold Proper, respectful.
    intros c1 c2 H.
    apply algenv_ctxt_equiv_strict_equiv.
    apply alg_ctxt_equiv_strict_equiv in H.
    apply lift_alg_context_proper; trivial.
  Qed.

  Local Open Scope alg_ctxt.
  Local Open Scope algenv_ctxt.

  (** This is just a restatement of lift_alg_context_proper
        which visually looks more like the paper version.
        For the mechanization, lift_alg_context_proper 
        is nicer, since it explicitly states that lift_alg_context
        is a morphism between the two equivalences
        and registers that relationship with the rewriting infrastructure
        of Coq.
   *)
  Theorem contextual_equivalence_lifting (c₁ c₂:alg_ctxt) :
    c₁ ≡ₐ c₂ -> lift_alg_context c₁ ≡ₑ lift_alg_context c₂.
  Proof.
    apply lift_alg_context_proper.
  Qed.

End RAlgEnvContext.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
