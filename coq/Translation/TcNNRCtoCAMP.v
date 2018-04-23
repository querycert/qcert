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
Require Import Decidable.
Require Import EquivDec.
Require Import Permutation.
Require Import EquivDec.
Require Import Eqdep_dec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import cNNRCSystem.
Require Import CAMPSystem.
Require Import cNNRCtoCAMP.
  
Section TcNNRCtoCAMP.

  (** Auxiliary definitions and lemmas *)
  Context {m:basic_model}.

  Local Open Scope camp_scope.

  Lemma  PTdot {τc} {Γ Γ₁:tbindings} {τ₁ τ₂ p k} (s:string) pf :
    NoDup (domain Γ₁) ->
    Assoc.lookup equiv_dec Γ₁ s = Some τ₁ ->
    [τc&Γ] |= p ; τ₁ ~> τ₂ ->
    [τc&Γ] |= pdot (loop_var s) p ; (Rec k (nnrc_to_camp_env Γ₁) pf) ~> τ₂.
  Proof.
    Hint Constructors camp_type.
    unfold pdot; intros.
    eapply PTletIt; eauto.
    eapply PTunop; eauto.
    constructor.
    rewrite <- env_lookup_edot; eauto.
  Qed.

  Hint Resolve merge_bindings_nil_r.
  Hint Resolve PTdot.

  Hint Resolve sorted_rec_nil.
  Hint Constructors camp_type.

  Lemma wf_env_same_domain {env tenv} v :
    bindings_type env tenv -> (In v (domain env) <-> In v (domain tenv)).
  Proof.
    unfold bindings_type; revert tenv v.
    induction env; simpl; inversion 1; subst; simpl; intuition; subst;
     intuition.
    - destruct (IHenv _ v H4); intuition.
    - destruct (IHenv _ v H4); intuition.
  Qed.

  Lemma loop_var_in_nnrc_to_camp_env {B} {tenv v} :
         In v (@domain _ B tenv) <->
         In (loop_var v) (domain (nnrc_to_camp_env tenv)).
  Proof.
    unfold nnrc_to_camp_env. unfold domain. 
    rewrite map_map; simpl.
    repeat rewrite in_map_iff.
    intuition.
    - destruct H as [?[??]]; subst; eauto.
    - destruct H as [?[??]]. 
      apply loop_var_inj in H; subst.
      eauto.
  Qed.

  (* TODO: redundant *)
  Lemma nnrc_to_camp_in {B} Γ v :
    In v (@domain _ B Γ) <->
    In (loop_var v) (domain (nnrc_to_camp_env Γ)).
  Proof.
    apply loop_var_in_nnrc_to_camp_env.
 Qed.

  Lemma nnrc_to_camp_nodup {B} Γ : 
    NoDup (@domain _ B Γ) <-> 
    NoDup (domain (nnrc_to_camp_env Γ)).
  Proof.
    Hint Constructors NoDup.
    unfold nnrc_to_camp_env, domain.
    rewrite map_map; simpl.
    induction Γ; simpl; intuition.
    - inversion H1; subst.
      econstructor; eauto.
      simpl. rewrite in_map_iff in H4 |- *.
      destruct 1 as [?[eqs ?]].
      apply loop_var_inj in eqs; subst.
      eauto.
    -  inversion H1; subst.
       econstructor; eauto.
       simpl. rewrite in_map_iff in H4 |- *.
       destruct 1 as [?[eqs ?]]; subst.
       eauto.
  Qed.

  Hint Constructors unary_op_type binary_op_type data_type.

  Lemma is_list_sorted_nnrc_to_camp_env_nodup {B} {tenv} :
    is_list_sorted ODT_lt_dec (@domain _ B (nnrc_to_camp_env tenv)) = true ->
    NoDup (domain tenv).
  Proof.
    intros.
    rewrite nnrc_to_camp_nodup.
    eapply is_list_sorted_NoDup; eauto.
    eapply StringOrder.lt_strorder.
  Qed.

  Hint Resolve is_list_sorted_nnrc_to_camp_env_nodup.

  (* TODO: move to Assoc *)
  Lemma lookup_incl_perm_nodup {A B} {dec:EqDec A eq} {l1 l2:list (A*B)} :
    Permutation l1 l2 ->
    NoDup (@domain A B l1) ->
    lookup_incl l1 l2.
  Proof.
    intros perm nd x y leqq.
    eapply lookup_some_nodup_perm; eauto.
  Qed.

  Lemma lookup_equiv_perm_nodup {A B} {dec:EqDec A eq} {l1 l2:list (A*B)} :
    Permutation l1 l2 ->
    NoDup (@domain A B l1) ->
    lookup_equiv l1 l2.
  Proof.
    intros.
    apply lookup_incl_part; repeat red; split.
    - apply lookup_incl_perm_nodup; trivial.
    - apply lookup_incl_perm_nodup; trivial.
      + symmetry; trivial.
      + rewrite <- H; trivial.
  Qed.

  Lemma nnrc_core_type_context_perm {Γ Γ'} τc τ n :
    Permutation Γ Γ' ->
    NoDup (domain Γ) ->
    shadow_free n = true ->
    (forall x, In x (domain Γ) -> ~ In x (nnrc_bound_vars n)) ->
    nnrc_core_type τc Γ n τ ->
    nnrc_core_type τc Γ' n τ.
  Proof.
    revert Γ Γ' τ.
    induction n; simpl; intros; inversion H3; subst; intros; repeat rewrite andb_true_iff in *; intuition.
    - econstructor; eauto.
    - econstructor; eauto. rewrite <- (lookup_equiv_perm_nodup H); trivial.
    - econstructor; eauto.
    - apply in_in_app_false in H2. intuition. econstructor; eauto.
    - econstructor; eauto.
    - apply in_in_cons_app_false in H2.  intuition.
      econstructor; eauto.
      eapply IHn2; [idtac| | | | eauto]; eauto.
      + econstructor; eauto.
      + simpl. intuition. subst. 
         destruct (in_dec string_eqdec x (nnrc_bound_vars n2)); 
          intuition.
         eauto.
    - apply in_in_cons_app_false in H2.  intuition.
      econstructor; eauto.
      eapply IHn2; [idtac| | | | eauto]; eauto.
      + econstructor; eauto.
      + simpl. intuition. subst. 
         destruct (in_dec string_eqdec x (nnrc_bound_vars n2)); 
          intuition.
          eauto.
    - apply in_in_app_false in H2; intuition.
      apply in_in_app_false in H7; intuition.
      econstructor; eauto.
    - apply in_in_cons_cons_app_app_false in H2.
      match_destr_in H1.
      match_destr_in H8.
      destruct H2 as [?[?[?[??]]]].
      econstructor; eauto 2.
      + eapply IHn2; try eapply H12; eauto 2.
        * constructor; trivial.
        * simpl. intros ? [?|?] inn2.
          subst; intuition.
          eauto.
      + eapply IHn3; try eapply H13; eauto 2.
        * constructor; trivial.
        * simpl. intros ? [?|?] inn2.
          subst; intuition.
          eauto.
  Qed.

  Lemma rec_cons_sort_nnrc_to_camp_env_pullback {A} a b Γ :
    NoDup (a :: domain Γ) ->
      exists Γ' : list (string*A),
     insertion_sort_insert rec_field_lt_dec (loop_var a, b)
       (nnrc_to_camp_env Γ) = nnrc_to_camp_env Γ' /\
     Permutation ((a, b) :: Γ) Γ'.
  Proof.
    revert a b. induction Γ; simpl; intros.
    - exists ((a,b)::nil); simpl; eauto.
    - destruct (StringOrder.lt_dec (loop_var a0) (loop_var (fst a))).
      + exists ((a0, b) :: a :: Γ); intuition.
      + destruct (StringOrder.lt_dec (loop_var (fst a)) (loop_var a0)).
         * inversion H; subst.
           destruct (IHΓ a0 b) as [?[??]]; trivial.
           simpl in H2.
           inversion H3; subst; econstructor; eauto.
            rewrite H0.
            exists (a::x); simpl; intuition.
            rewrite <- H1.
            apply perm_swap.
         * destruct (StringOrder.trichotemy (loop_var a0) (loop_var (fst a))); intuition.
           apply loop_var_inj in b0.
           subst.
           inversion H; subst; simpl in *; intuition.
  Qed.

  Lemma rec_sort_nnrc_to_camp_env_pullback {A} (Γ:list (string*A)) :
    NoDup (domain Γ) ->
    exists Γ',
      rec_sort (nnrc_to_camp_env Γ) = nnrc_to_camp_env Γ'
      /\ Permutation Γ Γ'.
  Proof.
    induction Γ; simpl.
    - exists (@nil (string*A)); intuition.
    - inversion 1; subst; destruct IHΓ; intuition.
      rewrite H1.
      destruct (rec_cons_sort_nnrc_to_camp_env_pullback ((fst a)) (snd a) x); intuition.
      rewrite <- H4; trivial.
      rewrite <- H4 in H6.
      exists x0. destruct a; simpl in *; intuition.
  Qed.

  Lemma fresh_bindings_some {A} `{EqDec A eq} (g g1 g2:list (string*A)) :
         Some g = merge_bindings g1 g2 <->
         Compat.compatible g1 g2 = true /\
         g = rec_concat_sort g1 g2.
  Proof.
    unfold merge_bindings.
    destruct (Compat.compatible g1 g2); simpl; intuition; congruence.
  Qed.

 Ltac t :=  match goal with 
           | [H:(_, _) = (_, _) |- _ ] => inversion H; clear H
           | [H:Coll _ = Coll _ |- _ ] => inversion H; clear H
           | [H: context [merge_bindings _ nil] |- _] => 
             rewrite merge_bindings_nil_r in H
           | [|- context [merge_bindings _ nil]] => 
             rewrite merge_bindings_nil_r
           | [H:context [@rec_concat_sort _ ?g nil] |- _] =>
             rewrite rec_concat_sort_nil_r in H
           | [H:context [@rec_concat_sort _ nil ?g] |- _] =>
             rewrite rec_concat_sort_nil_l in H
           | [H:Some _ = Some _ |- _] => 
             inversion H; clear H
           | [H1: is_list_sorted ?dec ?l = true,
            H2: is_list_sorted ?dec ?l = true |- _] =>
             generalize (is_list_sorted_ext dec _ H1 H2);
             let HH := fresh "eqisl" in
             intro HH; destruct HH; clear H2
           | [H: [_&_] |= lookup (loop_var _); _ ~> _ |- _] =>
             inversion H; subst; clear H
           | [H:[_ & _] |= loop_var _ ↓ …; _ ~> _ |- _] =>
             inversion H; subst; clear H
           | [H: [_ & _] |= punop _ _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pbinop _ _ _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pletIt _ _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= penv ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pleft ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pright ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pconst _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pvar _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pgetConstant _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= porElse _ _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= passert _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H: [_ & _] |= pand _ _ ; _ ~> _ |- _] =>
                  inversion H; subst; clear H
           | [H1: [?τc & ?b] |= mapall _; _ ~> _,
              H2: is_list_sorted ODT_lt_dec (domain ?b) = true |- _] =>
             apply (PTmapall_inv τc H2) in  H1;
               destruct H1 as [? [? [? [??]]]]; subst 
           | [H1: [?τc & ?b] |= mapall _; _ ~> _,
              H2: is_list_sorted StringOrder.lt_dec (domain ?b) = true |- _] =>
             apply (PTmapall_inv τc H2) in  H1;
               destruct H1 as [? [? [? [??]]]]; subst 
           | [H: [_ & _] |= pletEnv _ _; _ ~> _ |- _] => 
             inversion H; try subst; clear H

           | [H:unary_op_type _ _ _ |- _] => 
             inversion H; subst; clear H
(*           | [H:binary_op_type _ _ _ _ |- _] => 
             inversion H; subst; clear H
*)
           | [H: camp_type ?c ?g pit ?t1 ?t2 |- _] => 
           match t1 with
             |  t2 => clear H
             | _ => inversion H; try subst
           end

          | [H: context [nil = map 
                               (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x, ` (snd x))) _] |- _] => symmetry in H
          | [H: context [map 
                               (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x, ` (snd x))) _ = nil] |- _] => apply map_eq_nil in H

          | [H: context [(_::nil) = map 
                               (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x, ` (snd x))) _] |- _] => symmetry in H

          | [H: context [map 
                               (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x, ` (snd x))) _ = (_::nil) ] |- _] => apply map_eq_cons in H;
      destruct H as [? [? [? [??]]]]
       end; try rtype_equalizer; try subst; try t.

 Ltac defresh :=   
   match goal with
       | [H:Some ?g = merge_bindings _ _ |- _ ] => 
             apply fresh_bindings_some in H; destruct H; subst g
   end.

 Ltac simpt := 
      repeat progress (
               repeat rewrite map_app in *;
               repeat rewrite andb_true_iff in *;
        repeat match goal with
          | [H: context [match ?x with
                  | left _ => false
                  | right _ => true
                end]
                            |- _] => destruct x; [discriminate|idtac] 
          | [H: ~ In _ (_ ++ _) |- _ ] => rewrite nin_app_or in H
          | [H: In _ (_ ++ _) -> False |- _ ] => apply nin_app_or in H
          | [H: forall _, In _ (domain _) -> _ |- _] =>
               apply in_in_app_false in H 
            || apply in_in_cons_app_false in H
            || apply in_in_cons_cons_app_app_false in H
        end; intuition).

   (** Proving ``forwards'' type preservation: if the compiled pattern is 
        well-typed, then the source nnrc is well-typed (with the same type) *)
  Lemma nnrc_to_camp_ns_type_preserve n τc Γ τout :
    is_list_sorted ODT_lt_dec (domain (nnrc_to_camp_env Γ)) = true ->
    shadow_free n = true ->
    (forall x, In x (domain Γ) -> ~ In x (nnrc_bound_vars n)) ->
    nnrc_core_type τc Γ n τout ->
    forall τ₀,
      [τc&(nnrc_to_camp_env Γ)] |= (nnrcToCamp_ns n) ; τ₀ ~> τout.
  Proof.
    revert Γ τout; induction n; intros;
      inversion H2; subst; try solve [econstructor; eauto 3].
    - simpl in H0, H1. simpt; econstructor; eauto.
    - simpl. 
      simpl in H, H0, H1. simpt. 
      econstructor; eauto.
      eapply PTletEnv.
      + econstructor; eauto. 
      + rewrite merge_bindings_single_nin; eauto.
        rewrite <- loop_var_in_nnrc_to_camp_env; intuition.
      + rewrite rec_concat_sort_concats.
        assert (perm:Permutation 
                       ((loop_var v, τ₁) :: nnrc_to_camp_env Γ)
                       (nnrc_to_camp_env Γ ++ [(loop_var v, τ₁)]))
          by (rewrite Permutation_cons_append; trivial).
        assert (nd:NoDup (domain ((loop_var v, τ₁) :: nnrc_to_camp_env Γ))).
        * simpl. constructor.
          rewrite <- nnrc_to_camp_in; trivial.
          apply -> (@nnrc_to_camp_nodup rtype); auto.
        * rewrite <- (drec_sort_perm_eq _ _ nd perm).
          replace ((loop_var v, τ₁) :: nnrc_to_camp_env Γ) 
          with (nnrc_to_camp_env ((v, τ₁) :: Γ)) by reflexivity.
          destruct (rec_sort_nnrc_to_camp_env_pullback ((v, τ₁) :: Γ)) 
            as [Γ' [eq' perm']].
          apply nnrc_to_camp_nodup; auto.
          rewrite eq'.
          destruct (in_dec string_eqdec v (nnrc_bound_vars n2)); intuition.
          eapply IHn2; eauto.
          rewrite <- eq'. eauto.
          intros.
          apply nnrc_to_camp_in in H5.
          rewrite <- eq' in H5.
          apply drec_sort_domain in H5.
          apply loop_var_in_nnrc_to_camp_env in H5.
          simpl in H5; intuition; subst; [intuition|eauto].
          apply (nnrc_core_type_context_perm _ _ _ perm'); auto.
          apply nnrc_to_camp_nodup; auto.
          simpl; intuition; [idtac|eauto].
          subst;
            destruct (in_dec string_eqdec x (nnrc_bound_vars n2)); 
            intuition.
    - simpl.
      simpl in H, H0, H1. simpt. 
      econstructor; eauto.
      eapply PTmapall; eauto.
      eapply PTletEnv.
      + econstructor; eauto. 
      + rewrite merge_bindings_single_nin; eauto.
         rewrite <- loop_var_in_nnrc_to_camp_env; intuition.
      + rewrite rec_concat_sort_concats.
        assert (perm:Permutation 
                       ((loop_var v, τ₁) :: nnrc_to_camp_env Γ)
                       (nnrc_to_camp_env Γ ++ [(loop_var v, τ₁)]))
          by (rewrite Permutation_cons_append; trivial).
        assert (nd:NoDup (domain ((loop_var v, τ₁) :: nnrc_to_camp_env Γ))).
        * simpl. constructor.
          rewrite <- nnrc_to_camp_in; trivial.
          apply -> (@nnrc_to_camp_nodup rtype); auto.
        * rewrite <- (drec_sort_perm_eq _ _ nd perm).
          replace ((loop_var v, τ₁) :: nnrc_to_camp_env Γ) 
          with (nnrc_to_camp_env ((v, τ₁) :: Γ)) by reflexivity.
          destruct (rec_sort_nnrc_to_camp_env_pullback ((v, τ₁) :: Γ)) 
            as [Γ' [eq' perm']].
          apply nnrc_to_camp_nodup; auto.
          rewrite eq'.
          destruct (in_dec string_eqdec v (nnrc_bound_vars n2)); intuition.
          eapply IHn2; eauto.
          rewrite <- eq'.
          eauto.
          intros.
          apply nnrc_to_camp_in in H5.
          rewrite <- eq' in H5.
          apply drec_sort_domain in H5.
          apply loop_var_in_nnrc_to_camp_env in H5.
          simpl in H5; intuition; subst; [intuition|eauto].
          apply (nnrc_core_type_context_perm _ _ _ perm'); auto.
          apply nnrc_to_camp_nodup; auto.
          simpl; intuition; [idtac|eauto].
          subst;
            destruct (in_dec string_eqdec x (nnrc_bound_vars n2)); 
            intuition.
    - simpl in H0, H1, H2. simpt. 
      eapply PTorElse.
      + eapply PTletEnv.
        * eapply PTassert.
          eapply PTbinop; eauto.
          econstructor; simpl; eauto.
        * rewrite merge_bindings_nil_r. reflexivity.
        * eapply camp_type_tenv_rec; eauto.
      + eapply PTletEnv.
        * eapply PTassert.
          eapply PTunop; eauto.
        * rewrite merge_bindings_nil_r. reflexivity.
        * eapply camp_type_tenv_rec; eauto.
    - simpl in *.
      apply in_in_cons_cons_app_app_false in H1.
      destruct H1 as [?[?[?[??]]]].
      repeat rewrite andb_true_iff in H0; destruct H0 as [[[[??]?]?]?].
      match_destr_in H0. match_destr_in H7.
      eapply PTletIt; [eauto | ].
      eapply PTorElse.
      + eapply PTletIt; [eauto | ].
        eapply PTletEnv.
        * repeat econstructor.
        * rewrite merge_bindings_single_nin. reflexivity.
          rewrite <- loop_var_in_nnrc_to_camp_env.
          trivial.
        * assert (nd:NoDup (domain ((loop_var v, τl) :: nnrc_to_camp_env Γ))).
          simpl; constructor.
          rewrite <- loop_var_in_nnrc_to_camp_env; trivial.
          apply -> (@nnrc_to_camp_nodup rtype); auto.
          assert (perm:Permutation 
                         ((loop_var v, τl) :: nnrc_to_camp_env Γ)
                         (nnrc_to_camp_env Γ ++ [(loop_var v, τl)]))
            by (rewrite Permutation_cons_append; trivial).
          unfold rec_concat_sort; rewrite <- (drec_sort_perm_eq _ _ nd perm).
          replace ((loop_var v, τl) :: nnrc_to_camp_env Γ) 
          with (nnrc_to_camp_env ((v, τl) :: Γ)) by reflexivity.
          destruct (rec_sort_nnrc_to_camp_env_pullback ((v, τl) :: Γ)) 
            as [Γ' [eq' perm']].
          apply nnrc_to_camp_nodup. auto.
          rewrite eq'.
          apply IHn2; trivial.
          rewrite <- eq'; eauto; reflexivity.
          intros ? inn.
          symmetry in perm'.
          generalize (Permutation_in _ (dom_perm _ _ perm') inn); simpl; intros [inn'|inn']; subst; eauto.
          apply (nnrc_core_type_context_perm _ _ _ perm'); trivial.
          simpl.
          constructor; auto.
          simpl.
          intros ? [?|?]; subst; eauto.
      + eapply PTletIt; [eauto | ].
        eapply PTletEnv.
        * repeat econstructor.
        * rewrite merge_bindings_single_nin. reflexivity.
          rewrite <- loop_var_in_nnrc_to_camp_env.
          trivial.
        * unfold rec_concat_sort.
          assert (nd:NoDup (domain ((loop_var v0, τr) :: nnrc_to_camp_env Γ))).
          simpl; constructor.
          rewrite <- loop_var_in_nnrc_to_camp_env; trivial.
          apply -> (@nnrc_to_camp_nodup rtype); auto.
          assert (perm:Permutation 
                         ((loop_var v0, τr) :: nnrc_to_camp_env Γ)
                         (nnrc_to_camp_env Γ ++ [(loop_var v0, τr)]))
            by (rewrite Permutation_cons_append; trivial).
          rewrite <- (drec_sort_perm_eq _ _ nd perm).
          replace ((loop_var v0, τr) :: nnrc_to_camp_env Γ) 
          with (nnrc_to_camp_env ((v0, τr) :: Γ)) by reflexivity.
          destruct (rec_sort_nnrc_to_camp_env_pullback ((v0, τr) :: Γ)) 
            as [Γ' [eq' perm']].
          apply nnrc_to_camp_nodup; auto.
          rewrite eq'.
          apply IHn3; trivial.
          rewrite <- eq'; eauto; reflexivity.
          intros ? inn.
          symmetry in perm'.
          generalize (Permutation_in _ (dom_perm _ _ perm') inn); simpl; intros [inn'|inn']; subst; eauto.
          apply (nnrc_core_type_context_perm _ _ _ perm'); trivial.
          simpl; constructor; auto.
          simpl.
          intros ? [?|?]; subst; eauto.
          Grab Existential Variables.
          eauto. eauto. eauto. eauto.
          eauto. eauto. eauto.
  Qed.

  Lemma nnrc_to_camp_ns_top_type_preserve n τc τout :
    shadow_free n = true ->
    nnrc_core_type τc nil n τout ->
    forall τ₀,
      [τc&nil] |= (nnrcToCamp_ns n) ; τ₀ ~> τout.
  Proof.
    intros.
    apply (nnrc_to_camp_ns_type_preserve n τc nil); eauto.
  Qed.

  Lemma nnrc_to_camp_type_preserve n τc Γ τout :
    is_list_sorted ODT_lt_dec (domain (nnrc_to_camp_env Γ)) = true ->
    nnrc_core_type τc Γ n τout ->
    forall τ₀,
      [τc&(nnrc_to_camp_env Γ)] |= (nnrcToCamp (domain Γ) n) ; τ₀ ~> τout.
  Proof.
    intros.
    apply nnrc_to_camp_ns_type_preserve; eauto.
    - apply unshadow_shadow_free.
    - apply unshadow_avoid.
    - apply nnrc_core_unshadow_type; trivial.
  Qed.

  Hint Rewrite 
     fresh_bindings_pbinop 
     fresh_bindings_punop 
     fresh_bindings_pletIt
     fresh_bindings_pmap 
     fresh_bindings_mapall
     fresh_bindings_pletEnv
     fresh_bindings_pvar
     fresh_bindings_porElse
     fresh_bindings_passert
     fresh_bindings_pand
     fresh_bindings_plookup
     @fresh_bindings_domain_drec_sort
     fresh_bindings_app
     fresh_bindings_cons
     fresh_bindings_nil
     @domain_app 
  : fresh_bindings.

  Hint Resolve StringOrder.lt_strorder.
  Hint Resolve is_list_sorted_NoDup.

  Hint Rewrite 
       @rec_concat_sort_concats 
       @in_dom_rec_sort
       @domain_app
       in_app_iff : simpr.

  Lemma fresh_bindings_cons_loop_var a l p :
    fresh_bindings ((loop_var a)::l) p
    <-> fresh_bindings l p.
  Proof.
    unfold fresh_bindings; simpl; intuition; eauto.
    eapply loop_let_var_distinct; eauto.
  Qed.

  Hint Rewrite fresh_bindings_cons_loop_var : fresh_bindings.

  Lemma nnrcToCamp_ns_type_ignored_let_binding τc b x xv τ₁ τ₂ n :
    nnrcIsCore n ->
    shadow_free n = true ->
    is_list_sorted ODT_lt_dec (domain b) = true ->
    fresh_bindings (domain b) (nnrcToCamp_ns n) ->
    (forall x, In x (domain b) -> ~ In x (map loop_var (nnrc_bound_vars n))) ->
    NoDup (domain b) ->
    ~ In (let_var x) (let_vars (nnrcToCamp_ns n)) ->
    ~ In (let_var x) (domain b) ->
    ([τc&b] |= (nnrcToCamp_ns n) ; τ₁ ~> τ₂) ->
    [τc&(rec_concat_sort b ((let_var x, xv)::nil))] |= (nnrcToCamp_ns n) ; τ₁ ~> τ₂.
  Proof.
    Hint Resolve loop_let_var_distinct.
    Hint Resolve rec_concat_sort_sorted.
    intro Hiscore.
    revert Hiscore b x xv τ₁ τ₂.
    induction n; intros; trivial; simpl in H1;
    try autorewrite with fresh_bindings in H1;
    simpt.
    - simpl in *. t. econstructor; eauto.
    - simpl in *.
      t.
      repeat econstructor; eauto.
      rewrite tdot_rec_concat_sort_neq; [idtac|eauto].
      rewrite sort_sorted_is_id; eauto.
    - simpl in *; t; eauto.
    - simpl in *; simpt;  t; eauto.
    - simpl in *.
      inversion H6; subst.
      econstructor; [idtac|eauto].
      intuition.
    - simpl in *.
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpt; t.
      econstructor; eauto.
      destruct x0; simpl in *. subst.
      econstructor.
      + econstructor; eauto.
      + rewrite merge_bindings_single_nin; [reflexivity|idtac].
        autorewrite with simpr.
        simpl; subst; intuition.
      + unfold rec_concat_sort.
        rewrite rec_sort_rec_sort_app1.
        assert (perm:Permutation
                       ((b ++ [(let_var x, xv)]) ++ [(loop_var v, s0)])
                       ((b ++ [(loop_var v, s0)]) ++ [(let_var x, xv)])).
        repeat rewrite app_ass. apply Permutation_app; eauto.
        apply perm_swap.
        erewrite drec_sort_perm_eq; try eapply perm.
        rewrite <- rec_sort_rec_sort_app1.
        eapply IHn2; eauto 2.
        * autorewrite with fresh_bindings.
          simpl.
          autorewrite with fresh_bindings.
          intuition.
        * intros ? inn1 inn2.
          apply drec_sort_domain in inn1.
          rewrite domain_app in inn1.
          rewrite in_app_iff in inn1; simpl in inn1.
          intuition.
          eapply H8; eauto.
          subst.
          apply in_map_iff in inn2.
          destruct inn2 as [? [? ?]].
          apply loop_var_inj in H11; subst. eauto.
        * intuition.
        * rewrite in_dom_rec_sort, domain_app, in_app_iff; simpl.
          intuition.
        * repeat defresh; trivial.
        * repeat rewrite domain_app. simpl.
          rewrite Permutation_app_comm; simpl.
          econstructor.
          rewrite in_app_iff; simpl. intuition.
          rewrite Permutation_app_comm; simpl.
          econstructor; eauto.
    - elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpl in *. simpt; t.
      econstructor; eauto.
      eapply PTmapall; eauto.
      destruct x0; simpl in *. subst.
      econstructor.
      + econstructor; eauto.
      + rewrite merge_bindings_single_nin; [reflexivity|idtac].
        autorewrite with simpr.
        simpl; subst; intuition.
      + unfold rec_concat_sort.
        rewrite rec_sort_rec_sort_app1.
        assert (perm:Permutation
                       ((b ++ [(let_var x, xv)]) ++ [(loop_var v, s0)])
                       ((b ++ [(loop_var v, s0)]) ++ [(let_var x, xv)])).
        repeat rewrite app_ass. apply Permutation_app; eauto.
        apply perm_swap.
        erewrite drec_sort_perm_eq; try eapply perm.
        rewrite <- rec_sort_rec_sort_app1.
        eapply IHn2; eauto 2.
        * autorewrite with fresh_bindings.
          simpl.
          autorewrite with fresh_bindings.
          intuition.
        * intros ? inn1 inn2.
          apply drec_sort_domain in inn1.
          rewrite domain_app in inn1.
          rewrite in_app_iff in inn1; simpl in inn1.
          intuition.
          eapply H8; eauto.
          subst.
          apply in_map_iff in inn2.
          destruct inn2 as [? [? ?]].
          apply loop_var_inj in H11; subst. eauto.
        * intuition.
        * rewrite in_dom_rec_sort, domain_app, in_app_iff; simpl.
          intuition.
        * repeat defresh; trivial.
        * repeat rewrite domain_app. simpl.
          rewrite Permutation_app_comm; simpl.
          econstructor.
          rewrite in_app_iff; simpl. intuition.
          rewrite Permutation_app_comm; simpl.
          econstructor; eauto.
    - simpl in *.
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpt; t.
      econstructor; eauto.
      + inversion H35; subst.
        econstructor. eauto.
        rewrite merge_bindings_nil_r.
        rewrite drec_sort_drec_sort_concat.
        reflexivity.
        apply IHn2; eauto.
        assert (rec_sort b = b) by (eapply rec_sorted_id; eauto).
        unfold rec_sort in *. rewrite <- H6; assumption.
      + inversion H35; subst.
        econstructor. eauto.
        rewrite merge_bindings_nil_r.
        rewrite drec_sort_drec_sort_concat.
        reflexivity.
        apply IHn3; eauto.
        assert (rec_sort b = b) by (eapply rec_sorted_id; eauto).
        unfold rec_sort in *. rewrite <- H6; assumption.
    - simpl in *.
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpt; simpl in *; simpt.
      inversion H6; clear H6; subst.
      inversion H30; clear H30; subst.
      inversion H26; clear H26; subst.
      inversion H28; clear H28; subst.
      inversion H31; clear H31; subst.
      inversion H26; clear H26; subst.
      rtype_equalizer. subst.
      inversion H32; clear H32; subst.
      inversion H25; clear H25; subst.
      inversion H29; clear H29; subst.
      inversion H34; clear H34; subst.
      inversion H30; clear H30; subst.
      inversion H25; clear H25; subst.
      inversion H30; clear H30; subst.
      inversion H36; clear H36; subst.
      destruct Γ'; try discriminate.
      destruct Γ'; try discriminate.
      inversion H26; clear H26; subst.
      destruct Γ'0; try discriminate.
      destruct Γ'0; try discriminate.
      inversion H29; clear H29; subst.
      destruct p; destruct p0. unfold fst in H23, H25, H26, H30.
      rtype_equalizer. subst.
      econstructor; [eauto | ].
      econstructor.
      + econstructor; [eauto | ]; simpl.
        econstructor.
        * simpl. repeat econstructor.
        * rewrite merge_bindings_single_nin; try reflexivity.
          unfold rec_concat_sort; rewrite in_dom_rec_sort.
          rewrite domain_app, in_app_iff. simpl.
          intros [?|[?|?]]; eauto.
        * unfold rec_concat_sort.
          rewrite rec_sort_rec_sort_app1.
          assert (perm:Permutation
                         ((b ++ [(let_var x, xv)]) ++ [(loop_var v, r)])
                         ((b ++ [(loop_var v, r)]) ++ [(let_var x, xv)]))
            by (repeat rewrite app_ass; apply Permutation_app; eauto;
                apply perm_swap).
          erewrite drec_sort_perm_eq; try eapply perm.
          rewrite <- rec_sort_rec_sort_app1.
          {eapply IHn2; trivial.
           - eapply (drec_sort_sorted (odt:=ODT_string)).
           - autorewrite with fresh_bindings; simpl; split; trivial.
             autorewrite with fresh_bindings; trivial.
           - intros ? inn; apply drec_sort_domain in inn.
             rewrite domain_app, in_app_iff in inn.
             simpl in inn.
             destruct inn as [?|[?|?]]; subst; eauto 2.
             rewrite in_map_iff. intros [?[injj inn]].
             apply loop_var_inj in injj; subst. eauto.
           - eapply is_list_sorted_NoDup_strlt.
             eapply rec_sort_sorted; eauto.
           - intros inn; apply drec_sort_domain in inn.
             rewrite domain_app, in_app_iff in inn.
             simpl in inn.
             destruct inn as [?|[?|?]]; subst; eauto 2.
           - unfold merge_bindings in H28.
             match_destr_in H28. inversion H28; subst.
             eauto.
          }
          repeat rewrite domain_app.
          rewrite Permutation_app_comm.
          { constructor.
            - simpl. rewrite in_app_iff; simpl.
              intros [?|[?|?]]; subst; eauto 2.
            - rewrite Permutation_app_comm.
              simpl.
              constructor; trivial.
          }
      + econstructor; [eauto | ]; simpl.
        econstructor.
        * simpl. repeat econstructor.
        * rewrite merge_bindings_single_nin; try reflexivity.
          unfold rec_concat_sort; rewrite in_dom_rec_sort.
          rewrite domain_app, in_app_iff. simpl.
          intros [?|[?|?]]; eauto.
          eelim loop_let_var_distinct; eauto.
        * unfold rec_concat_sort.
          rewrite rec_sort_rec_sort_app1.
          assert (perm:Permutation
                         ((b ++ [(let_var x, xv)]) ++ [(loop_var v0, r0)])
                         ((b ++ [(loop_var v0, r0)]) ++ [(let_var x, xv)]))
            by (repeat rewrite app_ass; apply Permutation_app; eauto;
                apply perm_swap).
          erewrite drec_sort_perm_eq; try eapply perm.
          rewrite <- rec_sort_rec_sort_app1.
          {eapply IHn3; trivial.
           - eapply (drec_sort_sorted (odt:=ODT_string)).
           - autorewrite with fresh_bindings; simpl; split; trivial.
             autorewrite with fresh_bindings; trivial.
           - intros ? inn; apply drec_sort_domain in inn.
             rewrite domain_app, in_app_iff in inn.
             simpl in inn.
             destruct inn as [?|[?|?]]; subst; eauto 2.
             rewrite in_map_iff. intros [?[injj inn]].
             apply loop_var_inj in injj; subst. eauto.
           - eapply is_list_sorted_NoDup_strlt.
             eapply rec_sort_sorted; eauto.
           - simpl in H24.
             intros inn; apply H24. right; eauto.
           - intros inn; apply drec_sort_domain in inn.
             rewrite domain_app, in_app_iff in inn.
             simpl in inn.
             destruct inn as [?|[?|?]]; subst; eauto 2.
             eapply loop_let_var_distinct; eauto.
           - unfold merge_bindings in H31.
             match_destr_in H31. inversion H31; subst.
             eauto.
          }
          repeat rewrite domain_app.
          rewrite Permutation_app_comm.
          { constructor.
            - simpl. rewrite in_app_iff; simpl.
              intros [?|[?|?]]; subst; eauto 2.
              eapply loop_let_var_distinct; eauto.
            - rewrite Permutation_app_comm.
              simpl.
              constructor; trivial.
          }
     Grab Existential Variables.
     eauto.
     eauto.
     eauto.
     eauto.
     eauto.
     eauto.
     eauto.
  Qed.

  Lemma nnrc_to_camp_ns_let_type_equiv n τc Γ τout :
    nnrcIsCore n ->
    is_list_sorted ODT_lt_dec (domain Γ) = true ->
    fresh_bindings (domain Γ) (nnrcToCamp_ns_let n) ->
    shadow_free n = true ->
    (forall x, In x (domain Γ) -> ~ In x (map loop_var (nnrc_bound_vars n))) ->
    forall τ₀,
      [τc&Γ] |= (nnrcToCamp_ns n) ; τ₀ ~> τout ->
                                   [τc&Γ] |= (nnrcToCamp_ns_let n) ; τ₀ ~> τout.
  Proof.
    intro Hiscore.
    revert Hiscore Γ τout.
    induction n; simpl; intros Hiscore Γ τout issort freshb shf ninb τ₀;
    inversion 1; subst;  simpl in freshb, shf, ninb;
    autorewrite with fresh_bindings in freshb;
    repeat rewrite andb_true_iff in *.
    - eauto.
    - eauto.
    - eauto.
    - rewrite map_app in ninb; apply in_in_app_false in ninb; intuition; eauto.
    - intuition; eauto.
    - simpl in Hiscore; elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      rewrite map_app in ninb; apply in_in_cons_app_false in ninb; intuition.
      destruct (in_dec string_eqdec v (nnrc_bound_vars n2)); [discriminate|idtac].
      t.
      destruct x; destruct x0; simpl in *.
      subst.
      econstructor; eauto.
      econstructor.
      + econstructor; eauto.
      + eassumption.
      + eapply IHn2; eauto.
         * intros ? inn1 inn2.
           repeat defresh.
           assert (inn1': In (let_var x) (domain (Γ ++ [(loop_var v, s0)])))
                  by (apply  drec_sort_equiv_domain; trivial).
           rewrite domain_app, in_app_iff in inn1'.
           simpl in inn1'; intuition; eauto.
           apply (H9 _ H7); trivial.
           eelim loop_let_var_distinct; eauto.
         * intros ? inn1 inn2.
            repeat defresh.
            assert (inn1': In x (domain (Γ ++ [(loop_var v, s0)])))
                  by (apply  drec_sort_equiv_domain; trivial).
            rewrite domain_app, in_app_iff in inn1'.
            simpl in inn1'; intuition; eauto.
            subst. apply n. apply in_map_iff in inn2.
           destruct inn2 as [?[HH ?]].
           apply loop_var_inj in HH. subst. trivial.
    - simpl in Hiscore; elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      rewrite map_app in ninb; apply in_in_cons_app_false in ninb; intuition.
      destruct (in_dec string_eqdec v (nnrc_bound_vars n2)); [discriminate|idtac].
      t.
      destruct x; destruct x0; simpl in *.
      subst.
      econstructor; eauto.
      econstructor.
      + econstructor; eauto.
         econstructor; eauto.
         econstructor.
         econstructor; eauto.
         eauto.
         inversion H15; subst.
         eapply IHn2; eauto 2.
         * unfold mapall_let in H1. 
            autorewrite with fresh_bindings in H1.
            intuition.
            repeat defresh.
            rewrite rec_concat_sort_concats,
                       fresh_bindings_domain_drec_sort,
                       domain_app,
                       fresh_bindings_app.
            simpl. intuition.
            unfold fresh_bindings; simpl. intuition.
            eapply loop_let_var_distinct; eauto.
         * intros ? inn1 inn2.
           repeat defresh.
           assert (inn1': In x (domain (Γ ++ [(loop_var v, s0)])))
             by (apply  drec_sort_equiv_domain; trivial).
           rewrite domain_app, in_app_iff in inn1'.
           simpl in inn1'; intuition; eauto.
           subst. apply n. apply in_map_iff in inn2.
           destruct inn2 as [?[HH ?]].
           apply loop_var_inj in HH. subst. trivial.
      + simpl.
        rewrite merge_bindings_single_nin; eauto.
        unfold mapall_let in H1.
        autorewrite with fresh_bindings in H1.
        intuition.
        eapply H1; eauto.
        rewrite fresh_let_var_as_let.
        reflexivity.
      + econstructor.
        * repeat econstructor; eauto.
          simpl.
          apply tdot_rec_concat_sort_eq.
          unfold mapall_let in H1. 
          autorewrite with fresh_bindings in H1.
          intuition.
          eapply H1; eauto.
          reflexivity.
        * rewrite merge_bindings_nil_r.
          rewrite drec_sort_drec_sort_concat.
          reflexivity.
        * repeat econstructor; eauto.
          apply tdot_rec_concat_sort_eq.
          unfold merge_bindings.
          unfold mapall_let in H1. 
          autorewrite with fresh_bindings in H1.
          intuition.
          eapply H1; eauto.
          reflexivity.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      repeat rewrite map_app in ninb.
      apply in_in_app_false in ninb; intuition.
      apply in_in_app_false in H7; intuition.
      t.
      rewrite sort_sorted_is_id in H24,H28,H33,H37 by eauto.
      econstructor.
      + eauto.
      + rewrite merge_bindings_single_nin.
        reflexivity.
        intro inn.
        eapply H8; eauto.
        reflexivity.
      + econstructor.
        * econstructor.
          econstructor; eauto.
          econstructor; eauto.
          econstructor; eauto.
          econstructor; eauto.
          econstructor; eauto.
          econstructor; eauto.
          inversion H32; clear H32; subst.
          inversion H41; clear H41; subst.
          apply tdot_rec_concat_sort_eq.
          intro inn.
          eapply H8; eauto.
          reflexivity.
          rewrite merge_bindings_nil_r.
          rewrite drec_sort_drec_sort_concat.
          reflexivity.
          eapply IHn2; eauto.
          
          rewrite
            rec_concat_sort_concats,
          fresh_bindings_domain_drec_sort,
          domain_app,
          fresh_bindings_app.
          simpl. intuition.
          unfold fresh_bindings.
          simpl.
          intros ? [inn|idtac]; [idtac|intuition].
          rewrite <- inn.
          intros inn2.
          apply (fresh_let_var_fresh "if$"
                                     (let_vars (nnrcToCamp_ns_let n1) ++
                                               let_vars (nnrcToCamp_ns_let n2) ++
                                               let_vars (nnrcToCamp_ns_let n3))).
          repeat rewrite in_app_iff. intuition.
          
          unfold rec_concat_sort.
          intros ? inn1 inn2.
          rewrite in_dom_rec_sort, domain_app, in_app_iff in inn1.
          simpl in inn1.
          intuition. eauto.
          subst. eapply in_map_iff in inn2.
          destruct inn2 as [? [eqq ?]].
          rewrite fresh_let_var_as_let in eqq.
          eapply loop_let_var_distinct; eauto.
          
          eapply nnrcToCamp_ns_type_ignored_let_binding; eauto.
          apply fresh_bindings_let_to_naive; trivial.
          
          intros inn. apply let_vars_let_to_naive in inn.
          apply (fresh_let_var_fresh "if$"
                                     (let_vars (nnrcToCamp_ns_let n1) ++
                                               let_vars (nnrcToCamp_ns_let n2) ++
                                               let_vars (nnrcToCamp_ns_let n3))).
          repeat rewrite in_app_iff. intuition.
          
          intros inn; eapply H8; eauto.
          reflexivity.
        * econstructor; [eauto|..].
          repeat (econstructor; eauto).
          inversion H41.
          apply tdot_rec_concat_sort_eq.
          intro inn.
          eapply H8; eauto.
          reflexivity.
          
          rewrite merge_bindings_nil_r.
          rewrite drec_sort_drec_sort_concat.
          reflexivity.
          eapply IHn3; eauto.
          
          unfold rec_concat_sort.
          rewrite fresh_bindings_domain_drec_sort,
          domain_app,
          fresh_bindings_app.
          simpl. intuition.
          unfold fresh_bindings.
          simpl.
          intros ? [inn|idtac]; [idtac|intuition].
          rewrite <- inn.
          intros inn2.
          apply (fresh_let_var_fresh "if$"
                                     (let_vars (nnrcToCamp_ns_let n1) ++
                                               let_vars (nnrcToCamp_ns_let n2) ++
                                               let_vars (nnrcToCamp_ns_let n3))).
          repeat rewrite in_app_iff. intuition.
          
          unfold rec_concat_sort.
          intros ? inn1 inn2.
          rewrite in_dom_rec_sort, domain_app, in_app_iff in inn1.
          simpl in inn1.
          intuition. eauto.
          subst. eapply in_map_iff in inn2.
          destruct inn2 as [? [eqq ?]].
          rewrite fresh_let_var_as_let in eqq.
          eapply loop_let_var_distinct; eauto.
          
          eapply nnrcToCamp_ns_type_ignored_let_binding; eauto.
          apply fresh_bindings_let_to_naive; trivial.
          
          intros inn. apply let_vars_let_to_naive in inn.
          apply (fresh_let_var_fresh "if$"
                                     (let_vars (nnrcToCamp_ns_let n1) ++
                                               let_vars (nnrcToCamp_ns_let n2) ++
                                               let_vars (nnrcToCamp_ns_let n3))).
          repeat rewrite in_app_iff. intuition.
          
          intros inn; eapply H8; eauto.
          reflexivity.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpt.
      inversion H6; clear H6; subst.
      inversion H22; clear H22; subst.
      inversion H21; clear H21; subst.
      inversion H26; clear H26; subst.
      inversion H20; clear H20; subst.
      inversion H23; clear H23; subst.
      inversion H28; clear H28; subst.
      destruct Γ'; try discriminate.
      destruct Γ'; try discriminate.
      destruct p.
      inversion H21; clear H21; rtype_equalizer.
      subst.
      inversion H25; clear H25; subst.
      inversion H26; clear H26; subst.
      inversion H21; clear H21; subst.
      rtype_equalizer. subst.
      inversion H20; clear H20; subst.
      inversion H23; clear H23; subst.
      inversion H28; clear H28; subst.
      destruct Γ'; try discriminate.
      destruct Γ'; try discriminate.
      destruct p.
      inversion H21; clear H21; rtype_equalizer.
      subst.
      econstructor; [eauto | ].
      econstructor.
      + econstructor; [eauto | ].
        econstructor.
        * repeat econstructor.
        * rewrite <- H22. reflexivity.
        * unfold merge_bindings in H22.
          match_case_in H22; intros comcamp;
          rewrite comcamp in H22; try discriminate.
          inversion H22; clear H22; subst.
          { apply IHn2; trivial.
            - unfold rec_concat_sort.
              autorewrite with fresh_bindings.
              simpl. autorewrite with fresh_bindings.
              auto.
            - unfold rec_concat_sort. intros ? inn.
              rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
              simpl in inn. destruct inn as [?|[?|?]]; subst; eauto.
              rewrite in_map_iff. intros [? [injj ?]]; apply loop_var_inj in injj.
              subst; eauto.
          } 
      + econstructor; [eauto | ].
        econstructor.
        * repeat econstructor.
        * rewrite <- H24. reflexivity.
        * unfold merge_bindings in H24.
          match_case_in H24; intros comcamp;
          rewrite comcamp in H24; try discriminate.
          inversion H24; clear H24; subst.
          { apply IHn3; trivial.
            - unfold rec_concat_sort.
              autorewrite with fresh_bindings.
              simpl. autorewrite with fresh_bindings.
              auto.
            - unfold rec_concat_sort; intros ? inn.
              rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
              simpl in inn. destruct inn as [?|[?|?]]; subst; eauto.
              rewrite in_map_iff. intros [? [injj ?]]; apply loop_var_inj in injj.
              subst; eauto.
          }
    - contradiction. (* GroupBy Case -- nnrcIsCore is False *)
      Grab Existential Variables.
      solve[eauto].
      solve[eauto].
      solve[eauto].
      solve[eauto].    
      solve[eauto].
      solve[eauto].
      solve[eauto].
      solve[eauto].
      solve[eauto].
      solve[eauto].
      solve[eauto].
      solve[eauto].
      solve[eauto].
  Qed.

  Lemma fresh_bindings_from_tnnrc {A} e l :
    fresh_bindings (@domain _ A (nnrc_to_camp_env e)) l.
  Proof.
    unfold fresh_bindings, nnrc_to_camp_env, domain.
    rewrite map_map. simpl. intros.
    apply in_map_iff in H.
    destruct H as [? [??]].
    apply loop_let_var_distinct in H.
    intuition.
  Qed.

  Lemma nnrc_to_camp_let_type_preserve n τc Γ τout :
    nnrcIsCore n ->
    is_list_sorted ODT_lt_dec (domain (nnrc_to_camp_env Γ)) = true ->
    nnrc_core_type τc Γ n τout ->
    forall τ₀,
      [τc&(nnrc_to_camp_env Γ)] |= (nnrcToCamp_let (domain Γ) n) ; τ₀ ~> τout.
  Proof.
    intros.
    apply nnrc_to_camp_ns_let_type_equiv; eauto.
    - apply unshadow_simpl_preserve_core.
      apply H.
    - apply fresh_bindings_from_tnnrc.
    - apply unshadow_shadow_free.
    - intros ? inn1 inn2.
      unfold nnrc_to_camp_env, domain in inn1.
      rewrite map_map, in_map_iff in inn1.
      destruct inn1 as [? [? inn1]]; subst.
      rewrite in_map_iff in inn2.
      destruct inn2 as [? [eqs inn2]]; subst; simpl in *.
      apply loop_var_inj in eqs; subst.
      destruct x0; simpl in *.
      revert inn2.
      apply unshadow_avoid.
      eapply in_dom; eauto.
    - apply nnrc_to_camp_ns_type_preserve; eauto.
    + apply unshadow_shadow_free.
    + apply unshadow_avoid.
    + apply nnrc_core_unshadow_type; trivial.
  Qed.

  Lemma nnrc_to_camp_ns_let_top_type_preserve n τc τout :
    nnrcIsCore n ->
    shadow_free n = true ->
    nnrc_core_type τc nil n τout ->
    forall τ₀,
    [τc&nil] |= (nnrcToCamp_ns_let n) ; τ₀ ~> τout.
  Proof.
    intros.
    apply nnrc_to_camp_ns_let_type_equiv; eauto.
    unfold fresh_bindings; simpl; intuition.
    apply nnrc_to_camp_ns_top_type_preserve; eauto.
  Qed.

  (** Proving ``backwards'' type preservation: if the compiled pattern is 
        well-typed, then the source nnrc is well-typed (with the same type) *)
  
  Lemma nnrc_to_camp_ns_type_preserve_back n τc Γ τout :
    nnrcIsCore n ->
    is_list_sorted ODT_lt_dec (domain (nnrc_to_camp_env Γ)) = true ->
    shadow_free n = true ->
    (forall x, In x (domain Γ) -> ~ In x (nnrc_bound_vars n)) ->
    forall τ₀,
      [τc&(nnrc_to_camp_env Γ)] |= (nnrcToCamp_ns n) ; τ₀ ~> τout ->
                                                     nnrc_core_type τc Γ n τout.
  Proof.
    intro Hiscore.
    revert Hiscore Γ τout; induction n; intros;
      inversion H2; subst.
    - econstructor; eauto.
    - t.
      econstructor.
      unfold tdot in H4.
      rewrite env_lookup_edot; eauto.
    - econstructor; eauto.
    - simpl in *; simpt. econstructor; eauto.
    - simpl in *; simpt. econstructor; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpl in *. simpt. t. 
      destruct x0; destruct x; simpl in *; subst.
      eapply type_cNNRCLet; eauto.
      destruct (rec_sort_nnrc_to_camp_env_pullback ((v, s2) :: Γ)) 
        as [g' [grec gperm]]; simpl; [econstructor; eauto|idtac].
      symmetry in gperm.
      assert(nin:forall x : string, In x (domain g') -> In x (nnrc_bound_vars n2) -> False) 
        by (intros ? inn1 inn2; apply dom_perm in gperm;
            apply (Permutation_in _ gperm) in inn1;
            simpl in inn1; destruct inn1; subst; eauto).
      apply (nnrc_core_type_context_perm _ _ _ gperm); try rewrite gperm; trivial.
      + simpl; econstructor; eauto.
      + eapply IHn2; trivial;
          unfold rtype; rewrite <- grec; eauto.
         * repeat defresh. 
            unfold rec_concat_sort in H20.
            simpl nnrc_to_camp_env.
            assert (perm: Permutation 
                            ((loop_var v, s2) :: nnrc_to_camp_env Γ) 
                            (nnrc_to_camp_env Γ ++ [(loop_var v, s2)]))
              by (rewrite Permutation_app_comm; simpl; reflexivity).
              erewrite drec_sort_perm_eq; try eapply perm; eauto.
              simpl. econstructor; eauto.
              intros inn1.
              apply nnrc_to_camp_in in inn1.
              intuition.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpl in *. simpt. t. 
      destruct x0; destruct x; simpl in *; subst.
      eapply type_cNNRCFor; eauto.
      destruct (rec_sort_nnrc_to_camp_env_pullback ((v, s2) :: Γ)) 
        as [g' [grec gperm]]; [simpl; econstructor; eauto|idtac].
      symmetry in gperm.
      assert(nin:forall x : string, In x (domain g') -> In x (nnrc_bound_vars n2) -> False) 
        by (intros ? inn1 inn2; apply dom_perm in gperm;
            apply (Permutation_in _ gperm) in inn1;
            simpl in inn1; destruct inn1; subst; eauto).
      apply (nnrc_core_type_context_perm _ _ _ gperm); try rewrite gperm; trivial.
      + simpl; econstructor; eauto.
      + eapply IHn2; unfold rtype; trivial; rewrite <- grec; eauto.
        unfold merge_bindings in H14.
        destruct (Compat.compatible (nnrc_to_camp_env Γ) [(loop_var v, s2)]);
            [idtac|discriminate].
            t.
            unfold rec_concat_sort in H20.
            simpl nnrc_to_camp_env.
            assert (perm: Permutation 
                            ((loop_var v, s2) :: nnrc_to_camp_env Γ) 
                            (nnrc_to_camp_env Γ ++ [(loop_var v, s2)]))
                   by (rewrite Permutation_app_comm; simpl; reflexivity).
            erewrite drec_sort_perm_eq; try eapply perm; eauto 2.
            simpl. econstructor; eauto.
            intros inn1.
            apply nnrc_to_camp_in in inn1.
            intuition.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpl in *; simpt; t. 
      inversion H34; inversion H25; subst.
      rewrite sort_sorted_is_id in H17,H21,H26,H30 by trivial.
      econstructor; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpl in *; simpt; t.
      destruct x; destruct x0; destruct x1; destruct x2; simpl in *; subst.
      unfold merge_bindings in *.
      match_case_in H15; intros comcamp1; rewrite comcamp1 in H15; try discriminate.
      match_case_in H18; intros comcamp2; rewrite comcamp2 in H18; try discriminate.
      match_case_in H23; intros comcamp3; rewrite comcamp3 in H23; try discriminate.
      match_case_in H25; intros comcamp4; rewrite comcamp4 in H25; try discriminate.
      inversion H15; clear H15; subst.
      inversion H18; clear H18; subst.
      inversion H23; clear H23; subst.
      inversion H25; clear H25; subst.
      econstructor; [eauto | .. ].
      + destruct (rec_sort_nnrc_to_camp_env_pullback ((v, s4) :: Γ)) 
          as [g' [grec gperm]]; [simpl; econstructor; eauto|idtac].
        symmetry in gperm.
        assert(nin:forall x : string, In x (domain g') -> In x (nnrc_bound_vars n2) -> False) 
          by (intros ? inn1 inn2; apply dom_perm in gperm;
              apply (Permutation_in _ gperm) in inn1;
              simpl in inn1; destruct inn1; subst; eauto).
        apply (nnrc_core_type_context_perm _ _ _ gperm); try rewrite gperm; trivial.
        simpl; econstructor; eauto.
        eapply IHn2; unfold rtype; trivial; rewrite <- grec; eauto.
        * unfold rec_concat_sort in H32.
          assert (perm: Permutation 
                          ((loop_var v, s4) :: nnrc_to_camp_env Γ) 
                          (nnrc_to_camp_env Γ ++ [(loop_var v, s4)]))
            by (rewrite Permutation_app_comm; simpl; reflexivity).
            erewrite drec_sort_perm_eq; try eapply perm; eauto.
            simpl. econstructor; eauto.
            intros inn1.
            apply nnrc_to_camp_in in inn1.
            intuition.
      + destruct (rec_sort_nnrc_to_camp_env_pullback ((v0, s6) :: Γ)) 
          as [g' [grec gperm]]; [simpl; econstructor; eauto|idtac].
        symmetry in gperm.
        assert(nin:forall x : string, In x (domain g') -> In x (nnrc_bound_vars n3) -> False) 
          by (intros ? inn1 inn2; apply dom_perm in gperm;
              apply (Permutation_in _ gperm) in inn1;
              simpl in inn1; destruct inn1; subst; eauto).
        apply (nnrc_core_type_context_perm _ _ _ gperm); try rewrite gperm; trivial.
        simpl; econstructor; eauto.
        eapply IHn3; unfold rtype; trivial; rewrite <- grec; eauto.
        * unfold rec_concat_sort in H29.
          assert (perm: Permutation 
                          ((loop_var v0, s6) :: nnrc_to_camp_env Γ) 
                          (nnrc_to_camp_env Γ ++ [(loop_var v0, s6)]))
            by (rewrite Permutation_app_comm; simpl; reflexivity).
            erewrite drec_sort_perm_eq; try eapply perm; eauto.
            simpl. econstructor; eauto.
            intros inn1.
            apply nnrc_to_camp_in in inn1.
            intuition.
    - simpl in Hiscore; contradiction.  (* GroupBy Case -- nnrcIsCore is False *)
   Qed.

  Lemma nnrc_to_camp_ns_top_type_preserve_back n τc τout :
    nnrcIsCore n ->
    shadow_free n = true ->
    forall τ₀,
      [τc&nil] |= (nnrcToCamp_ns n) ; τ₀ ~> τout ->
                                     nnrc_core_type τc nil n τout.
  Proof.
    intro Hiscore.
    intros.
    apply (nnrc_to_camp_ns_type_preserve_back n τc nil) in H0; eauto.
  Qed.

  Lemma PTmapall_let τc {Γ : tbindings} {τ₁ τ₂ : rtype} {p : camp} :
    NoDup (domain Γ) ->
    fresh_bindings (domain Γ) (mapall_let p) ->
    ([τc&Γ] |= p; τ₁ ~> τ₂) -> [τc&Γ] |= mapall_let p; Coll τ₁ ~> Coll τ₂.
  Proof.
    unfold mapall_let; intros.
    autorewrite with fresh_bindings in H0; intuition. 
    specialize (H0 _ (eq_refl _)).
    repeat econstructor; eauto.
    - rewrite merge_bindings_single_nin; [reflexivity|trivial].
    - rewrite tdot_rec_concat_sort_eq; eauto.
    - rewrite drec_sort_drec_sort_concat.
      rewrite tdot_rec_concat_sort_eq; eauto.
      Grab Existential Variables.
      eauto.
      eauto.
      eauto.
      eauto.
  Qed.

  Lemma PTmapall_let_inv τc {Γ : tbindings} {τ₁ τ₂ : rtype} {p : camp} :
    is_list_sorted ODT_lt_dec (domain Γ) = true ->
    fresh_bindings (domain Γ) (mapall_let p) ->
    [τc&Γ] |= mapall_let p; τ₁ ~> τ₂ ->
                            exists τ₁' τ₂',
                              τ₁ = Coll τ₁' /\
                              τ₂ = Coll τ₂' /\
                              ([τc&Γ] |= p; τ₁' ~> τ₂').
  Proof.
    unfold mapall_let; intros.
    autorewrite with fresh_bindings in H0; intuition. 
    specialize (H0 _ (eq_refl _)).
    t.
    destruct x; simpl in *; subst.
    inversion H18; subst.
    t.
    inversion H14; subst.
    t.
    inversion H16; subst.
    t.
    inversion H17; subst.
    t.
    rewrite sort_sorted_is_id in H6; eauto.
    rewrite H6 in H9. inversion H9; subst.
    inversion H11; subst.
    rtype_equalizer.
    subst.
    repeat eexists; intuition.
    unfold merge_bindings in H12.
    match goal with 
    | [H: context [match ?x with
                   | true => _
                   | false => _
                   end] |- _]=> destruct x
    end; try discriminate.
    t.
    rewrite tdot_rec_concat_sort_eq in H6; eauto.
    t. subst. eauto.
  Qed.

  Hint Resolve merge_bindings_sorted.

  Lemma nnrcToCamp_ns_type_weaken_let_binding τc b x xv τ₁ τ₂ n :
    nnrcIsCore n ->
    shadow_free n = true ->
    is_list_sorted ODT_lt_dec (domain b) = true ->
    fresh_bindings (domain b) (nnrcToCamp_ns n) ->
    (forall x, In x (domain b) -> ~ In x (map loop_var (nnrc_bound_vars n))) ->
    NoDup (domain b) ->
    ~ In (let_var x) (let_vars (nnrcToCamp_ns n)) ->
    ~ In (let_var x) (domain b) ->
    [τc&(rec_concat_sort b
                         ((let_var x, xv)::nil))] |= (nnrcToCamp_ns n) ; τ₁ ~> τ₂ ->
                                                                        [τc&b] |= (nnrcToCamp_ns n) ; τ₁ ~> τ₂.
  Proof.
    Hint Resolve loop_let_var_distinct.
    Hint Resolve rec_concat_sort_sorted.
    Hint Resolve drec_concat_sort_sorted.

    intro Hiscore.
    revert Hiscore b x xv τ₁ τ₂.
    induction n; intro Hiscore; intros; trivial; simpl in H1;
    try autorewrite with fresh_bindings in H1;
    simpt.
    - simpl in *. t. econstructor; eauto.
    - simpl in *.
      t.
      repeat econstructor; eauto.
      rewrite tdot_rec_concat_sort_neq in H7; [idtac|eauto].
      rewrite sort_sorted_is_id in H7; eauto.
    - simpl in *; t; eauto.
    - simpl in *; simpt;  t; eauto.
    - simpl in *; simpt;  t; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpl in *. simpt; t.
      econstructor; eauto.
      destruct x0; simpl in *; subst.
      econstructor.
      + econstructor; eauto.
      + rewrite merge_bindings_single_nin; [reflexivity|idtac].
        eauto.
      + eapply IHn2; eauto 2;  unfold rec_concat_sort.
        * apply (drec_sort_sorted (odt:=ODT_string)).
        * autorewrite with fresh_bindings.
          simpl.
          autorewrite with fresh_bindings.
          intuition.
        * intros ? inn1 inn2.
          apply drec_sort_domain in inn1.
          rewrite domain_app in inn1.
          rewrite in_app_iff in inn1; simpl in inn1.
          intuition.
          eapply H8; eauto.
          subst.
          apply in_map_iff in inn2.
          destruct inn2 as [? [? ?]].
          apply loop_var_inj in H11; subst. eauto.
        * eauto.
        * intros inn.
          rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
          simpl in inn. intuition.
        * rewrite rec_sort_rec_sort_app1.
          assert (perm:Permutation
                         ((b ++ [(loop_var v, s0)]) ++ [(let_var x, xv)])
                         ((b ++ [(let_var x, xv)]) ++ [(loop_var v, s0)])).
          repeat rewrite app_ass. apply Permutation_app; eauto.
          apply perm_swap.
          repeat defresh.
          erewrite drec_sort_perm_eq; try eapply perm.
          rewrite <- rec_sort_rec_sort_app1; eauto.
          rewrite Permutation_app_comm. simpl.
          econstructor; eauto.
          rewrite domain_app, in_app_iff; simpl; intuition.
          rewrite domain_app; simpl. 
          rewrite Permutation_app_comm; simpl.
          econstructor; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpl in *. simpt; t.
      eapply PTmapall_inv in H20; eauto 2.
      destruct H20 as [?[?[?[??]]]]; subst.
      econstructor; eauto.
      eapply PTmapall; eauto.
      econstructor.
      + econstructor; eauto.
      + rewrite merge_bindings_single_nin; [reflexivity|idtac].
        eauto.
      + t. 
        destruct x0; simpl in *; subst.
        intuition.
        eapply IHn2; eauto 2;  unfold rec_concat_sort.
        * apply (drec_sort_sorted (odt:=ODT_string)).
        * autorewrite with fresh_bindings.
          simpl.
          autorewrite with fresh_bindings.
          intuition.
        * intros ? inn1 inn2.
          apply drec_sort_domain in inn1.
          rewrite domain_app in inn1.
          rewrite in_app_iff in inn1; simpl in inn1.
          intuition.
          eapply H8; eauto.
          subst.
          apply in_map_iff in inn2.
          destruct inn2 as [? [? ?]].
          apply loop_var_inj in H12; subst. eauto.
        * intros inn.
          repeat rewrite in_app_iff in H11; simpl in H11.
          intuition.
          eauto 2.
        * intros inn. 
          rewrite in_dom_rec_sort, domain_app, in_app_iff in inn;
            unfold domain in inn; simpl in inn.
          repeat rewrite in_app_iff in H11; simpl in H11; intuition.
        * rewrite rec_sort_rec_sort_app1.
          assert (perm:Permutation
                         ((b ++ [(loop_var v, s0)]) ++ [(let_var x, xv)])
                         ((b ++ [(let_var x, xv)]) ++ [(loop_var v, s0)])).
          repeat rewrite app_ass. apply Permutation_app; eauto.
          apply perm_swap.
          repeat defresh.
          erewrite drec_sort_perm_eq; try eapply perm.
          rewrite <- rec_sort_rec_sort_app1; eauto.
          rewrite Permutation_app_comm. simpl.
          econstructor; eauto.
          rewrite domain_app, in_app_iff; simpl; intuition.
          rewrite domain_app; simpl. 
          rewrite Permutation_app_comm; simpl.
          econstructor; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpl in *. simpt; t.
      unfold rec_concat_sort in *.
      rewrite sort_sorted_is_id in H27,H31 by auto.
      econstructor.
      + econstructor; [eauto|..].
        rewrite merge_bindings_nil_r. reflexivity.
        inversion H35; subst.
        rewrite sort_sorted_is_id by auto.
        eauto.
      + econstructor; [eauto|..].
        rewrite merge_bindings_nil_r. reflexivity.
        inversion H35; subst.
        rewrite sort_sorted_is_id by auto.
        eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpl in *; simpt; t.
      destruct x0; destruct x1; simpl in *; subst.
      unfold merge_bindings in *.
      match_case_in H26; intros comcamp1; rewrite comcamp1 in H26; try discriminate.
      inversion H26; clear H26; subst.
      match_case_in H28; intros comcamp2; rewrite comcamp2 in H28; try discriminate.
      inversion H28; clear H28; subst.
      econstructor; [eauto|idtac].
      apply not_or in H16.
      destruct H16 as [? GG].
      repeat rewrite nin_app_or in GG. simpl in GG.
      destruct GG as [? GG1].
      apply not_or in GG1.
      destruct GG1 as [??].
      econstructor.
      + econstructor; [eauto|idtac].
        econstructor.
        * repeat econstructor.
        * rewrite merge_bindings_single_nin; try reflexivity.
          eauto.
        * { eapply IHn2; trivial.
            - apply (drec_concat_sort_sorted (odt:=ODT_string)).
            - unfold rec_concat_sort.
              autorewrite with fresh_bindings; simpl.
              autorewrite with fresh_bindings. eauto.
            - unfold rec_concat_sort. intros ? inn.
              rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
              simpl in inn.
              destruct inn as [?|[?|?]]; subst; eauto 2.
              rewrite in_map_iff.
              intros [?[injj ?]]; apply loop_var_inj in injj; subst; eauto.
            - eauto.
            - eauto.
            - unfold rec_concat_sort. intros inn.
              rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
              simpl in inn.
              destruct inn as [?|[?|?]]; subst; eauto 2.
            - unfold rec_concat_sort in H29 |- *.
              rewrite rec_sort_rec_sort_app1 in H29 |- *.
              assert (perm:Permutation
                             ((b ++ [(loop_var v, s0)]) ++ [(let_var x, xv)])
                             ((b ++ [(let_var x, xv)]) ++ [(loop_var v, s0)])).
              { repeat rewrite app_ass.
                apply Permutation_app; try reflexivity.
                apply Permutation_app_comm.
              }
              erewrite drec_sort_perm_eq; try eapply perm; trivial.
              repeat rewrite domain_app.
              rewrite Permutation_app_comm; simpl.
              { constructor.
                - repeat rewrite in_app_iff; simpl.
                  intros [?|[?|?]]; eauto 2.
                - rewrite Permutation_app_comm; simpl.
                  auto.
              }
          } 
      + econstructor; [eauto|idtac].
        econstructor.
        * repeat econstructor.
        * rewrite merge_bindings_single_nin; try reflexivity.
          eauto.
        * { eapply IHn3; trivial.
            - apply (drec_concat_sort_sorted (odt:=ODT_string)).
            - unfold rec_concat_sort.
              autorewrite with fresh_bindings; simpl.
              autorewrite with fresh_bindings. auto.
            - unfold rec_concat_sort. intros ? inn.
              rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
              simpl in inn.
              destruct inn as [?|[?|?]]; subst; eauto 2.
              rewrite in_map_iff. intros [?[injj ?]]; apply loop_var_inj in injj; subst; eauto.
            - eauto.
            - eauto.
            - unfold rec_concat_sort. intros inn.
              rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
              simpl in inn.
              destruct inn as [?|[?|?]]; subst; eauto 2.
            - unfold rec_concat_sort in H34 |- *.
              rewrite rec_sort_rec_sort_app1 in H34 |- *.
              assert (perm:Permutation
                             ((b ++ [(let_var x, xv)]) ++ [(loop_var v0, s2)])
                             ((b ++ [(loop_var v0, s2)]) ++ [(let_var x, xv)])).
              repeat rewrite app_ass.
              apply Permutation_app; try reflexivity.
              apply Permutation_app_comm.
              erewrite <- drec_sort_perm_eq; try eapply perm; trivial.
              repeat rewrite domain_app.
              rewrite Permutation_app_comm; simpl.
              { constructor.
                - repeat rewrite in_app_iff; simpl.
                  intros [?|[?|?]]; eauto 2.
                - rewrite Permutation_app_comm; simpl.
                  auto.
              }
          }
          Grab Existential Variables.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.
  Qed.

  Lemma nnrc_to_camp_ns_let_type_equiv_back n τc Γ τout :
    nnrcIsCore n ->
      is_list_sorted ODT_lt_dec (domain Γ) = true ->
    fresh_bindings (domain Γ) (nnrcToCamp_ns_let n) ->
    shadow_free n = true ->
    (forall x, In x (domain Γ) -> ~ In x (map loop_var (nnrc_bound_vars n))) ->
    forall τ₀,
      [τc&Γ] |= (nnrcToCamp_ns_let n) ; τ₀ ~> τout ->
                                       [τc&Γ] |= (nnrcToCamp_ns n) ; τ₀ ~> τout.
  Proof.
    intro Hiscore.
    revert Hiscore Γ τout.
    induction n; intro Hiscore; simpl; intros Γ τout issort freshb shf ninb τ₀.
    - inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
    - inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
    - inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
    - specialize (IHn Hiscore).
      inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
      destruct x; destruct x0; simpl in *; subst.
      repeat econstructor; eauto.
      eapply IHn2; eauto.
      * repeat defresh.
        unfold rec_concat_sort.
        autorewrite with fresh_bindings.
        simpl. intuition.
        autorewrite with fresh_bindings; trivial.
      * repeat defresh.
        intros ? inn1 inn2.
        rewrite 
          rec_concat_sort_concats,
        in_dom_rec_sort,
        domain_app,
        in_app_iff
          in inn1.
        simpl in inn1.
        intuition; subst; eauto.
        apply in_map_iff in inn2.
        destruct inn2 as [? [??]]. apply loop_var_inj in H7; subst.
        eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
      apply PTmapall_let_inv in H6; eauto.
      destruct H6 as [? [? [? [??]]]]. subst.
      apply PTmapall_let_inv in H16; eauto.
      destruct H16 as [? [? [? [??]]]]. t. 
      destruct x; destruct x0; simpl in *; subst.
      econstructor.
      + apply IHn1; eauto.
      + econstructor.
        * { repeat econstructor.
            - eauto 2.
            - unfold mapall_let in H1.
              autorewrite with fresh_bindings in H1.
              intuition.
              repeat defresh.
              eapply IHn2; eauto 2.
              + apply (drec_concat_sort_sorted (odt:=ODT_string)).
              + unfold rec_concat_sort.
                autorewrite with fresh_bindings.
                split; [tauto | ].
                unfold domain; simpl.
                autorewrite with fresh_bindings.
                trivial.
              + intros ? inn1 inn2.
                rewrite 
                  rec_concat_sort_concats,
                in_dom_rec_sort,
                domain_app,
                in_app_iff
                  in inn1.
                simpl in inn1.
                intuition; subst; eauto.
                apply in_map_iff in inn2.
                destruct inn2 as [? [??]].
                apply loop_var_inj in H16; subst.
                eauto.
          }            
        * eauto 2.
        * econstructor.
          { econstructor.
            - econstructor.
              econstructor.
              apply type_OpRec.
            - rewrite rec_sorted_id; eauto 2.
            - unfold mapall_let in H1.
              autorewrite with fresh_bindings in H1.
              intuition.
              repeat defresh.
              eapply IHn2; eauto.
              + apply (drec_concat_sort_sorted (odt:=ODT_string)).
              + unfold rec_concat_sort.
                autorewrite with fresh_bindings.
                simpl. intuition.
                autorewrite with fresh_bindings; trivial.
              + intros ? inn1 inn2.
                rewrite 
                  rec_concat_sort_concats,
                in_dom_rec_sort,
                domain_app,
                in_app_iff
                  in inn1.
                simpl in inn1.
                intuition; subst; eauto.
                apply in_map_iff in inn2.
                destruct inn2 as [? [??]].
                apply loop_var_inj in H16; subst.
                eauto. 
          }
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
      specialize (H9 _ (eq_refl _)).
      destruct x; destruct x0; simpl in *; subst.
      rewrite sort_sorted_is_id in H26,H30,H39,H43 by eauto.
      inversion H22; subst.
      inversion H33; subst.
      t.
      inversion H24; inversion H28; subst.
      t.
      repeat defresh.
      rewrite tdot_rec_concat_sort_eq in H18 by eauto.
      rewrite tdot_rec_concat_sort_eq in H2 by eauto.
      t.
      econstructor.
      + econstructor; [eauto|..].
        rewrite merge_bindings_nil_r. rewrite sort_sorted_is_id by eauto. reflexivity.
        eapply nnrcToCamp_ns_type_weaken_let_binding; eauto.
        * apply fresh_bindings_let_to_naive; auto.
        * intro inn.
          apply (fresh_let_var_fresh "if$" (let_vars (nnrcToCamp_ns_let n1) ++
                                                     let_vars (nnrcToCamp_ns_let n2) ++
                                                     let_vars (nnrcToCamp_ns_let n3))).
          repeat rewrite in_app_iff.
          apply let_vars_let_to_naive in inn.
          rewrite fresh_let_var_as_let.
          unfold let_var in inn.
          right; left.
          eassumption.
        * eassumption.
        * eapply IHn2; eauto.
          unfold rec_concat_sort.
          autorewrite with fresh_bindings.
          simpl. intuition.
          autorewrite with fresh_bindings; intuition.
          apply (fresh_let_var_fresh "if$" (let_vars (nnrcToCamp_ns_let n1) ++
                                                     let_vars (nnrcToCamp_ns_let n2) ++
                                                     let_vars (nnrcToCamp_ns_let n3))).
          repeat rewrite in_app_iff.
          rewrite fresh_let_var_as_let.
          intuition.
          unfold rec_concat_sort; intros ? inn1 inn2.
          rewrite
            in_dom_rec_sort,
          domain_app,
          in_app_iff
            in inn1.
          simpl in inn1.
          intuition; subst; eauto.
          apply in_map_iff in inn2.
          destruct inn2 as [? [??]]. eapply loop_let_var_distinct; eauto.
      + econstructor; [eauto|..].
        rewrite merge_bindings_nil_r.
        rewrite sort_sorted_is_id by eauto. reflexivity.
        eapply nnrcToCamp_ns_type_weaken_let_binding; eauto 3.
        * apply fresh_bindings_let_to_naive; auto.
        * intro inn.
          apply (fresh_let_var_fresh "if$" (let_vars (nnrcToCamp_ns_let n1) ++
                                                     let_vars (nnrcToCamp_ns_let n2) ++
                                                     let_vars (nnrcToCamp_ns_let n3))).
          rewrite fresh_let_var_as_let.
          unfold let_var in inn.
          apply let_vars_let_to_naive in inn.
          repeat rewrite in_app_iff.
          right; right.
          unfold let_var in inn.
          eassumption.
        * eassumption.
        * eapply IHn3; eauto 3.
          unfold rec_concat_sort.
          autorewrite with fresh_bindings.
          simpl. intuition.
          autorewrite with fresh_bindings; intuition.
          apply (fresh_let_var_fresh "if$" (let_vars (nnrcToCamp_ns_let n1) ++
                                                     let_vars (nnrcToCamp_ns_let n2) ++
                                                     let_vars (nnrcToCamp_ns_let n3))).
          repeat rewrite in_app_iff.
          intuition.
          unfold rec_concat_sort; intros ? inn1 inn2.
          rewrite
            in_dom_rec_sort,
          domain_app,
          in_app_iff
            in inn1.
          simpl in inn1.
          intuition; subst; eauto.
          apply in_map_iff in inn2.
          destruct inn2 as [? [??]]. eapply loop_let_var_distinct; eauto.
    - simpl in Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      inversion 1; subst; simpl in freshb, shf, ninb;
      autorewrite with fresh_bindings in freshb;
      simpt; t; eauto.
      destruct x; destruct x0; destruct x1; destruct x2; simpl in *; subst.
      econstructor; [eauto | ].
      econstructor.
      + econstructor; [eauto | ].
        econstructor.
        * repeat econstructor.
        * eauto.
        * unfold merge_bindings in *.
          match_case_in H29; intros comcamp1; rewrite comcamp1 in H29; try discriminate.
          inversion H29; clear H29; subst.
          { eapply IHn2; eauto 2.
            - apply (drec_concat_sort_sorted (odt:=ODT_string)).
            - unfold rec_concat_sort.
              autorewrite with fresh_bindings; simpl.
              autorewrite with fresh_bindings; eauto.
            - unfold rec_concat_sort. intros ? .
              rewrite in_dom_rec_sort, domain_app, in_app_iff.
              simpl. intros [?|[?|?]]; subst; eauto 2.
              rewrite in_map_iff.
              intros [?[injj ?]]; apply loop_var_inj in injj; subst; eauto.
          }
      + econstructor; [eauto | ].
        econstructor.
        * repeat econstructor.
        * eauto.
        * unfold merge_bindings in *.
          match_case_in H31; intros comcamp2; rewrite comcamp2 in H31; try discriminate.
          inversion H31; clear H31; subst.
          { eapply IHn3; eauto 2.
            - apply (drec_concat_sort_sorted (odt:=ODT_string)).
            - unfold rec_concat_sort.
              autorewrite with fresh_bindings; simpl.
              autorewrite with fresh_bindings; eauto.
            - unfold rec_concat_sort. intros ? .
              rewrite in_dom_rec_sort, domain_app, in_app_iff.
              simpl. intros [?|[?|?]]; subst; eauto 2.
              rewrite in_map_iff.
              intros [?[injj ?]]; apply loop_var_inj in injj; subst; eauto.
          }
    - simpl in Hiscore; contradiction.  (* GroupBy Case -- nnrcIsCore is False *)
      Grab Existential Variables.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
  Qed.

  Lemma nnrc_to_camp_let_type_preserve_back n τc Γ τout :
    nnrcIsCore n ->
    is_list_sorted ODT_lt_dec (domain (nnrc_to_camp_env Γ)) = true ->
    forall τ₀,
      [τc&(nnrc_to_camp_env Γ)] |= (nnrcToCamp_let (domain Γ) n) ; τ₀ ~> τout ->
      nnrc_core_type τc Γ n τout.
  Proof.
    intro Hiscore. intros. unfold nnrcToCamp_let in *.
    generalize (unshadow_simpl_preserve_core (domain Γ) n Hiscore); intros.
    unfold cNNRCShadow.unshadow_simpl in *.
    eapply nnrc_core_unshadow_type.
    eapply (nnrc_to_camp_ns_type_preserve_back); trivial.
    - apply unshadow_preserve_core; assumption.
    - apply unshadow_shadow_free.
    - apply unshadow_avoid.
    - apply nnrc_to_camp_ns_let_type_equiv_back; eauto.
      + apply fresh_bindings_from_tnnrc.
      + apply unshadow_shadow_free.
      + intros ? inn1 inn2.
        unfold nnrc_to_camp_env, domain in inn1.
        rewrite map_map, in_map_iff in inn1.
        destruct inn1 as [? [? inn1]]; subst.
        rewrite in_map_iff in inn2.
        destruct inn2 as [? [eqs inn2]]; subst; simpl in *.
        apply loop_var_inj in eqs; subst.
        destruct x0; simpl in *.
        revert inn2.
        apply unshadow_avoid.
        eapply in_dom; eauto.
  Qed.

  Lemma nnrc_to_camp_ns_let_top_type_preserve_back n τc τout :
    nnrcIsCore n ->
    shadow_free n = true ->
    forall τ₀,
      [τc&nil] |= (nnrcToCamp_ns_let n) ; τ₀ ~> τout ->
                                          nnrc_core_type τc nil n τout.
  Proof.
    intro Hiscore. intros.
    apply nnrc_to_camp_ns_let_type_equiv_back in H0; eauto.
    apply nnrc_to_camp_ns_top_type_preserve_back in H0; eauto.
    unfold fresh_bindings; simpl; intuition.
  Qed.

  (** Theorem 7.4, NNRC<->CAMP.
       Final iff Theorem of type preservation for the translation
       from NNRC back to Campterns *)

  Theorem nnrc_to_camp_let_top_type_preserve_iff τc Γ n τout τ₀:
    nnrcIsCore n ->
    is_list_sorted ODT_lt_dec (domain (nnrc_to_camp_env Γ)) = true ->
    (nnrc_core_type τc Γ n τout <->
    [τc&(nnrc_to_camp_env Γ)]  |= (nnrcToCamp_let (domain Γ) n) ; τ₀ ~> τout).
   Proof.
     Hint Resolve nnrc_to_camp_let_type_preserve.
     Hint Resolve nnrc_to_camp_let_type_preserve_back.
     intuition; eauto.
   Qed.

End TcNNRCtoCAMP.

