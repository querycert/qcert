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
Require Import EquivDec.
Require Import Decidable.
Require Import Morphisms.
Require Import Datatypes.
Require Import Permutation.
Require Import Eqdep_dec.
Require Import Omega.
Require Import Utils.
Require Import CommonRuntime.
Require Import CAMPRuntime.
Require Import cNNRCRuntime.
Require Import NNRCSize.
Require Import CAMPSize.

Section cNNRCtoCAMP.
  Context {fruntime:foreign_runtime}.

  (** Auxiliary definitions and lemmas *)

  Definition loop_var (n:string):string := append "loop$" n.

  Lemma loop_var_inj x y : loop_var x = loop_var y -> x = y.
  Proof.
    unfold loop_var; intros re.
    inversion re; trivial.
  Qed.

  Definition let_var (n:string):string := append "let$" n.

  Lemma let_var_inj x y : let_var x = let_var y -> x = y.
  Proof.
    unfold loop_var; intros re.
    inversion re; trivial.
  Qed.

  Fixpoint let_vars (p:camp) : list string := 
    match p with
    | pconst _ => nil
    | punop uop p => 
      match uop with
      | OpRec f => f::nil
      | _ => nil
      end ++ let_vars p
    | pbinop bop p₁ p₂ => let_vars p₁ ++ let_vars p₂
    | pmap p => let_vars p
    | passert p => let_vars p
    | porElse p₁ p₂ => let_vars p₁ ++ let_vars p₂
    | pit => nil
    | pletIt p₁ p₂ => let_vars p₁ ++ let_vars p₂
    | pletEnv p₁ p₂ => let_vars p₁ ++ let_vars p₂
    | penv => nil
    | pUnbrand => nil
    end.

  (** Translation from NNRC to CAMP.
      This assumes that there is no shadowing *)
  Fixpoint nnrcToCamp_ns (n:cNNRC.nnrc) : camp
    := match n with
       | cNNRC.NNRCGetConstant v => pgetConstant v
       | cNNRC.NNRCVar v => lookup (loop_var v)
       | cNNRC.NNRCConst d => pconst d
       | cNNRC.NNRCBinop op n1 n2 => pbinop op (nnrcToCamp_ns n1) (nnrcToCamp_ns n2)
       | cNNRC.NNRCUnop op n1 => punop op (nnrcToCamp_ns n1)
       | cNNRC.NNRCLet v bind body => 
         pletIt (nnrcToCamp_ns bind)
                (pletEnv (pvar (loop_var v))
                         (nnrcToCamp_ns body))
       | cNNRC.NNRCFor v iter body => 
         pletIt (nnrcToCamp_ns iter)
                (mapall
                   (pletEnv (pvar (loop_var v))
                            (nnrcToCamp_ns body)))
       | cNNRC.NNRCIf c n1 n2 =>
         let ctrans := (nnrcToCamp_ns c) in
         let n1trans := (nnrcToCamp_ns n1) in
         let n2trans := (nnrcToCamp_ns n2) in
         (porElse 
            (pand (pbinop OpAnd ‵true ctrans) n1trans)
            (* it could have failed because of n1, but then this will also fail *)
            (pand (punop OpNeg ctrans) n2trans))
       | cNNRC.NNRCEither nd xl nl xr nr =>
         pletIt (nnrcToCamp_ns nd)
                (porElse (pletIt pleft (pletEnv (pvar (loop_var xl)) (nnrcToCamp_ns nl))) (pletIt pright (pletEnv (pvar (loop_var xr)) (nnrcToCamp_ns nr))))
       | cNNRC.NNRCGroupBy g sl n =>
         pfail (* XXX How to do this best? XXX *)
       end.

  (** Definition with shadowing *)

  Definition nnrcToCamp avoid (n:cNNRC.nnrc) : camp := nnrcToCamp_ns (unshadow_simpl avoid n).

  (** Additional auxiliary lemmas to reason about domains and environments *)

  Definition nnrc_to_camp_env {A:Type} (env:list (string*A)) : list (string * A)
    := map (fun xy => (loop_var (fst xy), snd xy)) env.

  Lemma env_lookup_edot {A} (env:list (string*A)) (v:string) :
    NoDup (domain env) ->
     Assoc.lookup equiv_dec env v =
     edot (nnrc_to_camp_env env) (loop_var v).
  Proof.
    intros nd.
    unfold edot; simpl.
    induction env; simpl; trivial.
    destruct a; simpl. inversion nd; subst.
    rewrite <- IHenv by trivial.
    dest_eqdec.
    - match_case; intros.
      + apply Assoc.lookup_in in H.
        apply in_dom in H.
        tauto.
      + destruct (string_eqdec s s); simpl; [ | congruence ].
        trivial.
    - match_case.
      destruct (string_eqdec v s); simpl; trivial; intros nin.
      apply Assoc.lookup_none_nin in nin.
      congruence.
  Qed.

  Lemma compatible_nin v (env:list (string*data)) a :
        ~ In v (domain env) -> Compat.compatible (nnrc_to_camp_env env) ((loop_var v, a) :: nil) = true.
  Proof.
    revert v a. induction env; simpl; trivial.
    destruct a; simpl. intuition.
    rewrite IHenv; trivial.
    rewrite andb_true_iff; intuition.
    unfold compatible_with.
    simpl.
    destruct (equiv_dec (loop_var s) (loop_var v)); intuition.
    unfold equiv, complement in *.
    apply loop_var_inj in e. intuition.
  Qed.

  Lemma nnrc_to_camp_nodup {A env} : 
    NoDup (@domain _ A env) -> NoDup (domain (nnrc_to_camp_env env)).
  Proof.
    Hint Constructors NoDup.
    induction env; simpl; intuition.
    inversion H; subst.
    constructor; auto.
    destruct a; simpl in *.
    unfold domain, nnrc_to_camp_env.
    rewrite map_map; simpl.
    rewrite in_map_iff.
    intros [x [lx ix]].
    apply H2. destruct x. simpl in *.
    apply loop_var_inj in lx; subst.
    eapply in_dom; eauto.
  Qed.

  Lemma compatible_drec_sort_nin v (env: bindings) a :
    NoDup (domain env) ->
    ~ In v (domain env) ->
    Compat.compatible (rec_sort (nnrc_to_camp_env env)) ((loop_var v, a) :: nil) = true.
  Proof.
    intros.
    eapply compatible_perm_proper_l; try eapply compatible_nin; eauto.
    - apply rec_sort_perm.
      apply nnrc_to_camp_nodup; trivial.
  Qed.

  (* our translation does not look at the data *)
  Lemma nnrcToCamp_data_indep h cenv d d' b n:
    camp_eval h cenv (nnrcToCamp_ns n) b d = camp_eval h cenv (nnrcToCamp_ns n) b d'.
  Proof.
    revert d d' b. 
    induction n; simpl in *; trivial; intros.
    - erewrite IHn1, IHn2; eauto; intuition.
    - erewrite IHn; eauto; intuition.
    - rewrite (IHn1 d d') by intuition.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) b d'); trivial.
    - rewrite (IHn1 d d') by intuition.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) b d'); trivial.
    - rewrite (IHn1 d d') by intuition.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) b d'); trivial.
      destruct res; trivial.
      destruct b0; simpl;
        repeat rewrite merge_bindings_nil_r.
      + rewrite (IHn2 d d').
        destruct (camp_eval h cenv (nnrcToCamp_ns n2) (rec_sort b) d'); trivial.
      + apply IHn3.
    - rewrite (IHn1 d d').
      unfold bindpr. match_destr.
  Qed.

  (* mapall works (in the language) by counting.
    This is equivalent to failing if any of the parts fail *)

  Lemma gather_successes_le {A B} (f:A->presult B) l a :
    (gather_successes (map f l)) = Success a ->
    (bcount a) <=
    (bcount l).
  Proof.
    revert a.
    induction l; simpl; auto.
    - inversion 1; subst; simpl; auto.
    - intros a0.
      destruct (f a); simpl; inversion 1; auto.
      unfold liftpr in *. 
      destruct (gather_successes (map f l)); auto.
      inversion H; subst.
      specialize (IHl _ (eq_refl _)). simpl; omega.
  Qed.

  Lemma gather_successes_not_recoverable {A:Type} (l:list (presult A)) : 
    gather_successes l <> RecoverableError.
  Proof.
    induction l; simpl; inversion 1.
    destruct a; try congruence.
    destruct (gather_successes l); simpl in *; intuition.
    discriminate.
  Qed.

  Lemma bcount_false1 {A} (l1 l2: list A) :
    (bcount l2 <= bcount l1)%nat ->
    Z.of_nat (S (bcount l1)) = Z.of_nat (bcount l2) ->
    False.
  Proof.
    intros.
    inversion H0.
    assert (S (bcount l1) = (bcount l2)).
    apply of_nat_inv; assumption.
    omega.
  Qed.

  Lemma camp_eval_mapall_cons h cenv p bind a l :
    is_list_sorted ODT_lt_dec (domain bind) = true ->
    camp_eval h cenv (mapall p) bind (dcoll (a::l)) =
    match camp_eval h cenv p bind a, (camp_eval h cenv (mapall p) bind (dcoll l)) with
    | Success x', Success (dcoll l') =>  Success (dcoll (x'::l'))
    | RecoverableError, Success (dcoll l') => RecoverableError
    | Success a, RecoverableError => RecoverableError
    | RecoverableError, RecoverableError => RecoverableError
    | TerminalError, _ => TerminalError
    | _, TerminalError => TerminalError
    | RecoverableError , Success _ => TerminalError 
    | Success _, Success _ => TerminalError
    end.
  Proof.
    Opaque data_eq_dec.
    simpl.
    case_eq (camp_eval h cenv p bind a); simpl; intros; trivial.
    - case_eq ((gather_successes (map (camp_eval h cenv p bind) l))); 
        intros; simpl; trivial.
      generalize (gather_successes_le _ _ _ H1); intros.
      destruct (data_eq_dec (dnat (Z.pos (Pos.of_succ_nat (bcount l))))
                            (dnat (Z.of_nat (bcount res)))).
      inversion e. assert False by (apply (bcount_false1 l res); assumption); contradiction.
      destruct (data_eq_dec (dnat (Z.of_nat (bcount l)))
                            (dnat (Z.of_nat (bcount res)))); simpl; trivial.
      inversion e; simpl.
      assert (bcount l = bcount res) by (apply of_nat_inv; assumption).
      rewrite merge_bindings_nil_r.
      rewrite sort_sorted_is_id; trivial.
      rewrite H1; simpl; trivial.
    - case_eq ((gather_successes (map (camp_eval h cenv p bind) l))); 
        intros; simpl; trivial.
      destruct (data_eq_dec (dnat (Z.pos (Pos.of_succ_nat (bcount l))))
                            (dnat (Z.pos (Pos.of_succ_nat (bcount res0))))); simpl.
      + rewrite merge_bindings_nil_r.
        rewrite sort_sorted_is_id; trivial.
        rewrite H,H1; simpl.
        inversion e.
        assert (bcount l = bcount res0)
          by apply (pos_succ_nat_inv (bcount l) (bcount res0) H3).
        rewrite H2.
        destruct (data_eq_dec (dnat (Z_of_nat (bcount res0))) (dnat (Z_of_nat (bcount res0)))); [|intuition].
        simpl.
        rewrite merge_bindings_nil_r.
        rewrite sort_sorted_is_id; trivial.
        rewrite H1; simpl; trivial.
      + destruct (data_eq_dec (dnat (Z_of_nat (bcount l))) (dnat (Z_of_nat (bcount res0)))).
        inversion e.
        assert (bcount l = bcount res0) by (apply of_nat_inv; assumption).
        congruence.
        simpl; trivial.
  Qed.

  Fixpoint prmapM {A:Type} (os:list (presult A)) : presult (list A)
    := match os with
       | nil => Success nil
       | (TerminalError)::xs => TerminalError
       | (RecoverableError)::xs => 
         (* If the continuation results in a TerminalError, that is propogated *)
         match prmapM xs with
         | TerminalError => TerminalError
         | _ => RecoverableError
         end
       | (Success a)::xs => liftpr (cons a) (prmapM xs)
       end.

  Lemma camp_eval_mapall h cenv p bind l :
    is_list_sorted ODT_lt_dec (domain bind) = true ->
    camp_eval h cenv (mapall p) bind (dcoll l) = liftpr dcoll (prmapM (map (camp_eval h cenv p bind) l)).
  Proof.
    revert p bind.
    induction l; intros.
    - simpl; destruct (data_eq_dec (dnat 0) (dnat 0)); [|intuition]; simpl.
      rewrite merge_bindings_nil_r; trivial.
    - rewrite camp_eval_mapall_cons by trivial.
      rewrite IHl by trivial.
      simpl.
      destruct (camp_eval h cenv p bind a); simpl; trivial;
        destruct (prmapM (map (camp_eval h cenv p bind) l)); simpl; trivial.
  Qed.

  Transparent data_eq_dec.

  Lemma camp_eval_pletIt_eq h cenv p₁ p₂ bind d : 
    camp_eval h cenv (pletIt p₁ p₂) bind d=
    bindpr (camp_eval h cenv p₁ bind d) (camp_eval h cenv p₂ bind).
  Proof.
    reflexivity.
  Qed.

  (** our translation will never yield a recoverable error.
   There are only two sources of recoverable errors in the pattern lanugage:
   passert and pletEnv.
   1) passert: this only used by the translation in two places:
      (a) if statements and (b) for loops (inside of mapall).
   1a) if statements use porElse to "catch" the recoverable error created by passert
   1b) a recoverable error is thrown only if the size of the result is not the same as the size
         of the original collection.  But that only happens if the translation of the sub-pattern
         resulted in a recoverable error, which (by induction) does not happen.
    2) pletEnv: we use pletEnv to introduce loop variables for For, but we are careful that 
        any such variable is "free" with respect to the current environment (that is the point
        of the shadow_free predicate), so merge_bindings always succeeds.
   *)
  Lemma nnrcToCamp_norecoverable_ns h cenv n env :
    nnrcIsCore n ->
    shadow_free n = true ->
    NoDup (domain env) ->
    (forall x, In x (domain env) -> ~ In x (nnrc_bound_vars n)) ->
    isRecoverableError (camp_eval h cenv (nnrcToCamp_ns n) (rec_sort (nnrc_to_camp_env env)) dunit) = false.
  Proof.
    Hint Resolve op2tpr_not_recoverable.
    intros Hiscore.
    revert Hiscore env. induction n; intros; trivial.
    - simpl in *.
      destruct ((edot
                 (rec_sort (nnrc_to_camp_env env))
              (loop_var v))); simpl; trivial.
    - simpl in *.
      destruct ((edot
                 (rec_sort (nnrc_to_camp_env env))
              (loop_var v))); simpl; trivial.
    - simpl in *.
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
        specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      rewrite andb_true_iff in H; apply in_in_app_false in H1; intuition.
      specialize (IHn1 _ H2 H0).
      specialize (IHn2 _ H3 H0).
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env)) dunit);
        destruct (camp_eval h cenv (nnrcToCamp_ns n2) (rec_sort (nnrc_to_camp_env env)) dunit); simpl; intuition.
    - simpl in *.
      specialize (IHn Hiscore).
      specialize (IHn _ H H0).
      destruct (camp_eval h cenv (nnrcToCamp_ns n) (rec_sort (nnrc_to_camp_env env)) dunit); simpl; intuition.
    - simpl in Hiscore.
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpl in H, H1; repeat rewrite andb_true_iff in H; apply in_in_cons_app_false in H1; intuition.
      unfold nnrcToCamp_ns; fold nnrcToCamp_ns.
      unfold cNNRC.nnrc_core_eval; fold cNNRC.nnrc_core_eval.
      rewrite camp_eval_pletIt_eq.
      match_destr_in H1.
      specialize (IHn1 _ H5 H0 H).
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env)) dunit);
        unfold bindpr; [trivial|(elim IHn1; eauto)|idtac].
      simpl.
      unfold merge_bindings.
      rewrite (compatible_drec_sort_nin _ _ _ H0 H6).
      rewrite (drec_concat_sort_app_comm
                 (rec_sort (nnrc_to_camp_env env))
                   ((loop_var v, res) :: nil)).
      simpl.
      unfold rec_concat_sort.
      simpl. rewrite drec_sort_idempotent.
      replace (insertion_sort_insert rec_field_lt_dec 
            (loop_var v, res) (rec_sort (nnrc_to_camp_env env))) with
      (rec_sort (nnrc_to_camp_env ((v,res)::env))) by reflexivity.
      rewrite (nnrcToCamp_data_indep _ _ _ dunit).
      apply IHn2; trivial.
      + constructor; eauto.
      + simpl; intuition; subst; eauto.
      + rewrite domain_app.
         rewrite Permutation_app_comm.
         simpl. constructor.
        * intros nin.
          unfold rec_sort in nin.
          apply drec_sort_domain in nin.
          unfold domain, nnrc_to_camp_env in nin.
          rewrite map_map in nin.
          rewrite in_map_iff in nin.
          destruct nin as [x [xeq xin]].
          simpl in *.
          apply loop_var_inj in xeq. subst.
          destruct x.
          apply in_dom in xin.
          simpl in *; intuition.
        * rewrite <- rec_sort_perm; apply nnrc_to_camp_nodup; trivial.
    - simpl in Hiscore.
      elim Hiscore; clear Hiscore; intros Hcore1 Hcore2;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2).
      simpl in H, H1; repeat rewrite andb_true_iff in H; apply in_in_cons_app_false in H1; intuition.
      unfold nnrcToCamp_ns; fold nnrcToCamp_ns.
      unfold cNNRC.nnrc_core_eval; fold cNNRC.nnrc_core_eval.
      rewrite camp_eval_pletIt_eq.
      match_destr_in H1.
      specialize (IHn1 _ H5 H0 H).
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env)) dunit);
        unfold bindpr; [trivial|(elim IHn1; eauto)|idtac].
      destruct res; trivial. 
      rewrite camp_eval_mapall; trivial.
      rewrite isRecoverableError_liftpr.
      induction l; simpl; trivial.
      simpl in IHl.
      unfold merge_bindings at 1.
      rewrite (compatible_drec_sort_nin _ _ _ H0 H6).
      rewrite (drec_concat_sort_app_comm
                 (rec_sort (nnrc_to_camp_env env))
                   ((loop_var v, a) :: nil)).
      unfold rec_concat_sort.
      simpl.
      rewrite drec_sort_idempotent.
      replace (insertion_sort_insert rec_field_lt_dec 
            (loop_var v, a) (rec_sort (nnrc_to_camp_env env))) with
      (rec_sort (nnrc_to_camp_env ((v,a)::env))) by reflexivity.
      specialize (IHn2 ((v,a)::env)).
      rewrite (nnrcToCamp_data_indep _ _ _ dunit).
      destruct (camp_eval h cenv (nnrcToCamp_ns n2) (rec_sort (nnrc_to_camp_env ((v, a) :: env))) dunit); 
        simpl in *; trivial.
      cut (true = false); [intuition|idtac].
      apply IHn2; eauto; intros ? [?|?] ?; subst; eauto.
      rewrite isRecoverableError_liftpr. auto.
      rewrite domain_app.
      rewrite Permutation_app_comm.
      simpl. constructor.
        * intros nin. 
          apply drec_sort_domain in nin.
          unfold domain, nnrc_to_camp_env in nin.
          rewrite map_map in nin.
          rewrite in_map_iff in nin.
          destruct nin as [x [xeq xin]].
          simpl in *.
          apply loop_var_inj in xeq. subst.
          destruct x.
          apply in_dom in xin.
          simpl in *; intuition.
        * rewrite <- rec_sort_perm; apply nnrc_to_camp_nodup; trivial.
    - simpl in Hiscore.
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpl in *; repeat rewrite andb_true_iff in *.
      apply in_in_app_false in H1; intuition.
      apply in_in_app_false in H4; intuition.
      specialize (IHn1 _ H1 H0 H).
      specialize (IHn2 _ H5 H0 H2).
      specialize (IHn3 _ H3 H0 H6).
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env)) dunit); simpl; trivial.
      destruct res; trivial.
      simpl in *.
      destruct b; simpl; rewrite merge_bindings_nil_r; rewrite drec_sort_idempotent; trivial.
      destruct (camp_eval h cenv (nnrcToCamp_ns n2) (rec_sort (nnrc_to_camp_env env)) dunit); simpl; trivial.
    - simpl in Hiscore.
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpl in *. repeat rewrite andb_true_iff in *.
      destruct H as [[[[nin1 nin2]sn1]sn2]sn3].
      match_destr_in nin1. match_destr_in nin2.
      apply in_in_cons_cons_app_app_false in H1; intuition.
      specialize (IHn1 _ sn1 H0).
      unfold bindpr. match_destr; [auto | ].
      destruct res; simpl; trivial.
      + unfold merge_bindings at 1.
        rewrite (compatible_drec_sort_nin _ _ _ H0 H3).
        specialize (IHn2 ((v, res)::env) sn2).
        rewrite (drec_concat_sort_app_comm
                   (rec_sort (nnrc_to_camp_env env))
                   ((loop_var v, res) :: nil)).
        * unfold rec_concat_sort.
          simpl in IHn2. simpl.
          rewrite drec_sort_idempotent.
          rewrite (nnrcToCamp_data_indep _ _ _ dunit).
          match_destr.
          simpl in *. apply IHn2; auto.
          intros ? [?|?]; subst; eauto.
        * rewrite <- rec_sort_perm by (apply nnrc_to_camp_nodup; trivial).
          rewrite domain_app.
          rewrite Permutation_app_comm.
          simpl; constructor; try apply nnrc_to_camp_nodup; trivial.
          unfold domain, nnrc_to_camp_env.
          rewrite map_map.
          rewrite in_map_iff.
          simpl.
          intros [?[eqq ?]].
          apply loop_var_inj in eqq. subst.
          destruct x. apply H3.
          apply (in_dom H4).
      + unfold merge_bindings at 1.
        rewrite (compatible_drec_sort_nin _ _ _ H0 H5).
        specialize (IHn3 ((v0, res)::env) sn3).
        rewrite (drec_concat_sort_app_comm
                   (rec_sort (nnrc_to_camp_env env))
                   ((loop_var v0, res) :: nil)).
        * unfold rec_concat_sort.
          simpl in IHn3. simpl.
          rewrite drec_sort_idempotent.
          rewrite (nnrcToCamp_data_indep _ _ _ dunit).
          unfold isRecoverableError.
          match_destr.
          simpl in *. apply IHn3; auto.
          intros ? [?|?]; subst; eauto.
        * rewrite <- rec_sort_perm by (apply nnrc_to_camp_nodup; trivial).
          rewrite domain_app.
          rewrite Permutation_app_comm.
          simpl; constructor; try apply nnrc_to_camp_nodup; trivial.
          unfold domain, nnrc_to_camp_env.
          rewrite map_map.
          rewrite in_map_iff.
          simpl.
          intros [?[eqq ?]].
          apply loop_var_inj in eqq. subst.
          destruct x. apply H5.
          apply (in_dom H4).
    - simpl in Hiscore; contradiction. (* GroupBy Case nnrcIsCore is False *)
  Qed.

  Lemma nnrcToCamp_norecoverable_top_ns h cenv n :
    nnrcIsCore n ->
    shadow_free n = true ->
    isRecoverableError (camp_eval h cenv (nnrcToCamp_ns n) nil dunit) = false.
  Proof.
    intros.
    generalize (nnrcToCamp_norecoverable_ns h cenv n nil); simpl; auto.
  Qed.

  Theorem nnrcToCamp_norecoverable_top h cenv avoid n :
    nnrcIsCore n ->
    isRecoverableError (camp_eval h cenv (nnrcToCamp avoid n) nil dunit) = false.
  Proof.
    intros Hiscore.
    generalize (unshadow_simpl_preserve_core avoid n Hiscore); intros.
    generalize (nnrcToCamp_norecoverable_top_ns h cenv (unshadow_simpl avoid n)
               H (unshadow_shadow_free _ _ _ _)); intros.
    trivial.
  Qed.

  Lemma pr2op_liftpr  {A B:Type} (f:A->B) (pr:presult A) : 
      pr2op (liftpr f pr) = lift f (pr2op pr).
  Proof.
    destruct pr; trivial.
  Qed.

  Lemma in_loop_var_nnrc_to_camp_env {B} v (env:list (string*B)) :
   In (loop_var v) (domain (nnrc_to_camp_env env)) <-> In v (domain env).
  Proof.
    unfold domain, nnrc_to_camp_env.
    rewrite map_map.
    repeat rewrite in_map_iff.
    split; intros inn; destruct inn as [x [xeq xin]]; simpl in *; subst.
    - apply loop_var_inj in xeq. subst. exists x; intuition.
    - exists x; intuition.
  Qed.

  (** Note that since the translation never yields recoverable errors, 
      any errors are terminal, which nicely aligns with errors in NNRC (which are terminal) *)
  Lemma nnrcToCamp_sem_correct_ns h cenv n env :
    nnrcIsCore n ->
    shadow_free n = true ->
    NoDup (domain env) ->
    (forall x, In x (domain env) -> ~ In x (nnrc_bound_vars n)) ->
    cNNRC.nnrc_core_eval h cenv env n = pr2op (camp_eval h cenv (nnrcToCamp_ns n) (rec_sort (nnrc_to_camp_env env)) dunit).
  Proof.
    intros HisCore.
    revert HisCore env; induction n; intro Hiscore; intros; trivial.
    - simpl in *.
      destruct (edot cenv v); reflexivity.
    - simpl in *.
      simpl.
      rewrite env_lookup_edot; trivial.
      generalize (nnrc_to_camp_nodup H0); intros nd.
      generalize (rec_sort_perm _ nd); intros p.
      rewrite <- (edot_nodup_perm _ _ _ nd p).
      destruct (edot (nnrc_to_camp_env env) (loop_var v)); trivial.
    - simpl in *.
      rewrite andb_true_iff in H; apply in_in_app_false in H1.
      rewrite IHn1, IHn2; trivial; intuition.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env)) dunit); simpl; trivial.
      destruct (camp_eval h cenv (nnrcToCamp_ns n2) (rec_sort (nnrc_to_camp_env env)) dunit); simpl; trivial.
      rewrite pr2op_op2tpr; trivial.
    - simpl in *. 
      rewrite IHn; trivial.
      destruct (camp_eval h cenv (nnrcToCamp_ns n) (rec_sort (nnrc_to_camp_env env))); simpl; trivial.
      rewrite pr2op_op2tpr; trivial.
    - unfold nnrcToCamp_ns; fold nnrcToCamp_ns.
      unfold cNNRC.nnrc_core_eval; fold cNNRC.nnrc_core_eval.
      rewrite camp_eval_pletIt_eq.
      simpl in H, H1; repeat rewrite andb_true_iff in H; 
        apply in_in_cons_app_false in H1; intuition.
      destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
       intuition.
      rewrite IHn1; trivial.
      simpl.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env))  dunit);
        [intuition|intuition|idtac]. simpl.
      rewrite IHn2; trivial. simpl.
      unfold merge_bindings.
      rewrite (compatible_drec_sort_nin _ _ _ H0 H6).
      simpl.
      rewrite (drec_concat_sort_app_comm 
                 (rec_sort (nnrc_to_camp_env env))
                 ((loop_var v, res) :: nil)).
      unfold rec_concat_sort.
      simpl.
      rewrite drec_sort_idempotent.
      rewrite (nnrcToCamp_data_indep _ _ res dunit); trivial.
      rewrite domain_app.
      rewrite Permutation_app_comm.
      simpl. constructor.
      * rewrite in_dom_rec_sort, in_loop_var_nnrc_to_camp_env; trivial.
      * rewrite <- rec_sort_perm; apply nnrc_to_camp_nodup; trivial.
      * simpl in Hiscore. intuition.
      * simpl; constructor; trivial.
      * simpl in *. eauto; intros ? [?|?] ?; subst; eauto.
      * simpl in Hiscore. intuition.
    - (* need to be careful about simplifications, since we want to
          reason about mapall, which is a definition *)
      unfold nnrcToCamp_ns; fold nnrcToCamp_ns.
      unfold cNNRC.nnrc_core_eval; fold cNNRC.nnrc_core_eval.
      rewrite camp_eval_pletIt_eq.
      simpl in H, H1; repeat rewrite andb_true_iff in H; 
        apply in_in_cons_app_false in H1; intuition.
      destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
       intuition.
      rewrite IHn1; trivial.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env))  dunit);
        [intuition|intuition|idtac].
      unfold pr2op at 1.
      destruct res; trivial. unfold bindpr.
      rewrite camp_eval_mapall; trivial.
      rewrite pr2op_liftpr.
      f_equal.
      induction l; simpl; trivial.
      rewrite IHl. simpl.
      rewrite IHn2; trivial.
      + unfold merge_bindings at 2.
        rewrite (compatible_drec_sort_nin _ _ _ H0 H6).
        simpl.
        rewrite (drec_concat_sort_app_comm 
                   (rec_sort (nnrc_to_camp_env env))
                   ((loop_var v, a) :: nil)).
        unfold rec_concat_sort.
        simpl.
        rewrite drec_sort_idempotent.
        rewrite (nnrcToCamp_data_indep h _ a dunit); trivial.
        destruct ((camp_eval h cenv (nnrcToCamp_ns n2)
          (insertion_sort_insert rec_field_lt_dec 
             (loop_var v, a) (rec_sort (nnrc_to_camp_env env))) dunit)); simpl; trivial;
          destruct (prmapM
                      (map
            (fun d : data =>
             match
               merge_bindings (rec_sort (nnrc_to_camp_env env))
                              ((loop_var v, d) :: nil)
             with
             | Some bind' => camp_eval h cenv (nnrcToCamp_ns n2) bind' d
             | None => RecoverableError 
             end) l)); simpl; trivial.
        rewrite domain_app.
        rewrite Permutation_app_comm.
        simpl. constructor.
        * rewrite in_dom_rec_sort, in_loop_var_nnrc_to_camp_env; trivial.
        * rewrite <- rec_sort_perm; apply nnrc_to_camp_nodup; trivial.
      + simpl in Hiscore; intuition.
      + simpl; constructor; trivial.
      + simpl in *. eauto; intros ? [?|?] ?; subst; eauto.
      + simpl in Hiscore; intuition.
    - simpl in *; repeat rewrite andb_true_iff in *.
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      apply in_in_app_false in H1; intuition.
      apply in_in_app_false in H4; intuition.
      rewrite IHn1, IHn2, IHn3; trivial.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env)) dunit); simpl; trivial.
      simpl. destruct res; trivial.
      destruct b; simpl;
      rewrite merge_bindings_nil_r; rewrite drec_sort_idempotent; trivial.
      destruct (camp_eval h cenv (nnrcToCamp_ns n2) (rec_sort (nnrc_to_camp_env env)) dunit); trivial.
    - simpl in *.
      elim Hiscore; clear Hiscore; intros Hcore1 Hiscore;
      elim Hiscore; clear Hiscore; intros Hcore2 Hcore3;
      specialize (IHn1 Hcore1); specialize (IHn2 Hcore2); specialize (IHn3 Hcore3).
      simpl in *. repeat rewrite andb_true_iff in *.
      destruct H as [[[[nin1 nin2]sn1]sn2]sn3].
      match_destr_in nin1. match_destr_in nin2.
      apply in_in_cons_cons_app_app_false in H1; [| intuition.. ].
      rewrite IHn1 by intuition.
      unfold pr2op, bindpr.
      destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort (nnrc_to_camp_env env)) dunit); trivial.
      destruct H1 as [?[?[?[??]]]].
      destruct res; trivial.
      + rewrite IHn2; trivial.
         * unfold pr2op.
           unfold merge_bindings .
           rewrite (compatible_drec_sort_nin _ _ _ H0 H3).
           rewrite (drec_concat_sort_app_comm 
                      (rec_sort (nnrc_to_camp_env env))
                      ((loop_var v, res) :: nil)).
           unfold rec_concat_sort.
           simpl.
           rewrite drec_sort_idempotent.
           rewrite (nnrcToCamp_data_indep h _ res dunit); trivial.
           match_destr.
           rewrite <- rec_sort_perm, domain_app, Permutation_app_comm.
           simpl. constructor; trivial.
           rewrite in_loop_var_nnrc_to_camp_env; trivial.
           apply nnrc_to_camp_nodup; trivial.
           apply nnrc_to_camp_nodup; trivial.
         * constructor; trivial.
         * simpl. intros ? [?|?] inn; subst; eauto.
      + rewrite IHn3; trivial.
         * unfold pr2op.
           unfold merge_bindings .
           rewrite (compatible_drec_sort_nin _ _ _ H0 H4).
           rewrite (drec_concat_sort_app_comm 
                      (rec_sort (nnrc_to_camp_env env))
                      ((loop_var v0, res) :: nil)).
           unfold rec_concat_sort.
           simpl.
           rewrite drec_sort_idempotent.
           rewrite (nnrcToCamp_data_indep h _ res dunit); trivial.
           rewrite <- rec_sort_perm, domain_app, Permutation_app_comm.
           simpl. constructor; trivial.
           rewrite in_loop_var_nnrc_to_camp_env; trivial.
           apply nnrc_to_camp_nodup; trivial.
           apply nnrc_to_camp_nodup; trivial.
         * constructor; trivial.
         * simpl. intros ? [?|?] inn; subst; eauto.
  Qed.

  Lemma nnrcToCamp_sem_correct_top_ns h cenv n :
    nnrcIsCore n ->
    shadow_free n = true ->
    cNNRC.nnrc_core_eval h cenv nil n = pr2op (camp_eval h cenv (nnrcToCamp_ns n) nil dunit).
  Proof.
    intros.
    apply nnrcToCamp_sem_correct_ns; simpl; auto.
  Qed.

  Theorem nnrcToCamp_sem_correct_top h cenv avoid n :
    nnrcIsCore n ->
    cNNRC.nnrc_core_eval h cenv nil n = pr2op (camp_eval h cenv (nnrcToCamp avoid n) nil dunit).
  Proof.
    intro Hiscore.
    generalize (unshadow_simpl_preserve_core avoid n Hiscore); intros.
    generalize (nnrcToCamp_sem_correct_top_ns h cenv (unshadow_simpl avoid n)
                                             H (unshadow_shadow_free _ _ _ _)); intros.
    unfold nnrcToCamp.
    unfold unshadow_simpl in H0.
    rewrite nnrc_core_unshadow_eval in H0. trivial.
  Qed.

  Section trans_let.

    Section fresh.
      Definition option_to_list {A:Type} (o:option A) 
        := match o with
           | Some x => x::nil
           | None => nil
           end.
      
      Definition gather_opt_successes {A:Type} (os:list (option A)) : list A
        := flat_map option_to_list os.
      
      Definition fresh_let_var (pre:string) (l:list string) 
        := (fresh_var (append "let$" pre) l).
      
      Lemma fresh_let_var_fresh pre (l:list string) : 
        ~ In (fresh_let_var pre l) l.
      Proof.
        unfold fresh_let_var. apply fresh_var_fresh.
      Qed.

      Lemma fresh_let_var_as_let (pre:string) (l:list string) :
        fresh_let_var pre l = append "let$" (
                                       let problems := filter (prefix (append "let$" pre)) l in
                                       let problemEnds :=
                                           map
                                             (fun x : string =>
                                                substring (String.length (append "let$" pre)) (String.length x - String.length (append "let$" pre)) x) problems in
                                       (pre ++ find_fresh_string problemEnds))%string.
      Proof.
        reflexivity.
      Qed.
    
    End fresh.

    Definition fresh_bindings (vars:list string) (p:camp) :=
      forall x, In (let_var x) vars -> ~ In (let_var x) (let_vars p).

    Instance fresh_bindings_equiv_proper :
      Proper (equivlist ==> eq ==> iff) fresh_bindings.
    Proof.
      unfold Proper, respectful, equivlist; intros; subst.
      unfold fresh_bindings. 
      intuition; apply H in H1; eauto.
    Qed.

    Lemma fresh_bindings_pbinop l b p₁ p₂:
      fresh_bindings l (pbinop b p₁ p₂) <->
      (fresh_bindings l p₁ /\ fresh_bindings l p₂).
    Proof.
      Hint Resolve in_app_or in_or_app.
      unfold fresh_bindings; simpl; intuition; eauto.
      apply in_app_or in H2; intuition; eauto.
    Qed.

    Lemma fresh_bindings_punop l u p:
      fresh_bindings l (punop u p) <->
      (match u with
       | OpRec f => forall n, f = let_var n -> ~ In f l
       | _ => True
       end /\ fresh_bindings l p).
    Proof.
      unfold fresh_bindings; simpl.
      destruct u; simpl; intuition; subst; eauto.
    Qed.
    
    Lemma fresh_bindings_pletIt l p₁ p₂ :
      fresh_bindings l (pletIt p₁ p₂) <->
      (fresh_bindings l p₁ /\ fresh_bindings l p₂).
    Proof.
      Hint Resolve in_app_or in_or_app.
      unfold fresh_bindings; simpl; intuition; eauto.
      apply in_app_or in H2; intuition; eauto.
    Qed.
    
    Lemma fresh_bindings_pmap l p :
      fresh_bindings l (pmap p) <->
      fresh_bindings l p.
    Proof.
      unfold fresh_bindings; simpl; intuition.
    Qed.

    Lemma fresh_bindings_mapall l p :
      fresh_bindings l (mapall p) <->
      (fresh_bindings l p).
    Proof.
      Hint Resolve in_app_or in_or_app.
      unfold fresh_bindings; simpl; intuition; eauto.
      apply in_app_or in H1; intuition; eauto.
    Qed.

    Lemma fresh_bindings_pletEnv l p₁ p₂ :
      fresh_bindings l (pletEnv p₁ p₂) <->
      (fresh_bindings l p₁ /\ fresh_bindings l p₂).
    Proof.
      Hint Resolve in_app_or in_or_app.
      unfold fresh_bindings; simpl; intuition; eauto.
      apply in_app_or in H2; intuition; eauto.
    Qed.

    Lemma fresh_bindings_pvar l f :
      fresh_bindings l (pvar (let_var f)) <->
      ~ In (let_var f) l.
    Proof.
      unfold fresh_bindings; simpl.
      intuition; subst; eauto.
      apply let_var_inj in H2; subst; auto.
    Qed.
    
    Lemma fresh_bindings_porElse l p₁ p₂ :
      fresh_bindings l (porElse p₁ p₂) <->
      (fresh_bindings l p₁ /\ fresh_bindings l p₂).
    Proof.
      Hint Resolve in_app_or in_or_app.
      unfold fresh_bindings; simpl; intuition; eauto.
      apply in_app_or in H2; intuition; eauto.
    Qed.

    Lemma fresh_bindings_passert l p :
      fresh_bindings l (passert p) <->
      fresh_bindings l p.
    Proof.
      unfold fresh_bindings; simpl.
      intuition; subst; eauto.
    Qed.

    Lemma fresh_bindings_pand l p₁ p₂ :
      fresh_bindings l (pand p₁ p₂) <->
      (fresh_bindings l p₁ /\ fresh_bindings l p₂).
    Proof.
      Hint Resolve in_app_or in_or_app.
      unfold fresh_bindings; simpl; intuition; eauto.
      apply in_app_or in H2; intuition; eauto.
    Qed.

    Lemma fresh_bindings_plookup l f :
      fresh_bindings l (lookup f) <-> True.
    Proof.
      unfold fresh_bindings; simpl; intuition.
    Qed.
    
    Lemma  fresh_bindings_domain_drec_sort {A} l p :
      fresh_bindings (domain (@rec_sort _ _ A l)) p
      <-> fresh_bindings (domain l) p.
    Proof.
      rewrite drec_sort_equiv_domain; intuition.
    Qed.

    Lemma  fresh_bindings_app l₁ l₂ p :
      fresh_bindings (l₁ ++ l₂) p
      <-> (fresh_bindings l₁ p /\ 
           fresh_bindings l₂ p).
    Proof.
      unfold fresh_bindings; intuition; eauto.
      apply in_app_or in H. intuition; eauto. 
    Qed.

    Lemma fresh_bindings_cons a l p :
      fresh_bindings ((let_var a)::l) p
      <-> (~ In (let_var a) (let_vars p) /\ 
           fresh_bindings l p).
    Proof.
      unfold fresh_bindings; simpl in *; intuition; eauto.
      apply let_var_inj in H3; subst; eauto.
    Qed.

    Lemma fresh_bindings_nil p : 
      fresh_bindings nil p <-> True.
    Proof.
      unfold fresh_bindings; simpl; intuition.
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
    
    Definition mapall_let p :=
      let freshVar := fresh_let_var "ma$" (let_vars p) in
      (* calculate the map and store it in a "temporary variable" *)
      ((pletEnv (punop (OpRec freshVar) (pmap p))
                (pletEnv (punop OpCount pit ≐ punop OpCount (lookup freshVar))
                         (lookup freshVar))))%camp.

    Fixpoint nnrcToCamp_ns_let (n:cNNRC.nnrc) : camp
      := match n with
         | cNNRC.NNRCGetConstant v => pgetConstant v
         | cNNRC.NNRCVar v => lookup (loop_var v)
         | cNNRC.NNRCConst d => pconst d
         | cNNRC.NNRCBinop op n1 n2 => pbinop op (nnrcToCamp_ns_let n1) (nnrcToCamp_ns_let n2)
         | cNNRC.NNRCUnop op n1 => punop op (nnrcToCamp_ns_let n1)
         | cNNRC.NNRCLet v bind body => 
           pletIt (nnrcToCamp_ns_let bind)
                     (pletEnv (pvar (loop_var v))
                            (nnrcToCamp_ns_let body))
         | cNNRC.NNRCFor v iter body => 
           pletIt (nnrcToCamp_ns_let iter)
                 (mapall_let
                    (pletEnv (pvar (loop_var v))
                             (nnrcToCamp_ns_let body)))
                 
         | cNNRC.NNRCIf c n1 n2 =>
           let ctrans := (nnrcToCamp_ns_let c) in
           let n1trans := (nnrcToCamp_ns_let n1) in
           let n2trans := (nnrcToCamp_ns_let n2) in
           let freshVar := fresh_let_var "if$" (let_vars ctrans ++ let_vars n1trans ++ let_vars n2trans) in
           pletEnv (punop (OpRec freshVar) ctrans)
                   (porElse 
                      (pand (pbinop OpAnd ‵true (lookup freshVar)) n1trans)
                      (* it could have failed because of n1, but then this will also fail *)
                      (pand (punop OpNeg (lookup freshVar)) n2trans))
         | cNNRC.NNRCEither nd xl nl xr nr =>
           pletIt (nnrcToCamp_ns_let nd)
                  (porElse (pletIt pleft (pletEnv (pvar (loop_var xl)) (nnrcToCamp_ns_let nl))) (pletIt pright (pletEnv (pvar (loop_var xr)) (nnrcToCamp_ns_let nr))))
         | cNNRC.NNRCGroupBy g sl n =>
           pfail
         end.
    
    Definition nnrcToCamp_let avoid (n:cNNRC.nnrc) : camp 
      := nnrcToCamp_ns_let (unshadow_simpl avoid n).

    Lemma loop_let_var_distinct x y :
      loop_var x <> let_var y.
    Proof.
      inversion 1.
    Qed.

    Instance In_equivlist_proper {A}:
      Proper (eq ==> equivlist ==> iff) (@In A).
    Proof.
      unfold Proper, respectful, equivlist; intros; subst; trivial.
    Qed.

    Lemma camp_eval_nnrcToCamp_ns_ignored_let_binding h cenv b x xv d n :
      shadow_free n = true ->
      is_list_sorted ODT_lt_dec (domain b) = true ->
      fresh_bindings (domain b) (nnrcToCamp_ns n) ->
      (forall x, In x (domain b) -> ~ In x (map loop_var (nnrc_bound_vars n))) ->
      NoDup (domain b) ->
      ~ In (let_var x) (let_vars (nnrcToCamp_ns n)) ->
      ~ In (let_var x) (domain b) ->
      (camp_eval h cenv (nnrcToCamp_ns n)
                 (rec_concat_sort b
                                  ((let_var x, xv)::nil)) d)
      = 
      (camp_eval h cenv (nnrcToCamp_ns n)
                 (rec_sort b) d).
    Proof.
      Hint Resolve loop_let_var_distinct.
      revert b x xv d.
      induction n; intros; trivial; simpl in H0;
        autorewrite with fresh_bindings in H0.
      - simpl in *; unfold rec_concat_sort.
        unfold edot.
        repeat rewrite drec_sort_idempotent.
        rewrite (@assoc_lookupr_drec_sort_app_nin string ODT_string); simpl; intuition.
        eapply loop_let_var_distinct; eauto.
      - simpl in *;
          rewrite andb_true_iff in *; intuition.
        autorewrite with fresh_bindings in *. intuition.
        rewrite IHn1; intuition.
        rewrite IHn2; intuition.
        apply (H2 x0); eauto.
        rewrite map_app, in_app_iff; intuition.
        apply (H2 x0); eauto.
        rewrite map_app, in_app_iff; intuition.
      - autorewrite with fresh_bindings in *. intuition.
        simpl in *; rewrite IHn; intuition.
        unfold fresh_bindings in *; simpl in *; intros.
        intro nin; apply (H1 _ H6).
        destruct u; intuition.
      - unfold nnrcToCamp_ns; fold nnrcToCamp_ns.
        repeat rewrite camp_eval_pletIt_eq.
        simpl in H, H1,H2,H4. repeat rewrite andb_true_iff in H.
        rewrite map_app in H2.
        apply in_in_cons_app_false in H2.
        repeat rewrite nin_app_or in H4. simpl in H4. 
        autorewrite with fresh_bindings in *.
        intuition.
        rewrite IHn1; trivial.
        destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort b) d); simpl; trivial.
        destruct (in_dec string_eqdec v (nnrc_bound_vars n2)); try discriminate.
        repeat rewrite merge_bindings_single_nin; trivial.
        rewrite drec_concat_sort_pullout; auto.
        rewrite IHn2; trivial.
        simpl.
        rewrite drec_sort_drec_sort_concat.
        rewrite rec_sorted_id; eauto.
        unfold rec_concat_sort in *.
        * autorewrite with fresh_bindings; simpl; intuition.
          unfold fresh_bindings; simpl; intuition.
          eelim loop_let_var_distinct; eauto.
        * intros.
          unfold rec_concat_sort in *.
          rewrite drec_sort_equiv_domain in H10.
          rewrite domain_app in H10. simpl in H10.
          rewrite in_app_iff in H10. simpl in H10.
          destruct H10 as [?|[?|?]]; [eauto|idtac|trivial].
          subst. apply n.
          apply in_map_iff in H15.
          destruct H15 as [vv [vveq vvin]].
          apply loop_var_inj in vveq; subst. intuition.
        * cut (NoDup (domain (b ++ (loop_var v, res) :: nil))); intros.
          unfold rec_concat_sort; rewrite <- rec_sort_perm; trivial.
          rewrite domain_app.
          rewrite Permutation_app_comm.
          simpl.
          constructor; auto.
        * unfold rec_concat_sort.
          rewrite drec_sort_equiv_domain.
          rewrite domain_app, in_app_iff.
          simpl.
          intuition.
        * constructor; simpl. intuition.
          constructor; simpl; intuition.
        * intro nin. rewrite drec_sort_equiv_domain in nin. auto.
        * intro nin. unfold rec_concat_sort in nin.
          rewrite drec_sort_equiv_domain in nin.
          rewrite domain_app, in_app_iff in nin.
          simpl in nin.
          intuition.
      - (* need to be careful about simplifications, since we want to
          reason about mapall, which is a definition *)
        unfold nnrcToCamp_ns; fold nnrcToCamp_ns.
        repeat rewrite camp_eval_pletIt_eq.
        simpl in H, H1,H2,H4. repeat rewrite andb_true_iff in H.
        rewrite map_app in H2.
        apply in_in_cons_app_false in H2.
        repeat rewrite nin_app_or in H4. simpl in H4. 
        autorewrite with fresh_bindings in *.
        destruct H as [[??]?].
        destruct H1 as [?[??]].
        destruct H4 as [GG H4].
        repeat (apply not_or in H4; let x := fresh "GG" in
                                    destruct H4 as [x H4]).
        repeat rewrite in_app_iff in H4.
        repeat (apply not_or in H4; let x := fresh "GG" in
                                    destruct H4 as [x H4]).
        destruct H2 as [?[??]].
        rewrite IHn1; trivial.
        destruct (camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort b) d); try reflexivity.
        unfold bindpr.
        destruct res; try reflexivity.
        repeat rewrite camp_eval_mapall by intuition.
        f_equal; f_equal.
        apply Forall2_eq.
        rewrite <- Forall2_map.
        apply ListAdd.Forall2_refl.
        red; intros.
        simpl.
        destruct (in_dec string_eqdec v (nnrc_bound_vars n2)); try discriminate.
        repeat rewrite merge_bindings_single_nin; trivial.
        rewrite drec_concat_sort_pullout; auto.
        rewrite IHn2; trivial.
        rewrite drec_sort_drec_sort_concat.
        rewrite rec_sorted_id; eauto.
        * unfold rec_concat_sort.
          autorewrite with fresh_bindings; simpl; intuition.
          unfold fresh_bindings; simpl; intuition.
          eelim loop_let_var_distinct; eauto.
        * unfold rec_concat_sort.
          intros. 
          rewrite drec_sort_equiv_domain in H12.
          rewrite domain_app in H12. simpl in H12.
          rewrite in_app_iff in H12. simpl in H12.
          destruct H12 as [?|[?|?]]; [eauto|idtac|trivial].
          subst. rewrite in_map_iff. destruct 1 as [?[injj ?]].
          apply loop_var_inj in injj; subst. intuition.
          eauto.
        * unfold rec_concat_sort.
          cut (NoDup (domain (b ++ (loop_var v, x0) :: nil))); intros.
          rewrite <- rec_sort_perm; trivial.
          rewrite domain_app.
          rewrite Permutation_app_comm.
          simpl.
          constructor; auto.
        * unfold rec_concat_sort.
          rewrite drec_sort_equiv_domain.
          rewrite domain_app, in_app_iff.
          simpl.
          intuition.
        * constructor; simpl. intuition.
          constructor; simpl; intuition.
        * intro nin. rewrite drec_sort_equiv_domain in nin. auto.
        * intro nin. unfold rec_concat_sort in nin.
          rewrite drec_sort_equiv_domain in nin.
          rewrite domain_app, in_app_iff in nin.
          simpl in nin.
          intuition.
      - simpl in *.
        repeat rewrite andb_true_iff in *.
        repeat rewrite map_app in H2.
        apply in_in_app_false in H2.
        destruct H2 as [? HH].
        repeat rewrite nin_app_or in H4.
        autorewrite with fresh_bindings in *. 
        apply in_in_app_false in HH.
        destruct H4 as [[??][??]].
        destruct H as [[??]?].
        destruct H1 as [[[??]?][[??]?]].
        specialize (IHn1 b x xv d).
        rewrite IHn1 by intuition.
        destruct ((camp_eval h cenv (nnrcToCamp_ns n1) (rec_sort b) d));
          simpl in *; intuition.
        destruct res; simpl; trivial.
        destruct b0; simpl; 
          repeat rewrite merge_bindings_nil_r.
        + rewrite drec_sort_drec_sort_concat, drec_sort_idempotent.
          specialize (IHn2 b x xv d).
          rewrite IHn2 by intuition.
          destruct  (camp_eval h cenv (nnrcToCamp_ns n2) (rec_sort b) d); simpl in *; intuition.
        + rewrite drec_sort_drec_sort_concat, drec_sort_idempotent.
          specialize (IHn3 b x xv d).
          rewrite IHn3 by intuition.
          trivial.
      - simpl in *.
        repeat rewrite andb_true_iff in *.
        destruct H as [[[[inv inv0]sn1]sn2]sn3].
        match_destr_in inv; match_destr_in inv0.
        autorewrite with fresh_bindings in H1.
        destruct H1 as [?[[?[??]][?[??]]]].
        rewrite in_app_iff in H4.
        rewrite IHn1; trivial.
        + {unfold bindpr. match_destr; simpl; trivial. destruct res; simpl; trivial.
           - repeat rewrite merge_bindings_single_nin; trivial.
             cut ( (rec_concat_sort (rec_concat_sort b ((let_var x, xv) :: nil))
                                    ((loop_var v, res) :: nil)) =
                   (rec_concat_sort (rec_concat_sort b ((loop_var v, res)::nil))
                                    ((let_var x, xv) :: nil))).
             + intros re1; rewrite re1.
               specialize (IHn2 (rec_concat_sort b ((loop_var v, res)::nil)) x xv res).
               cut_to IHn2; trivial.
               * rewrite drec_sort_drec_sort_concat in IHn2.
                 unfold rec_concat_sort in IHn2 |- *.
                 repeat rewrite rec_sort_rec_sort_app1 in IHn2.
                 repeat rewrite rec_sort_rec_sort_app1.
                 destruct  (camp_eval h cenv (nnrcToCamp_ns n2)
                                      (rec_sort
                                         ((b ++ (loop_var v, res) :: nil) ++ (let_var x, xv) :: nil))
                                      res);
                   destruct (camp_eval h cenv (nnrcToCamp_ns n2)
                                       (rec_sort (b ++ (loop_var v, res) :: nil)) res);
                   simpl in *; intuition.
               * apply (drec_concat_sort_sorted (odt:=ODT_string)).
               * unfold rec_concat_sort.
                 rewrite fresh_bindings_domain_drec_sort,
                 domain_app, fresh_bindings_app.
                 split; trivial; simpl.
                 unfold fresh_bindings; intros.
                 simpl in H11.
                 destruct H11; [ | intuition ].
                 eelim loop_let_var_distinct.
                 eauto.
               * intros ? inn.
                 unfold rec_concat_sort in inn.
                 rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
                 simpl in inn.
                 destruct inn as [?|[?|?]].
                 specialize (H2 _ H11).
                 repeat rewrite map_app, in_app_iff in H2.
                 repeat (apply not_or in H2; let x := fresh "GG" in
                                             destruct H2 as [x H2]).
                 trivial.
                 subst.
                 rewrite in_map_iff.
                 intros [?[injj ?]].
                 apply loop_var_inj in injj; subst. eauto.
                 intuition.
               * unfold rec_concat_sort.
                 rewrite <- rec_sort_perm; trivial;
                   rewrite domain_app;
                   rewrite Permutation_app_comm;
                   simpl; constructor; auto 1;
                     intro inn; specialize (H2 _ inn);
                       apply not_or in H2; intuition.
               * simpl in H4.
                 repeat (apply not_or in H4; let x := fresh "GG" in
                                             destruct H4 as [x H4]).
                 repeat rewrite in_app_iff in H4.
                 apply not_or in H4. destruct H4 as [? ?].
                 trivial.
               * unfold rec_concat_sort.
                 rewrite in_dom_rec_sort, domain_app, in_app_iff.
                 repeat rewrite map_app in H2.
                 simpl. destruct 1 as [inn|[inn|?]]; trivial.
                 specialize (H2 _ inn);
                   repeat (apply not_or in H2; let x := fresh "GG" in
                                               destruct H2 as [x H2];
                                               repeat rewrite in_app_iff in H2).
                 congruence.
                 eapply loop_let_var_distinct; eauto.
             + unfold rec_concat_sort.
               repeat rewrite rec_sort_rec_sort_app1.
               apply drec_sort_perm_eq.
               * repeat rewrite domain_app; simpl.
                 rewrite Permutation_app_comm.
                 constructor.
                 simpl; rewrite in_app_iff; simpl; intros [inn|[inn|?]]; trivial.
                 specialize (H2 _ inn).
                 repeat (apply not_or in H2; let x := fresh "GG" in
                                             destruct H2 as [x H2];
                                             repeat rewrite in_app_iff in H2).
                 congruence.
                 eapply loop_let_var_distinct; eauto.
                 rewrite Permutation_app_comm.
                 constructor; trivial.
               * repeat rewrite app_ass. apply Permutation_app; trivial.
                 apply Permutation_app_comm.
             + rewrite in_dom_rec_sort. intros inn; specialize (H2 _ inn).
               repeat (apply not_or in H2; let x := fresh "GG" in
                                           destruct H2 as [x H2];
                                           repeat rewrite in_app_iff in H2).
               congruence.
             + unfold rec_concat_sort.
               rewrite in_dom_rec_sort, domain_app, in_app_iff.
               simpl.
               intros [inn|[inn|?]]; trivial.
               specialize (H2 _ inn).
               repeat (apply not_or in H2; let x := fresh "GG" in
                                           destruct H2 as [x H2];
                                           repeat rewrite in_app_iff in H2).
               congruence.
               eapply loop_let_var_distinct; eauto.
           - repeat rewrite merge_bindings_single_nin; trivial.
             cut ( (rec_concat_sort (rec_concat_sort b ((let_var x, xv) :: nil))
                                    ((loop_var v0, res) :: nil)) =
                   (rec_concat_sort (rec_concat_sort b ((loop_var v0, res)::nil))
                                    ((let_var x, xv) :: nil))).
             + intros re1; rewrite re1.
               rewrite IHn3; trivial.
               * rewrite drec_sort_drec_sort_concat.
                 unfold rec_concat_sort.
                 rewrite rec_sort_rec_sort_app1.
                 reflexivity.
               * apply (drec_concat_sort_sorted (odt:=ODT_string)).
               * unfold rec_concat_sort.
                 rewrite fresh_bindings_domain_drec_sort,
                 domain_app, fresh_bindings_app.
                 split; trivial; simpl.
                 unfold fresh_bindings; intros.
                 simpl in H11.
                 destruct H11; [ | intuition ].
                 eelim loop_let_var_distinct.
                 eauto.
               * intros ? inn.
                 unfold rec_concat_sort in inn.
                 rewrite in_dom_rec_sort, domain_app, in_app_iff in inn.
                 simpl in inn.
                 destruct inn as [?|[?|?]].
                 specialize (H2 _ H11).
                 repeat rewrite map_app, in_app_iff in H2.
                 repeat (apply not_or in H2; let x := fresh "GG" in
                                             destruct H2 as [x H2]).
                 trivial.
                 subst.
                 rewrite in_map_iff.
                 intros [?[injj ?]].
                 apply loop_var_inj in injj; subst. eauto.
                 intuition.
               * unfold rec_concat_sort.
                 rewrite <- rec_sort_perm; trivial;
                   rewrite domain_app;
                   rewrite Permutation_app_comm;
                   simpl; constructor; auto 1;
                     intro inn; specialize (H2 _ inn);
                       apply not_or in H2; intuition.
               * simpl in H4.
                 repeat (apply not_or in H4; let x := fresh "GG" in
                                             destruct H4 as [x H4]).
                 repeat rewrite in_app_iff in H4.
                 apply not_or in H4. simpl in H4. destruct H4 as [? ?].
                 apply not_or in H11. destruct H11.
                 trivial.
               * unfold rec_concat_sort.
                 rewrite in_dom_rec_sort, domain_app, in_app_iff.
                 repeat rewrite map_app in H2.
                 simpl. destruct 1 as [inn|[inn|?]]; trivial.
                 specialize (H2 _ inn);
                   repeat (apply not_or in H2; let x := fresh "GG" in
                                               destruct H2 as [x H2];
                                               repeat rewrite in_app_iff in H2).
                 congruence.
                 eapply loop_let_var_distinct; eauto.
             + unfold rec_concat_sort.
               repeat rewrite rec_sort_rec_sort_app1.
               apply drec_sort_perm_eq.
               * repeat rewrite domain_app; simpl.
                 rewrite Permutation_app_comm.
                 constructor.
                 simpl; rewrite in_app_iff; simpl; intros [inn|[inn|?]]; trivial.
                 specialize (H2 _ inn).
                 repeat (apply not_or in H2; let x := fresh "GG" in
                                             destruct H2 as [x H2];
                                             repeat rewrite in_app_iff in H2).
                 congruence.
                 eapply loop_let_var_distinct; eauto.
                 rewrite Permutation_app_comm.
                 constructor; trivial.
               * repeat rewrite app_ass. apply Permutation_app; trivial.
                 apply Permutation_app_comm.
             + rewrite in_dom_rec_sort. intros inn; specialize (H2 _ inn).
               repeat (apply not_or in H2; let x := fresh "GG" in
                                           destruct H2 as [x H2];
                                           repeat rewrite in_app_iff in H2).
               congruence.
             + unfold rec_concat_sort.
               rewrite in_dom_rec_sort, domain_app, in_app_iff.
               simpl.
               intros [inn|[inn|?]]; trivial.
               specialize (H2 _ inn).
               repeat (apply not_or in H2; let x := fresh "GG" in
                                           destruct H2 as [x H2];
                                           repeat rewrite in_app_iff in H2).
               congruence.
               eapply loop_let_var_distinct; eauto.
          }
        + intros ? inn inn2.
          rewrite in_map_iff in inn2.
          destruct inn2 as [? [? inn2]]; subst.
          specialize (H2 _ inn).
          repeat (apply not_or in H2; let x := fresh "GG" in
                                      destruct H2 as [x H2];
                                      repeat rewrite map_app, in_app_iff in H2).
          apply GG1. apply in_map_iff.
          eauto. 
        + unfold fresh_bindings in *. eauto.
    Qed.
    
    Lemma camp_eval_mapall_let_cons h cenv p bind a l :
      is_list_sorted ODT_lt_dec (domain bind) = true ->
      fresh_bindings (domain bind) (mapall_let p) -> 
      NoDup (domain bind) ->
      camp_eval h cenv (mapall_let p) bind (dcoll (a::l)) =
      match camp_eval h cenv p bind a, (camp_eval h cenv (mapall_let p) bind (dcoll l)) with
      | Success x', Success (dcoll l') =>  Success (dcoll (x'::l'))
      | RecoverableError, Success (dcoll l') => RecoverableError
      | Success a, RecoverableError => RecoverableError
      | RecoverableError,  RecoverableError => RecoverableError 
      | TerminalError , _ => TerminalError
      | _, TerminalError => TerminalError 
      | RecoverableError,  Success _ => TerminalError
      | Success _, Success _ => TerminalError
      end.
    Proof.
      Opaque data_eq_dec.
      simpl. intros.
      assert (nin:~ In (fresh_let_var "ma$" (let_vars p)) (domain bind)).
      unfold mapall_let in *.
      autorewrite with fresh_bindings in *.
      intuition.
      unfold fresh_let_var, let_var in H0.
      eapply H0; trivial; reflexivity.
      case_eq (camp_eval h cenv p bind a); simpl; intros; trivial.
      - case_eq (gather_successes (map (camp_eval h cenv p bind) l)); simpl; trivial; intros.
        rewrite merge_bindings_single_nin by trivial.
        rewrite edot_fresh_concat_right_single by trivial.
        simpl.
        destruct (data_eq_dec (dnat (Z.pos (Pos.of_succ_nat (bcount l))))
                              (dnat (Z.of_nat (bcount res)))).
        trivial.
        + generalize (gather_successes_le (camp_eval h cenv p bind) l); intros.
          specialize (H4 _ H3).
          inversion e.
          assert False by (apply (bcount_false1 l res); assumption); contradiction.
        + simpl.
          destruct (data_eq_dec (dnat (Z.of_nat (bcount l)))
                                (dnat (Z.of_nat (bcount res))));
            simpl; trivial.
          inversion e.
          rewrite merge_bindings_nil_r.
          rewrite sort_sorted_is_id; trivial.
          rewrite edot_fresh_concat_right_single; trivial.
      - case_eq (gather_successes (map (camp_eval h cenv p bind) l)); simpl; trivial; intros.
        rewrite merge_bindings_single_nin by trivial.
        rewrite edot_fresh_concat_right_single by trivial.
        simpl.
        destruct (data_eq_dec (dnat (Z.pos (Pos.of_succ_nat (bcount l))))
                              (dnat (Z.pos (Pos.of_succ_nat (bcount res0))))).
        trivial; simpl.
        + rewrite merge_bindings_nil_r.
          rewrite sort_sorted_is_id; trivial.
          rewrite edot_fresh_concat_right_single; trivial. simpl.
          rewrite merge_bindings_single_nin by trivial.
          rewrite edot_fresh_concat_right_single; trivial.
          simpl.
          inversion e.
          destruct (data_eq_dec (dnat (Z.of_nat (bcount l)))
                                (dnat (Z.of_nat (bcount res0)))); simpl; trivial.
          * rewrite merge_bindings_nil_r.
            rewrite sort_sorted_is_id; trivial.
            rewrite edot_fresh_concat_right_single; trivial.
          * inversion e.
            assert (bcount l = bcount res0)
              by apply (pos_succ_nat_inv (bcount l) (bcount res0) H6).
            rewrite H4 in *. congruence.
        + rewrite merge_bindings_single_nin by trivial.
          rewrite edot_fresh_concat_right_single; trivial.
          simpl.
          destruct (data_eq_dec (dnat (Z.of_nat (bcount l)))
                                (dnat (Z.of_nat (bcount res0))));
            simpl; trivial.
          inversion e.
          assert (bcount l = bcount res0)
            by apply (of_nat_inv (bcount l) (bcount res0) H5).
          congruence.
    Qed.

    Transparent data_eq_dec.

    Lemma camp_eval_mapall_let h cenv p bind l :
      is_list_sorted ODT_lt_dec (domain bind) = true ->
      fresh_bindings (domain bind) (mapall_let p) -> 
      NoDup (domain bind) ->
      camp_eval h cenv (mapall_let p) bind (dcoll l) = liftpr dcoll (prmapM (map (camp_eval h cenv p bind) l)).
    Proof.
      revert p bind.
      induction l; intros.
      - simpl.
        assert (nin:~ In (fresh_let_var "ma$" (let_vars p)) (domain bind)).
        unfold mapall_let in *.
        autorewrite with fresh_bindings in *.
        intuition. unfold fresh_let_var, let_var in H0.
        eapply H0; trivial; reflexivity.
        rewrite merge_bindings_single_nin by trivial.
        rewrite edot_fresh_concat_right_single by trivial.
        simpl. 
        rewrite merge_bindings_nil_r.
        rewrite drec_sort_drec_sort_concat.
        rewrite edot_fresh_concat_right_single by trivial.
        trivial.
      - rewrite camp_eval_mapall_let_cons by trivial.
        rewrite IHl by trivial.
        simpl.
        destruct (camp_eval h cenv p bind a); simpl; trivial;
          destruct (prmapM (map (camp_eval h cenv p bind) l)); simpl; trivial.
    Qed.

    Lemma camp_eval_mapall_let_mapall h cenv p b d:
      is_list_sorted ODT_lt_dec (domain b) = true ->
      fresh_bindings (domain b) (mapall_let p) -> 
      NoDup (domain b) ->
      (camp_eval h cenv (mapall_let p) b d) = (camp_eval h cenv (mapall p) b d).
    Proof.
      intros.
      destruct d; try solve[simpl; trivial].
      rewrite camp_eval_mapall by trivial.
      rewrite camp_eval_mapall_let by trivial.
      reflexivity.
    Qed.

    Lemma let_vars_let_to_naive x n :
      In (let_var x) (let_vars (nnrcToCamp_ns n)) ->
      In (let_var x) (let_vars (nnrcToCamp_ns_let n)).
    Proof.
      revert x.
      induction n; simpl; trivial; intros;
        repeat (repeat rewrite in_app_iff in *; simpl in *); intuition.
    Qed.

    Lemma fresh_bindings_let_to_naive l n :
      fresh_bindings l (nnrcToCamp_ns_let n) ->
      fresh_bindings l (nnrcToCamp_ns n).
    Proof.
      unfold fresh_bindings; intros.
      specialize (H _ H0).
      intros inn.
      apply H.
      apply let_vars_let_to_naive; trivial.
    Qed.

    Instance map_forall2_prop {A B} (f:B->B->Prop) (g:A->B) : Proper (Forall2 (fun x y => f (g x) (g y)) ==> (Forall2 f)) (map g).
    Proof.
      unfold Proper, respectful.
      induction x; destruct y; simpl; inversion 1; trivial; subst; eauto.
    Qed.
  
    Lemma nnrcToCamp_ns_let_equiv h cenv n b d :
      is_list_sorted ODT_lt_dec (domain b) = true ->
      fresh_bindings (domain b) (nnrcToCamp_ns_let n) ->
      NoDup (domain b) ->
      shadow_free n = true ->
      (forall x, In x (domain b) -> ~ In x (map loop_var (nnrc_bound_vars n))) ->
      camp_eval h cenv (nnrcToCamp_ns_let n) b d = camp_eval h cenv (nnrcToCamp_ns n) b d.
    Proof.
      Hint Resolve drec_sort_sorted fresh_bindings_let_to_naive.

      revert b d. 
      induction n; intros; trivial; simpl in H0;
        autorewrite with fresh_bindings in H0; try reflexivity.
      - simpl in *. 
        repeat rewrite andb_true_iff in *; intuition.
        rewrite IHn1, IHn2; intuition.
        + apply (H3 _ H2).
          rewrite map_app, in_app_iff. intuition.
        + apply (H3 _ H2).
          rewrite map_app, in_app_iff. intuition.
      - simpl in *. 
        rewrite IHn; intuition.
      - simpl in *. repeat rewrite andb_true_iff in *. intuition.
        rewrite IHn1; intuition.
        assert (vnin:~ In (loop_var v) (domain b)) by eauto.
        destruct (camp_eval h cenv (nnrcToCamp_ns n1) b d); simpl; trivial.
        + repeat rewrite merge_bindings_single_nin by trivial.
          apply IHn2; trivial; intros.
          * apply (drec_concat_sort_sorted (odt:=ODT_string)).
          * unfold fresh_bindings in *; intros ? nin.
            unfold rec_concat_sort in nin.
            rewrite drec_sort_equiv_domain in nin.
            rewrite domain_app, in_app_iff in nin.
            simpl in *.
            intuition.
            destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
              intuition.
            apply (H7 _ H9). simpl; intuition.
            eapply loop_let_var_distinct; eauto.
          * eauto 2.
          * unfold rec_concat_sort in H0.
            rewrite drec_sort_equiv_domain in H0.
            rewrite domain_app, in_app_iff in H0.
            simpl in *.
            intuition. 
            destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
              intuition.
            apply (H3 _ H10). rewrite map_app, in_app_iff.
            intuition.
            subst.
            destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
              intuition.
            apply in_map_iff in H9.
            destruct H9 as [vv [vveq vvin]].
            apply loop_var_inj in vveq; subst. intuition.
        + apply (H3 _ H0). rewrite map_app. intuition.
      - Opaque mapall_let mapall.
        simpl in *. repeat rewrite andb_true_iff in *. intuition.
        rewrite IHn1; intuition.
        + destruct (camp_eval h cenv (nnrcToCamp_ns n1) b d); simpl; trivial.
          Transparent mapall_let mapall.
          destruct res;
            try solve [auto 2; simpl; trivial].
          rewrite camp_eval_mapall_let_mapall; 
            repeat rewrite camp_eval_mapall; auto 3.
          f_equal; f_equal.
          assert (vnin:~ In (loop_var v) (domain b)) by eauto.
          apply map_ext; intros.
          simpl.
          repeat rewrite merge_bindings_single_nin by trivial.
          apply IHn2; trivial; intros.
          * apply (drec_concat_sort_sorted (odt:=ODT_string)).
          * unfold fresh_bindings in *; intros ? nin.
            unfold rec_concat_sort in nin.
            rewrite drec_sort_equiv_domain in nin.
            rewrite domain_app, in_app_iff in nin.
            simpl in *.
            intuition.
            destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
              intuition.
            apply (H5 _ H8). simpl; intuition.
            eapply loop_let_var_distinct; eauto.
          * eauto 2.
          * unfold rec_concat_sort in H0.
            rewrite drec_sort_equiv_domain in H0.
            rewrite domain_app, in_app_iff in H0.
            simpl in *.
            intuition. 
            destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
              intuition.
            apply (H3 _ H9). rewrite map_app, in_app_iff.
            intuition.
            subst.
            destruct (in_dec string_eqdec v (nnrc_bound_vars n2));
              intuition.
            apply in_map_iff in H8.
            destruct H8 as [vv [vveq vvin]].
            apply loop_var_inj in vveq; subst. intuition.
        + apply (H3 _ H0). rewrite map_app. intuition.
      - simpl in *. 
        repeat rewrite andb_true_iff in *; intuition.
        assert(nin:~ In
                  (fresh_let_var "if$" 
                                 (let_vars (nnrcToCamp_ns_let n1) ++
                                           let_vars (nnrcToCamp_ns_let n2) ++ let_vars (nnrcToCamp_ns_let n3)))
                  (domain b)).
        unfold mapall_let in *.
        autorewrite with fresh_bindings in *.
        intuition. eapply H2. reflexivity.
        trivial.
        rewrite IHn1; intuition.
        destruct (camp_eval h cenv (nnrcToCamp_ns n1) b d); trivial.
        simpl.
        rewrite merge_bindings_single_nin by trivial.
        rewrite edot_fresh_concat_right_single by trivial.
        destruct res; trivial.
        destruct b0; simpl.
        + repeat rewrite merge_bindings_nil_r.
          cut (
              (camp_eval h cenv (nnrcToCamp_ns_let n2)
                         (rec_sort
                            (rec_concat_sort b
                                             ((fresh_let_var "if$"
                                                             (let_vars (nnrcToCamp_ns_let n1) ++
                                                                       let_vars (nnrcToCamp_ns_let n2) ++
                                                                       let_vars (nnrcToCamp_ns_let n3)), 
                                               dbool true) :: nil))) d) =
              (camp_eval h cenv (nnrcToCamp_ns n2)
                         (rec_sort b) d)).
          intros HH; rewrite HH.
          match_destr.
          rewrite IHn2; auto.
          * rewrite drec_sort_drec_sort_concat.
            rewrite fresh_let_var_as_let.
            rewrite camp_eval_nnrcToCamp_ns_ignored_let_binding; unfold rec_sort; intuition.
            apply (H3 _ H4). repeat rewrite map_app, in_app_iff; intuition.
            apply let_vars_let_to_naive in H4.
            unfold let_var in H4.
            rewrite <- append_ass in H4.
            apply (fresh_let_var_fresh
                     "if$"
                     (let_vars (nnrcToCamp_ns_let n1) ++
                               let_vars (nnrcToCamp_ns_let n2) ++ let_vars (nnrcToCamp_ns_let n3))); unfold fresh_let_var, fresh_var.
            repeat rewrite in_app_iff.
            intuition.
          * apply (drec_sort_sorted (odt:=ODT_string)).
          * unfold rec_concat_sort.
            autorewrite with fresh_bindings.
            simpl. 
            autorewrite with fresh_bindings.
            intuition.
            unfold fresh_bindings; intros.
            simpl in *; intuition.
            rewrite <- H15 in H14.
            eelim (fresh_let_var_fresh); eauto.
          * eauto 2.
          * intros.
            rewrite drec_sort_drec_sort_concat in H4.
            unfold rec_concat_sort in H4.
            rewrite drec_sort_equiv_domain in H4.
            rewrite domain_app, in_app_iff in H4.
            simpl in *. intuition.
            apply (H3 _ H15).
            repeat rewrite map_app, in_app_iff.
            intuition.
            subst.
            apply in_map_iff in H14.
            destruct H14 as [xx [xxeq xxin]].
            rewrite fresh_let_var_as_let in xxeq.
            eelim loop_let_var_distinct; eauto.
        + simpl;repeat rewrite merge_bindings_nil_r.
          rewrite IHn3; auto.
          * rewrite drec_sort_drec_sort_concat.
            rewrite fresh_let_var_as_let.
            rewrite camp_eval_nnrcToCamp_ns_ignored_let_binding; unfold rec_sort; intuition.
            apply (H3 _ H4).   
            repeat rewrite map_app, in_app_iff.
            intuition.
            apply let_vars_let_to_naive in H4.
            unfold let_var in H4.
            rewrite <- append_ass in H4.
            apply (fresh_let_var_fresh "if$" (let_vars (nnrcToCamp_ns_let n1) ++
                                                       let_vars (nnrcToCamp_ns_let n2) ++ let_vars (nnrcToCamp_ns_let n3))).
            repeat rewrite in_app_iff.
            intuition.
          * apply (drec_sort_sorted (odt:=ODT_string)).
          * rewrite drec_sort_drec_sort_concat.
            unfold rec_concat_sort.
            rewrite drec_sort_equiv_domain.
            rewrite domain_app.
            simpl. unfold fresh_bindings in *; intros.
            rewrite in_app_iff in H4.
            intuition. eauto.
            simpl in H15; intuition.
            rewrite <- H4 in *.
            eelim (fresh_let_var_fresh); eauto.   
          * eauto 2.
          * intros.
            rewrite drec_sort_drec_sort_concat in H4.
            unfold rec_concat_sort in H4.
            rewrite drec_sort_equiv_domain in H4.
            rewrite domain_app in H4.
            rewrite in_app_iff in H4. simpl in H4.
            intuition.
            apply (H3 _ H15).   
            repeat rewrite map_app, in_app_iff.
            intuition.
            rewrite <- H4 in *.
            apply in_map_iff in H14.
            destruct H14 as [xx [xxeq xxin]].
            rewrite fresh_let_var_as_let in xxeq.
            eelim loop_let_var_distinct; eauto.
        + apply (H3 _ H4).   
          repeat rewrite map_app, in_app_iff.
          intuition.
      - destruct H0 as [?[[?[??]][?[??]]]].
        simpl in *.
        repeat rewrite andb_true_iff in H2.
        destruct H2 as [[[[inn1 inn2]sn1]sn2]sn3].
        match_destr_in inn1; match_destr_in inn2.
        repeat rewrite map_app in H3.
        apply in_in_cons_cons_app_app_false in H3.
        destruct H3 as [?[?[?[??]]]].
        simpl. rewrite IHn1; trivial.
        + unfold bindpr. match_destr; simpl; trivial. destruct res; simpl; trivial.
          * rewrite merge_bindings_single_nin; trivial.
            specialize (IHn2  (rec_concat_sort b ((loop_var v, res) :: nil)) res).
            {
              cut_to IHn2; trivial.
              - destruct (  camp_eval h cenv (nnrcToCamp_ns_let n2)
                                      (rec_concat_sort b ((loop_var v, res) :: nil)) res);
                  destruct (  camp_eval h cenv (nnrcToCamp_ns n2)
                                        (rec_concat_sort b ((loop_var v, res) :: nil)) res); simpl in *;
                    trivial.
              - apply (drec_concat_sort_sorted (odt:=ODT_string)).
              - unfold rec_concat_sort. autorewrite with fresh_bindings.
                simpl. split; trivial.
                unfold fresh_bindings; simpl.
                intros ?[?|?]?; trivial.
                eapply loop_let_var_distinct; eauto.
              - eauto 2.
              - unfold rec_concat_sort. intros ? inn1' inn2'.
                rewrite drec_sort_equiv_domain in inn1'.
                rewrite domain_app, in_app_iff in inn1'.
                simpl in inn1'.
                destruct inn1' as [?|[?|?]]; trivial.
                + eauto 2.
                + apply in_map_iff in inn2'.
                  destruct inn2' as [? [injj inn2']]; subst.
                  apply loop_var_inj in injj. subst.
                  eauto.
            }
          * rewrite merge_bindings_single_nin; trivial.
            {apply IHn3; trivial.
             - apply (drec_concat_sort_sorted (odt:=ODT_string)).
             - unfold rec_concat_sort. autorewrite with fresh_bindings.
               simpl. split; trivial.
               unfold fresh_bindings; simpl.
               intros ?[?|?]?; trivial.
               eapply loop_let_var_distinct; eauto.
             - eauto 2.
             - unfold rec_concat_sort. intros ? inn1' inn2'.
               rewrite drec_sort_equiv_domain in inn1'.
               rewrite domain_app, in_app_iff in inn1'.
               simpl in inn1'.
               destruct inn1' as [?|[?|?]]; trivial.
               + eauto 2.
               + apply in_map_iff in inn2'.
                 destruct inn2' as [? [injj inn2']]; subst.
                 apply loop_var_inj in injj. subst.
                 eauto.
            }
    Qed.

    Lemma fresh_bindings_from_nnrc {A} e l :
      fresh_bindings (domain (@nnrc_to_camp_env A e)) l.
    Proof.
      unfold fresh_bindings, nnrc_to_camp_env, domain.
      rewrite map_map. simpl. intros.
      apply in_map_iff in H.
      destruct H as [? [??]].
      apply loop_let_var_distinct in H.
      intuition.
    Qed.
  
    (** Main lemmas for the correctness of the translation *)

    Lemma nnrcToCamp_let_ns_correct h cenv n env d :
      nnrcIsCore n ->
      shadow_free n = true ->
      NoDup (domain env) ->
      (forall x, In x (domain env) -> ~ In x (nnrc_bound_vars n)) ->
      (forall x, In x (domain (nnrc_to_camp_env env)) -> ~ In x (map loop_var (nnrc_bound_vars n))) ->
      cNNRC.nnrc_core_eval h cenv env n = pr2op (camp_eval h cenv (nnrcToCamp_ns_let n) (rec_sort (nnrc_to_camp_env env)) d).
    Proof.
      intros.
      rewrite (nnrcToCamp_sem_correct_ns _ cenv); auto.
      f_equal.
      rewrite nnrcToCamp_ns_let_equiv; eauto 2.
      - erewrite nnrcToCamp_data_indep; reflexivity.
      - rewrite fresh_bindings_domain_drec_sort.
        apply fresh_bindings_from_nnrc.
      - intros ? inn.
        apply -> (@in_dom_rec_sort string) in inn.
        eauto 2.
    Qed.

    Lemma nnrcToCamp_let_correct_messy h cenv avoid n env d :
      nnrcIsCore n ->
      NoDup (domain env) ->
      (forall x, In x (domain env) -> ~ In x (nnrc_bound_vars (unshadow_simpl avoid n))) ->
      (forall x, In x (domain (nnrc_to_camp_env env)) -> ~ In x (map loop_var (nnrc_bound_vars (unshadow_simpl avoid n)))) ->
      cNNRC.nnrc_core_eval h cenv env n = pr2op (camp_eval h cenv (nnrcToCamp_let avoid n) (rec_sort (nnrc_to_camp_env env)) d).
    Proof.
      intro Hiscore.
      intros.
      generalize (unshadow_simpl_preserve_core avoid n Hiscore); intros.
      generalize (nnrcToCamp_let_ns_correct h cenv (unshadow_simpl avoid n) env d
                                            H2 (unshadow_shadow_free _ _ _ _)); intros HH.
      unfold nnrcToCamp_let.
      unfold unshadow_simpl in HH.
      rewrite nnrc_core_unshadow_eval in HH.
      auto.
    Qed.

    (** This corresponds to Theorem 6.1 *)
    Theorem nnrcToCamp_let_correct h cenv n env d :
      nnrcIsCore n ->
      NoDup (domain env) ->
      cNNRC.nnrc_core_eval h cenv env n
      = pr2op (camp_eval h cenv (nnrcToCamp_let (domain env) n)
                         (rec_sort (nnrc_to_camp_env env)) d).
    Proof.
      Hint Resolve unshadow_avoid.
      intro Hiscore.
      intros.
      apply nnrcToCamp_let_correct_messy; unfold unshadow_simpl; auto.
      intros.
      unfold nnrc_to_camp_env, domain in H0.
      rewrite map_map in H0.
      apply in_map_iff in H0.
      destruct H0 as [? [? inn]]; subst.
      intro inn2.
      apply in_map_iff in inn2.
      destruct inn2 as [? [eq1 inn2]].
      simpl in eq1.
      apply loop_var_inj in eq1. subst.
      destruct x0.
      apply in_dom in inn.
      apply (unshadow_avoid _ _ _ _ _ inn inn2).
    Qed.

    Lemma nnrcToCamp_let_sem_correct_top_ns h cenv n :
      nnrcIsCore n ->
      shadow_free n = true ->
      cNNRC.nnrc_core_eval h cenv nil n =
      pr2op (camp_eval h cenv (nnrcToCamp_ns_let n) nil dunit).
    Proof.
      intro Hiscore.
      intros.
      rewrite (nnrcToCamp_sem_correct_top_ns _ cenv); auto.
      f_equal.
      rewrite nnrcToCamp_ns_let_equiv; eauto 2.
      simpl; autorewrite with fresh_bindings; trivial.
    Qed.

    Theorem nnrcToCamp_let_sem_correct_top h cenv n :
      nnrcIsCore n ->
      cNNRC.nnrc_core_eval h cenv nil n =
      pr2op (camp_eval h cenv (nnrcToCamp_let nil n) nil dunit).
    Proof.
      intros Hiscore.
      intros.
      generalize (unshadow_simpl_preserve_core nil n Hiscore); intros.
      generalize (nnrcToCamp_let_sem_correct_top_ns h cenv (unshadow_simpl nil n)
                                                    H (unshadow_shadow_free _ _ _ _)); intros H0.
      unfold nnrcToCamp_let.
      unfold unshadow_simpl in H0.
      rewrite nnrc_core_unshadow_eval in H0. trivial.
    Qed.
    
    (** Lemma and proof for the linear size of the translation *)

    Lemma nnrc_subst_var_size n v v' :
      nnrc_size (nnrc_subst n v (cNNRC.NNRCVar v')) = nnrc_size n.
    Proof.
      induction n; simpl; auto;
        repeat dest_eqdec; auto.
    Qed.

    Lemma nnrc_rename_lazy_size n v v' :
      nnrc_size (nnrc_rename_lazy n v v') = nnrc_size n.
    Proof.
      unfold nnrc_rename_lazy.
      match_destr.
      rewrite nnrc_subst_var_size.
      trivial.
    Qed.

    Lemma unshadow_size sep renamer avoid n :
      nnrc_size (unshadow sep renamer avoid n) = nnrc_size n.
    Proof.
      induction n; simpl; auto;
        (repeat match_destr; simpl;
         repeat rewrite nnrc_rename_lazy_size; auto).
    Qed.

    Lemma unshadow_simpl_size avoid n :
      nnrc_size (unshadow_simpl avoid n) = nnrc_size n.
    Proof.
      apply unshadow_size.
    Qed.

    Lemma nnrcToCamp_ns_let_size n : 
      camp_size (nnrcToCamp_ns_let n) <= 25 * nnrc_size n.
    Proof.
      induction n; simpl; try omega.
    Qed.

    Theorem nnrcToCamp_let_size avoid n : 
      camp_size (nnrcToCamp_let avoid n) <= 25 * nnrc_size n.
    Proof.
      unfold nnrcToCamp_let.
      generalize (nnrcToCamp_ns_let_size (unshadow_simpl avoid n)).
      rewrite unshadow_simpl_size.
      trivial.
    Qed.

  End trans_let.

  Section Top.

    Definition nnrc_core_to_camp_top (q:nnrc_core) :=
      lift_nnrc_core (nnrcToCamp_let nil) q.

    (* XXX Unfortunately, this is not true because of the lifting issues (CAMP evals to singletong collection at the moment. pr2op lifts differently from presult_to_result XXX *)
    (*
    Theorem nnrc_core_to_camp_top_correct
            (h:list (string*string)) (q:nnrc_core) (env:bindings) :
      camp_eval_top h (nnrc_core_to_camp_top q) env = nnrc_core_eval_top h q env.
    Proof.
      unfold camp_eval_top.
      unfold nnrc_core_to_camp_top.
      unfold nnrc_core_eval_top.
      unfold lift_nnrc_core.
      destruct q; simpl.
      rename x into qcore.
      rewrite nnrcToCamp_let_sem_correct_top; [|assumption].
      unfold pr2op.
      unfold presult_to_result.
      unfold camp_eval_top_to_presult.
      reflexivity.
    Qed. *)
    
  End Top.
End cNNRCtoCAMP.

