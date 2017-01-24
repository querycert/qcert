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

Section NNRC.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import Arith Max.

  Require Import Bool.

  Require Import Peano_dec.
  Require Import EquivDec Decidable.

  Require Import Utils BasicRuntime.
  Require Import cNNRC.

  (** Named Nested Relational Calculus - Extended *)

  Context {fruntime:foreign_runtime}.
  Context {h:brand_relation_t}.
  
  Section macros.
    (** e groupby[g,keys] ==
         LET $group0 := e
         IN { [ g: ]
                ⊕
              ♯flatten({ IF ($group3 = π[keys])
                         THEN {$group3}
                         ELSE {}
                       | $group3 ∈ $group0 })
            | $group2 ∈ ♯distinct({ π[keys]($group1) | $group1 ∈ $group0 }) }
    *)
    Definition nnrc_group_by (g:string) (sl:list string) (e:nnrc) : nnrc :=
      let t0 := "$group0"%string in
      let t1 := "$group1"%string in
      let t2 := "$group2"%string in
      let t3 := "$group3"%string in
      NNRCLet t0 e
             (NNRCFor t2
                     (NNRCUnop ADistinct
                              (NNRCFor t1 (NNRCVar t0) (NNRCUnop (ARecProject sl) (NNRCVar t1))))
                     (NNRCBinop AConcat
                               (NNRCUnop (ARec g)
                                        (NNRCUnop AFlatten
                                                 (NNRCFor t3 (NNRCVar t0)
                                                          (NNRCIf (NNRCBinop AEq (NNRCUnop (ARecProject sl) (NNRCVar t3)) (NNRCVar t2))
                                                                  (NNRCUnop AColl (NNRCVar t3))
                                                                  (NNRCConst (dcoll nil))))))
                               (NNRCVar t2))).
    
    Lemma nnrc_group_by_correct env
          (g:string) (sl:list string)
          (e:nnrc)
          (incoll outcoll:list data):
      nnrc_core_eval h env e = Some (dcoll incoll) ->
      group_by_nested_eval_table g sl incoll = Some outcoll -> 
      nnrc_core_eval h env (nnrc_group_by g sl e) = Some (dcoll outcoll).
    Proof.
      intros.
      unfold nnrc_group_by; simpl.
      rewrite H; simpl; clear H.
      apply (group_by_table_correct g sl incoll outcoll H0).
    Qed.

    Definition nnrc_group_by_from_nraenv (vid venv:var) (g:string) (sl:list string) (e:nnrc) :=
    (NNRCLet (fresh_var "tappe$" (vid :: venv :: nil))
       (NNRCUnop (ARec "$pregroup") e)
       (NNRCFor
          (fresh_var "tmap$"
             (vid :: fresh_var "tappe$" (vid :: venv :: nil) :: nil))
          (NNRCUnop ADistinct
             (NNRCFor
                (fresh_var "tmap$"
                   (vid :: fresh_var "tappe$" (vid :: venv :: nil) :: nil))
                (NNRCUnop (ADot "$pregroup")
                   (NNRCVar (fresh_var "tappe$" (vid :: venv :: nil))))
                (NNRCUnop (ARecProject sl)
                   (NNRCVar
                      (fresh_var "tmap$"
                         (vid
                          :: fresh_var "tappe$" (vid :: venv :: nil)
                             :: nil))))))
          (NNRCBinop AConcat
             (NNRCUnop (ARec g)
                (NNRCLet
                   (fresh_var "tappe$"
                      (fresh_var "tmap$"
                         (vid
                          :: fresh_var "tappe$" (vid :: venv :: nil)
                             :: nil)
                       :: fresh_var "tappe$" (vid :: venv :: nil) :: nil))
                   (NNRCBinop AConcat
                      (NNRCUnop (ARec "$key")
                         (NNRCVar
                            (fresh_var "tmap$"
                               (vid
                                :: fresh_var "tappe$" (vid :: venv :: nil)
                                   :: nil))))
                      (NNRCVar (fresh_var "tappe$" (vid :: venv :: nil))))
                   (NNRCUnop AFlatten
                      (NNRCFor
                         (fresh_var "tsel$"
                            (fresh_var "tmap$"
                               (vid
                                :: fresh_var "tappe$" (vid :: venv :: nil)
                                   :: nil)
                             :: fresh_var "tappe$"
                                  (fresh_var "tmap$"
                                     (vid
                                      :: fresh_var "tappe$"
                                           (vid :: venv :: nil) :: nil)
                                   :: fresh_var "tappe$"
                                        (vid :: venv :: nil) :: nil)
                                :: nil))
                         (NNRCUnop (ADot "$pregroup")
                            (NNRCVar
                               (fresh_var "tappe$"
                                  (fresh_var "tmap$"
                                     (vid
                                      :: fresh_var "tappe$"
                                           (vid :: venv :: nil) :: nil)
                                   :: fresh_var "tappe$"
                                        (vid :: venv :: nil) :: nil))))
                         (NNRCIf
                            (NNRCBinop AEq
                               (NNRCUnop (ARecProject sl)
                                  (NNRCVar
                                     (fresh_var "tsel$"
                                        (fresh_var "tmap$"
                                           (vid
                                            :: fresh_var "tappe$"
                                                (vid :: venv :: nil)
                                               :: nil)
                                         :: fresh_var "tappe$"
                                              (fresh_var "tmap$"
                                                (vid
                                                :: 
                                                fresh_var "tappe$"
                                                (vid :: venv :: nil)
                                                :: nil)
                                               :: 
                                               fresh_var "tappe$"
                                                (vid :: venv :: nil)
                                               :: nil) :: nil))))
                               (NNRCUnop (ADot "$key")
                                  (NNRCVar
                                     (fresh_var "tappe$"
                                        (fresh_var "tmap$"
                                           (vid
                                            :: fresh_var "tappe$"
                                                (vid :: venv :: nil)
                                               :: nil)
                                         :: fresh_var "tappe$"
                                              (vid :: venv :: nil) :: nil)))))
                            (NNRCUnop AColl
                               (NNRCVar
                                  (fresh_var "tsel$"
                                     (fresh_var "tmap$"
                                        (vid
                                         :: fresh_var "tappe$"
                                              (vid :: venv :: nil) :: nil)
                                      :: fresh_var "tappe$"
                                           (fresh_var "tmap$"
                                              (vid
                                               :: 
                                               fresh_var "tappe$"
                                                (vid :: venv :: nil)
                                               :: nil)
                                            :: fresh_var "tappe$"
                                                (vid :: venv :: nil)
                                               :: nil) :: nil))))
                            (NNRCConst (dcoll nil)))))))
             (NNRCVar
                (fresh_var "tmap$"
                   (vid :: fresh_var "tappe$" (vid :: venv :: nil) :: nil)))))).

    Lemma rmap1 sl l :
      (rmap
         (fun d1 : data =>
            match d1 with
            | dunit => None
            | dnat _ => None
            | dbool _ => None
            | dstring _ => None
            | dcoll _ => None
            | drec r => Some (drec (rproject r sl))
            | dleft _ => None
            | dright _ => None
            | dbrand _ _ => None
            | dforeign _ => None
            end) l) =
      (rmap
         (fun d1 : data =>
            olift
              (fun d0 : data =>
                 match d0 with
                 | dunit => None
                 | dnat _ => None
                 | dbool _ => None
                 | dstring _ => None
                 | dcoll _ => None
                 | drec r => Some (drec (rproject r sl))
                 | dleft _ => None
                 | dright _ => None
                 | dbrand _ _ => None
                 | dforeign _ => None
                 end) (Some d1)) l).
    Proof.
      apply rmap_ext; intros.
      reflexivity.
    Qed.

    Lemma pick_fresh_distinct_second v v1 v2 rest:
      exists v3,
        v3 = (fresh_var v (v1 :: v2 :: rest)) /\
        v2 <> v3.
    Proof.
      exists (fresh_var v (v1 :: v2 :: rest)).
      split;[reflexivity| ].
      apply fresh_var_fresh2.
    Qed.

    Lemma build_group_ext (x:data) (o1 o2:option data) :
      o1 = o2 ->
      match o1 with
      | Some dunit => None
      | Some (dnat _) => None
      | Some (dbool _) => None
      | Some (dstring _) => None
      | Some (dcoll _) => None
      | Some (drec r1) =>
        match x with
        | dunit => None
        | dnat _ => None
        | dbool _ => None
        | dstring _ => None
        | dcoll _ => None
        | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
        | dleft _ => None
        | dright _ => None
        | dbrand _ _ => None
        | dforeign _ => None
        end
      | Some (dleft _) => None
      | Some (dright _) => None
      | Some (dbrand _ _) => None
      | Some (dforeign _) => None
      | None => None
      end =
      match o2 with
      | Some dunit => None
      | Some (dnat _) => None
      | Some (dbool _) => None
      | Some (dstring _) => None
      | Some (dcoll _) => None
      | Some (drec r1) =>
        match x with
        | dunit => None
        | dnat _ => None
        | dbool _ => None
        | dstring _ => None
        | dcoll _ => None
        | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
        | dleft _ => None
        | dright _ => None
        | dbrand _ _ => None
        | dforeign _ => None
        end
      | Some (dleft _) => None
      | Some (dright _) => None
      | Some (dbrand _ _) => None
      | Some (dforeign _) => None
      | None => None
      end.
    Proof.
      intros Hinput; rewrite Hinput; clear Hinput.
      reflexivity.
    Qed.

    Lemma nnrc_core_eval_group_by_eq env (g:string) (sl:list string) (e1 e2:nnrc):
      nnrc_core_eval h env e1 = nnrc_core_eval h env e2 ->
      forall vid venv,
        nnrc_core_eval h env (nnrc_group_by g sl e1)
        = nnrc_core_eval h env (nnrc_group_by_from_nraenv vid venv g sl e2).
    Proof.
      intro Heval; intros.
      unfold nnrc_group_by, nnrc_group_by_from_nraenv.
      Opaque fresh_var.
      simpl.
      rewrite <- Heval; clear Heval.
      destruct (nnrc_core_eval h env e1); [|reflexivity]; simpl; clear e1 e2.
      generalize (fresh_var "tappe$" (vid :: venv :: nil)); intro v0.
      destruct (equiv_dec v0 v0); try congruence.
      destruct d; try reflexivity; simpl.
      generalize (pick_fresh_distinct_second "tmap$" vid v0 nil); intros Hpick.
      elim Hpick; clear Hpick; intro v1; intros.
      elim H; clear H; intros.
      assert ((fresh_var
           (String
              (Ascii.Ascii false false true false true true true false)
              (String
                 (Ascii.Ascii true false true true false true true false)
                 (String
                    (Ascii.Ascii true false false false false true true
                       false)
                    (String
                       (Ascii.Ascii false false false false true true true
                          false)
                       (String
                          (Ascii.Ascii false false true false false true
                             false false) EmptyString)))))
           (@cons string vid (@cons string v0 (@nil string)))) =
              fresh_var "tmap$" (vid :: v0 :: nil)).
      reflexivity.
      rewrite H1 in H; clear H1.
      rewrite <- H; clear H.
      destruct (equiv_dec v1 v1); try congruence; clear e0.
      rewrite <- rmap1.
      destruct (rmap
            (fun d1 : data =>
             match d1 with
             | dunit => None
             | dnat _ => None
             | dbool _ => None
             | dstring _ => None
             | dcoll _ => None
             | drec r => Some (drec (rproject r sl))
             | dleft _ => None
             | dright _ => None
             | dbrand _ _ => None
             | dforeign _ => None
             end) l); try reflexivity; simpl.
      f_equal.
      apply rmap_ext; intros. simpl.
      destruct (equiv_dec v0 v1); try congruence; clear c; simpl.
      destruct (equiv_dec (fresh_var "tappe$" (v1 :: v0 :: nil))
                          (fresh_var "tappe$" (v1 :: v0 :: nil))); try congruence;
      simpl; clear e0.
      unfold olift2.
      apply build_group_ext.
      f_equal.
      f_equal.
      f_equal.
      apply rmap_ext; intros.
      unfold olift.
      generalize (fresh_var "tappe$" (v1 :: v0 :: nil)); intros v2.
      destruct (equiv_dec (fresh_var "tsel$" (v1 :: v2 :: nil))
                          (fresh_var "tsel$" (v1 :: v2 :: nil))); try congruence;
      clear e0; simpl.
      generalize (pick_fresh_distinct_second "tsel$" v1 v2 nil); intros Hpick.
      elim Hpick; clear Hpick; intro v3; intros.
      elim H2; clear H2; intros.
      rewrite <- H2; clear H2.
      destruct (equiv_dec v2 v3); try congruence; clear c.
      simpl.
      reflexivity.
    Qed.

  End macros.

  Section translation.
    Fixpoint nnrc_ext_to_nnrc (e:nnrc) : nnrc :=
      match e with
      | NNRCVar v => NNRCVar v
      | NNRCConst d => NNRCConst d
      | NNRCBinop b e1 e2 =>
        NNRCBinop b (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2)
      | NNRCUnop u e1 =>
        NNRCUnop u (nnrc_ext_to_nnrc e1)
      | NNRCLet v e1 e2 =>
        NNRCLet v (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2)
      | NNRCFor v e1 e2 =>
        NNRCFor v (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2)
      | NNRCIf e1 e2 e3 =>
        NNRCIf (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2) (nnrc_ext_to_nnrc e3)
      | NNRCEither e1 v2 e2 v3 e3 =>
        NNRCEither (nnrc_ext_to_nnrc e1) v2 (nnrc_ext_to_nnrc e2) v3 (nnrc_ext_to_nnrc e3)
      | NNRCGroupBy g sl e1 =>
        nnrc_group_by g sl (nnrc_ext_to_nnrc e1)
      end.

    Lemma nnrc_ext_to_nnrc_is_core (e:nnrc) :
      nnrcIsCore (nnrc_ext_to_nnrc e).
    Proof.
      induction e; intros; simpl in *; auto.
      repeat (split; auto).
    Qed.
    
    Lemma core_nnrc_to_nnrc_ext_id (e:nnrc) :
      nnrcIsCore e ->
      (nnrc_ext_to_nnrc e) = e.
    Proof.
      intros.
      induction e; simpl in *.
      - reflexivity.
      - reflexivity.
      - elim H; intros.
        rewrite IHe1; auto; rewrite IHe2; auto.
      - rewrite IHe; auto.
      - elim H; intros.
        rewrite IHe1; auto; rewrite IHe2; auto.
      - elim H; intros.
        rewrite IHe1; auto; rewrite IHe2; auto.
      - elim H; intros.
        elim H1; intros.
        rewrite IHe1; auto; rewrite IHe2; auto; rewrite IHe3; auto.
      - elim H; intros.
        elim H1; intros.
        rewrite IHe1; auto; rewrite IHe2; auto; rewrite IHe3; auto.
      - contradiction. (* GroupBy case *)
    Qed.

    Lemma core_nnrc_to_nnrc_ext_idempotent (e1 e2:nnrc) :
      e1 = nnrc_ext_to_nnrc e2 ->
      nnrc_ext_to_nnrc e1 = e1.
    Proof.
      intros.
      apply core_nnrc_to_nnrc_ext_id.
      rewrite H.
      apply nnrc_ext_to_nnrc_is_core.
    Qed.

    Corollary core_nnrc_to_nnrc_ext_idempotent_corr (e:nnrc) :
      nnrc_ext_to_nnrc (nnrc_ext_to_nnrc e) = (nnrc_ext_to_nnrc e).
    Proof.
      apply (core_nnrc_to_nnrc_ext_idempotent _ e).
      reflexivity.
    Qed.
    
  End translation.

  Section semantics.
    (** Semantics of NNRCExt *)

    Definition nnrc_ext_eval (env:bindings) (e:nnrc) : option data :=
      nnrc_core_eval h env (nnrc_ext_to_nnrc e).

    Remark nnrc_ext_to_nnrc_eq (e:nnrc):
      forall env,
        nnrc_ext_eval env e = nnrc_core_eval h env (nnrc_ext_to_nnrc e).
    Proof.
      intros; reflexivity.
    Qed.

    Remark nnrc_to_nnrc_ext_eq (e:nnrc):
      nnrcIsCore e ->
      forall env,
        nnrc_core_eval h env e = nnrc_ext_eval env e.
    Proof.
      intros.
      unfold nnrc_ext_eval.
      rewrite core_nnrc_to_nnrc_ext_id.
      reflexivity.
      assumption.
    Qed.

    (* we are only sensitive to the environment up to lookup *)
    Global Instance nnrc_ext_eval_lookup_equiv_prop :
      Proper (lookup_equiv ==> eq ==> eq) nnrc_ext_eval.
    Proof.
      generalize nnrc_core_eval_lookup_equiv_prop; intros.
      unfold Proper, respectful, lookup_equiv in *; intros; subst.
      unfold nnrc_ext_eval.
      rewrite (H h x y H0 (nnrc_ext_to_nnrc y0) (nnrc_ext_to_nnrc y0)).
      reflexivity.
      reflexivity.
    Qed.
    
  End semantics.

  Section prop.
    Require Import cNNRCShadow.
    
    Lemma nnrc_ext_to_nnrc_free_vars_same e:
      nnrc_free_vars e = nnrc_free_vars (nnrc_ext_to_nnrc e).
    Proof.
      induction e; simpl; try reflexivity.
      - rewrite IHe1; rewrite IHe2; reflexivity.
      - assumption.
      - rewrite IHe1; rewrite IHe2; reflexivity.
      - rewrite IHe1; rewrite IHe2; reflexivity.
      - rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity.
      - rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity.
      - rewrite app_nil_r.
        assumption.
    Qed.

    Lemma nnrc_ext_to_nnrc_bound_vars_impl x e:
      In x (nnrc_bound_vars e) -> In x (nnrc_bound_vars (nnrc_ext_to_nnrc e)).
    Proof.
      induction e; simpl; unfold not in *; intros.
      - auto.
      - auto.
      - intuition.
        rewrite in_app_iff in H.
        rewrite in_app_iff.
        elim H; intros; auto.
      - intuition.
      - intuition.
        rewrite in_app_iff in H0.
        rewrite in_app_iff.
        elim H0; intros; auto.
      - intuition.
        rewrite in_app_iff in H0.
        rewrite in_app_iff.
        elim H0; intros; auto.
      - rewrite in_app_iff in H.
        rewrite in_app_iff in H.
        rewrite in_app_iff.
        rewrite in_app_iff.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
      - rewrite in_app_iff in H.
        rewrite in_app_iff in H.
        rewrite in_app_iff.
        rewrite in_app_iff.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
        right. right. auto.
        right. right. auto.
      - specialize (IHe H).
        right.
        rewrite in_app_iff.
        auto.
    Qed.

    Lemma nnrc_ext_to_nnrc_bound_vars_impl_not x e:
      ~ In x (nnrc_bound_vars (nnrc_ext_to_nnrc e)) -> ~ In x (nnrc_bound_vars e).
    Proof.
      unfold not.
      intros.
      apply H.
      apply nnrc_ext_to_nnrc_bound_vars_impl.
      assumption.
    Qed.

    Definition really_fresh_in_ext sep oldvar avoid e :=
      really_fresh_in sep oldvar avoid (nnrc_ext_to_nnrc e).
    
    Lemma really_fresh_from_free_ext sep old avoid (e:nnrc) :
      ~ In (really_fresh_in_ext sep old avoid e) (nnrc_free_vars (nnrc_ext_to_nnrc e)).
    Proof.
      unfold really_fresh_in_ext.
      intros inn1.
      apply (really_fresh_in_fresh sep old avoid (nnrc_ext_to_nnrc e)).
      repeat rewrite in_app_iff; intuition.
    Qed.

    Lemma nnrc_ext_to_nnrc_subst_comm e1 v1 e2:
      nnrc_subst (nnrc_ext_to_nnrc e1) v1 (nnrc_ext_to_nnrc e2) =
      nnrc_ext_to_nnrc (nnrc_subst e1 v1 e2).
    Proof.
      induction e1; simpl; try reflexivity.
      - destruct (equiv_dec v v1); reflexivity.
      - rewrite IHe1_1; rewrite IHe1_2; reflexivity.
      - rewrite IHe1; reflexivity.
      - rewrite IHe1_1.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite IHe1_2; reflexivity.
      - rewrite IHe1_1.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite IHe1_2; reflexivity.
      - rewrite IHe1_1; rewrite IHe1_2; rewrite IHe1_3; reflexivity.
      - rewrite IHe1_1.
        destruct (equiv_dec v v1);
          destruct (equiv_dec v0 v1);
          try reflexivity.
        rewrite IHe1_3; reflexivity.
        rewrite IHe1_2; reflexivity.
        rewrite IHe1_2; rewrite IHe1_3; reflexivity.
      - unfold nnrc_group_by.
        rewrite IHe1.
        unfold var in *.
        destruct (equiv_dec "$group0"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group1"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
    Qed.
        
    Lemma nnrc_ext_to_nnrc_rename_lazy_comm e v1 v2:
      nnrc_rename_lazy (nnrc_ext_to_nnrc e) v1 v2 =
      nnrc_ext_to_nnrc (nnrc_rename_lazy e v1 v2).
    Proof.
      induction e; unfold nnrc_rename_lazy in *; simpl; try reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        destruct (equiv_dec v v1); try reflexivity.
      - destruct (equiv_dec v1 v2); reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        simpl. rewrite <- IHe1; rewrite <- IHe2; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        simpl. rewrite <- IHe; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe1.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite <- IHe1; reflexivity.
        rewrite <- IHe1; rewrite <- IHe2; simpl; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe1.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite <- IHe1; reflexivity.
        rewrite <- IHe1; rewrite <- IHe2; simpl; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        simpl; rewrite <- IHe1; rewrite <- IHe2; rewrite <- IHe3.
        reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe1.
        destruct (equiv_dec v v1); try reflexivity.
        destruct (equiv_dec v0 v1); try reflexivity.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        rewrite <- IHe3.
        reflexivity.
        destruct (equiv_dec v0 v1); try reflexivity.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        rewrite <- IHe2.
        reflexivity.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        rewrite <- nnrc_ext_to_nnrc_subst_comm; simpl.
        rewrite <- IHe2.
        rewrite <- IHe3.
        reflexivity.
      - simpl.
        unfold nnrc_group_by.
        destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe.
        simpl; unfold nnrc_group_by.
        unfold var in *.
        destruct (equiv_dec "$group0"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group1"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
    Qed.

    (* unshadow properties for extended NNRC *)
    Lemma unshadow_over_nnrc_ext_idem sep renamer avoid e:
      (nnrc_ext_to_nnrc (unshadow sep renamer avoid (nnrc_ext_to_nnrc e))) =
      (unshadow sep renamer avoid (nnrc_ext_to_nnrc e)).
    Proof.
      generalize (unshadow_preserve_core sep renamer avoid (nnrc_ext_to_nnrc e)); intros.
      rewrite core_nnrc_to_nnrc_ext_id.
      reflexivity.
      apply H.
      apply nnrc_ext_to_nnrc_is_core.
    Qed.

    Lemma nnrc_ext_eval_cons_subst e env v x v' :
      ~ (In v' (nnrc_free_vars e)) ->
      ~ (In v' (nnrc_bound_vars e)) ->
      nnrc_ext_eval ((v',x)::env) (nnrc_subst e v (NNRCVar v')) = 
      nnrc_ext_eval ((v,x)::env) e.
    Proof.
      revert env v x v'.
      nnrc_cases (induction e) Case; simpl; unfold equiv_dec;
        unfold nnrc_ext_eval in *; unfold var in *; trivial; intros; simpl.
      - Case "NNRCVar"%string.
        intuition. destruct (string_eqdec v0 v); simpl; subst; intuition.
        + match_destr; intuition. simpl. dest_eqdec; intuition.
          rewrite e0.
          destruct (equiv_dec v0 v0); try congruence.
        + match_destr; subst; simpl; dest_eqdec; intuition.
          destruct (equiv_dec v v0); try congruence.
      - Case "NNRCBinop"%string.
        rewrite nin_app_or in H. f_equal; intuition.
      - f_equal; intuition.
      - rewrite nin_app_or in H. rewrite IHe1 by intuition.
        case_eq (nnrc_core_eval h ((v0, x) :: env) (nnrc_ext_to_nnrc e1)); trivial; intros d deq.
        destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
        + generalize (@nnrc_core_eval_remove_duplicate_env _ h nil v0 d nil); 
            simpl; intros rr1; rewrite rr1.
          destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
          * generalize (@nnrc_core_eval_remove_duplicate_env _ h nil v' d nil); 
              simpl; auto.
          * generalize (@nnrc_core_eval_remove_free_env _ h ((v0,d)::nil)); 
              simpl; intros rr2; apply rr2. intuition.
            elim H3. apply remove_in_neq; auto.
            rewrite nnrc_ext_to_nnrc_free_vars_same; auto.
        + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
          generalize (@nnrc_core_eval_swap_neq _ h nil v d); simpl; intros rr2; 
            repeat rewrite rr2 by trivial.
          apply IHe2.
          * intros nin; intuition. elim H2; apply remove_in_neq; auto.
          * intuition.
      - rewrite nin_app_or in H. rewrite IHe1 by intuition.
        case_eq (nnrc_core_eval h ((v0, x) :: env) (nnrc_ext_to_nnrc e1)); trivial; intros d deq.
        destruct d; trivial.
        f_equal.
        apply rmap_ext; intros.
        destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
        + generalize (@nnrc_core_eval_remove_duplicate_env _ h nil v0 x0 nil); 
            simpl; intros rr1; rewrite rr1.
          destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
          * generalize (@nnrc_core_eval_remove_duplicate_env _ h nil v' x0 nil); 
              simpl; auto.
          * generalize (@nnrc_core_eval_remove_free_env _ h ((v0,x0)::nil)); 
              simpl; intros rr2; apply rr2. intuition.
            elim H4. apply remove_in_neq; auto.
            rewrite nnrc_ext_to_nnrc_free_vars_same; auto.
        + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
          generalize (@nnrc_core_eval_swap_neq _ h nil v x0); simpl; intros rr2; 
            repeat rewrite rr2 by trivial.
          apply IHe2.
          * intros nin; intuition. elim H3; apply remove_in_neq; auto.
          * intuition.
      - rewrite nin_app_or in H; destruct H as [? HH]; 
          rewrite nin_app_or in HH, H0.
        rewrite nin_app_or in H0.
        rewrite IHe1, IHe2, IHe3; intuition.
      - apply not_or in H0; destruct H0 as [neq1 neq2].
        apply not_or in neq2; destruct neq2 as [neq2 neq3].
        repeat rewrite nin_app_or in neq3.
        repeat rewrite nin_app_or in H.
        rewrite IHe1 by intuition.
        repeat rewrite <- remove_in_neq in H by congruence.
        match_destr. destruct d; trivial.
        + match_destr; unfold Equivalence.equiv in *; subst.
          * generalize (@nnrc_core_eval_remove_duplicate_env _ h nil v1 d nil); simpl;
              intros re2; rewrite re2 by trivial.
            generalize (@nnrc_core_eval_remove_free_env _ h ((v1,d)::nil)); 
              simpl; intros re3. rewrite re3. intuition.
            rewrite <- nnrc_ext_to_nnrc_free_vars_same; intuition.
          * generalize (@nnrc_core_eval_swap_neq _ h nil v d); simpl;
              intros re1; repeat rewrite re1 by trivial.
            rewrite IHe2; intuition.
        + match_destr; unfold Equivalence.equiv in *; subst.
          * generalize (@nnrc_core_eval_remove_duplicate_env _ h nil v1 d nil); simpl;
              intros re2; rewrite re2 by trivial.
            generalize (@nnrc_core_eval_remove_free_env _ h ((v1,d)::nil)); 
              simpl; intros re3. rewrite re3. intuition.
            rewrite <- nnrc_ext_to_nnrc_free_vars_same; intuition.
          * generalize (@nnrc_core_eval_swap_neq _ h nil v0 d); simpl;
              intros re1; repeat rewrite re1 by trivial.
            rewrite IHe3; intuition.
      - rewrite IHe; try assumption.
        reflexivity.
    Qed.

    Definition unnest_from_nraenv vid venv a b n1 := 
      (NNRCFor (fresh_var "tmap$" (vid :: venv :: nil))
               (NNRCUnop AFlatten
                         (NNRCFor (fresh_var "tmc$" (vid :: venv :: nil))
                                  n1
                                  (NNRCFor
                                     (fresh_var "tmc$" (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil))
                                     (NNRCFor (fresh_var "tmap$" (vid :: venv :: nil))
                                              (NNRCUnop (ADot a) (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil))))
                                              (NNRCUnop (ARec b) (NNRCVar (fresh_var "tmap$" (vid :: venv :: nil)))))
                                     (NNRCBinop AConcat (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil)))
                                                (NNRCVar
                                                   (fresh_var "tmc$"
                                                              (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil)))))))
               (NNRCUnop (ARecRemove a) (NNRCVar (fresh_var "tmap$" (vid :: venv :: nil))))).

    Definition unnest_from_nraenv_core vid venv a b n1 :=
      (NNRCFor (fresh_var "tmap$" (vid :: venv :: nil))
               (NNRCUnop AFlatten
                         (NNRCFor (fresh_var "tmc$" (vid :: venv :: nil))
                                  n1
                                  (NNRCFor
                                     (fresh_var "tmc$" (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil))
                                     (NNRCFor
                                        (fresh_var "tmap$" (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil))
                                        (NNRCUnop (ADot a) (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil))))
                                        (NNRCUnop (ARec b)
                                                  (NNRCVar
                                                     (fresh_var "tmap$"
                                                                (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil)))))
                                     (NNRCBinop AConcat (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil)))
                                                (NNRCVar
                                                   (fresh_var "tmc$"
                                                              (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil)))))))
               (NNRCUnop (ARecRemove a) (NNRCVar (fresh_var "tmap$" (vid :: venv :: nil))))).

    Lemma unnest_from_nraenv_and_nraenv_core_eq vid venv env a b op1 op1' :
      nnrc_core_eval h env op1 = nnrc_core_eval h env op1' ->
      nnrc_core_eval h env (unnest_from_nraenv vid venv a b op1) =
      nnrc_core_eval h env (unnest_from_nraenv_core vid venv a b op1').
    Proof.
      intros Hind.
      Opaque fresh_var.
      simpl.
      rewrite Hind; clear Hind.
      destruct (nnrc_core_eval h env op1'); try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      destruct (equiv_dec (fresh_var "tmap$" (vid :: venv :: nil))
                          (fresh_var "tmap$" (vid :: venv :: nil))); try congruence.
      destruct (equiv_dec (fresh_var "tmc$" (vid :: venv :: nil))
                          (fresh_var "tmc$" (vid :: venv :: nil))); try congruence.
      simpl in *.
      destruct (equiv_dec
                  (fresh_var "tmc$"
                             (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil))
                  (fresh_var "tmc$"
                             (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil)));
        try congruence; simpl.
      destruct (equiv_dec
                  (fresh_var "tmap$"
                             (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil))
                  (fresh_var "tmap$"
                             (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil))); try congruence; simpl in *.
      destruct (equiv_dec (fresh_var "tmc$" (vid :: venv :: nil))
                          (fresh_var "tmc$"
                                     (fresh_var "tmc$" (vid :: venv :: nil)
                                                :: vid :: venv :: nil))). auto.
      clear e e0 e1 e2 c.
      f_equal.
      induction l; [reflexivity| ]; simpl.
      destruct a0; try reflexivity.
    Qed.
  
  End prop.

  Section core.
    Program Definition nnrc_to_nnrc_core (e:nnrc) : nnrc_core :=
      nnrc_ext_to_nnrc e.
    Next Obligation.
      apply nnrc_ext_to_nnrc_is_core.
    Defined.

  End core.
  
End NNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
