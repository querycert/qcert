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

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import Utils.
Require Import CommonSystem.
Require Import NRA.
Require Import NRAExt.
Require Import NRAEq.
Require Import NRARewrite.
Require Import TNRA.
Require Import TNRAEq.
Require Import Program.
  
Section TNRARewrite.
  Local Open Scope nra_scope.

  (* An attempt at proving some of the relational algebra's
     TYPE-DEPENDENT algebraic equivalences. *)

  (* P1 ∧ P2 == P2 ∧ P1 *)

  Context {m:basic_model}.
  
  Lemma tand_comm {τc} {τin} (op1 op2 opl opr: τin ⇝ Bool ⊣ τc) :
    (`opl = `op2 ∧ `op1) ->
    (`opr = `op2 ∧ `op1) ->
    opl ≡τ opr.
  Proof.
    intros.
    apply nra_eq_impl_tnra_eq.
    rewrite H; rewrite H0.
    rewrite and_comm.
    reflexivity.
  Qed.

  Lemma tand_comm_arrow {τc} {τin} (op1 op2:nra) :
    m ⊢ₐ τin ↦ Bool ⊣ τc ⊧ (op1 ∧ op2) ⇒ (op2 ∧ op1).
  Proof.
    intros.
    split.
    - inversion H; clear H; try eauto; subst.
      inversion H3; clear H3; subst.
      eapply type_NRABinop; try eauto.
      eapply type_OpAnd; assumption.
    - intros; rewrite and_comm; eauto.
  Qed.

  (* σ{P1}(σ{P2}(P3)) == σ{P2 ∧ P1}(P3)) *)

  Lemma tselect_and_aux (x: data) c τc τin τ (op op1 op2:nra) :
    op ▷ τin >=> (Coll τ) ⊣ τc ->
    op1 ▷ τ >=> Bool ⊣ τc ->
    op2 ▷ τ >=> Bool ⊣ τc ->
    bindings_type c τc ->
    x ▹ τin ->
    brand_relation_brands ⊢ (σ⟨ op1 ⟩(σ⟨ op2 ⟩(op))) @ₐ x  ⊣ c =
    brand_relation_brands ⊢ (σ⟨ op2 ∧ op1 ⟩(op)) @ₐ x ⊣ c.
  Proof.
    intros ? ? ? Hcenv; intros; simpl.
    assert (exists d, (brand_relation_brands ⊢ op@ₐx ⊣ c = Some d /\ (d ▹ (Coll τ))))
      by (apply (@typed_nra_yields_typed_data m τc τin); assumption).
    elim H3; clear H3; intros.
    elim H3; clear H3; intros.
    rewrite H3; clear H3; simpl.
    invcs H4.
    rtype_equalizer.
    subst.
    autorewrite with alg.
    apply lift_dcoll_inversion.
    induction dl; try reflexivity.
    simpl.
    assert (Forall (fun d : data => data_type d τ) dl)
      by (clear IHdl; rewrite Forall_forall in *; intros;
          simpl in *; intuition).
    specialize (IHdl H3); clear H3.
    rewrite <- IHdl; clear IHdl.
    rewrite Forall_forall in H6; simpl in H6.
    assert (data_type a τ)
      by intuition.
    assert (exists d, (brand_relation_brands ⊢ op2@ₐa ⊣ c = Some d /\ (d ▹ Bool)))
      by (apply (@typed_nra_yields_typed_data m τc τ); assumption).
    destruct H4 as [? [eqq dt]].
    rewrite eqq; clear eqq.
    dtype_inverter.
    unfold olift.
    destruct (       lift_filter
         (fun x' : data =>
          match brand_relation_brands ⊢ op2 @ₐ x' ⊣ c with
          | Some (dbool b0) => Some b0
          | _ => None
          end) dl).
    - destruct x1.
      + simpl.
        assert (exists d, (brand_relation_brands ⊢ op1@ₐa ⊣ c = Some d /\ (d ▹ Bool)))
          by (apply (@typed_nra_yields_typed_data m τc τ); assumption).
        destruct H4 as [? [eqq dt]].
        rewrite eqq; clear eqq.
        dtype_inverter.
        reflexivity.
      + assert (exists d, (brand_relation_brands ⊢ op1@ₐa ⊣ c = Some d /\ (d ▹ Bool)))
          by (apply (@typed_nra_yields_typed_data m τc τ); assumption).
        destruct H4 as [? [eqq dt]].
        rewrite eqq; clear eqq.
        dtype_inverter.
        destruct (lift_filter
     (fun x' : data =>
      match brand_relation_brands ⊢ op1 @ₐ x' ⊣ c with
      | Some (dbool b0) => Some b0
      | _ => None
      end) l); reflexivity.
    - destruct (brand_relation_brands ⊢ op1@ₐa ⊣ c); try reflexivity.
      destruct d; reflexivity.
  Qed.      

  Lemma tselect_and {τc} {τin τ} (op opl opr: τin ⇝ (Coll τ) ⊣ τc) (op1 op2:τ ⇝ Bool ⊣ τc) :
    (`opl = σ⟨ `op1 ⟩(σ⟨ `op2 ⟩(`op))) ->
    (`opr = σ⟨ `op2 ∧ `op1 ⟩(`op)) ->
    (opl ≡τ opr).
  Proof.
    unfold tnra_eq; intros.
    rewrite H; rewrite H0.
    rewrite (tselect_and_aux x c τc τin τ).
    reflexivity.
    apply (proj2_sig op).
    apply (proj2_sig op1).
    apply (proj2_sig op2).
    assumption.
    assumption.
  Qed.

  (* σ⟨ P1 ⟩(σ⟨ P2 ⟩(P3)) == σ⟨ P2 ⟩(σ⟨ P1 ⟩(P3)) *)

  (* This is the first rewrite done at algebra level, using nra_eq. *)
  Lemma tselect_comm_nra {τc} {τin τ} (op1 op2:τ ⇝ Bool ⊣ τc) (op opl opr: τin ⇝ (Coll τ) ⊣ τc) :
    (`opl = σ⟨ `op1 ⟩(σ⟨ `op2 ⟩(`op))) ->
    (`opr = σ⟨ `op2 ⟩(σ⟨ `op1 ⟩(`op))) ->
    opl ≡τ opr.
  Proof.
    intros.
    unfold tnra_eq; intros.
    rewrite H; rewrite H0.
    rewrite (tselect_and_aux x c τc τin τ); try assumption.
    rewrite (tselect_and_aux x c τc τin τ); try assumption.
    generalize and_comm; intros.
    assert ((σ⟨ ` op2 ∧ ` op1 ⟩( ` op)) ≡ₐ (σ⟨ ` op1 ∧ ` op2 ⟩( ` op))).
    rewrite (H1 (`op1) (`op2)).
    reflexivity.
    rewrite H2 by eauto.
    reflexivity.
    apply (proj2_sig op).
    apply (proj2_sig op2).
    apply (proj2_sig op1).
    apply (proj2_sig op).
    apply (proj2_sig op1).
    apply (proj2_sig op2).
  Qed.

  Lemma tselect_comm {τc} {τin τ} c x (op: τin ⇝ (Coll τ) ⊣ τc) (op1 op2:τ ⇝ Bool ⊣ τc) :
    bindings_type c τc ->
    x ▹ τin ->
    (brand_relation_brands ⊢ σ⟨ `op1 ⟩(σ⟨ `op2 ⟩(`op)) @ₐ x ⊣ c) = (brand_relation_brands ⊢ σ⟨ `op2 ⟩(σ⟨ `op1 ⟩(`op)) @ₐ x ⊣ c).
  Proof.
    generalize (@tselect_comm_nra τc τin); intros.
    unfold tnra_eq in H.
    specialize (H τ op1 op2 op).
    assert (σ⟨ `op1 ⟩( σ⟨ `op2 ⟩( ` op)) ▷ τin >=> Coll τ ⊣ τc).
    apply type_NRASelect.
    apply (proj2_sig op1).
    apply type_NRASelect.
    apply (proj2_sig op2).
    apply (proj2_sig op).
    assert (σ⟨ `op2 ⟩( σ⟨ `op1 ⟩( ` op)) ▷ τin >=> Coll τ ⊣ τc).
    apply type_NRASelect.
    apply (proj2_sig op2).
    apply type_NRASelect.
    apply (proj2_sig op1).
    apply (proj2_sig op).
    assert (exists opl:τin ⇝ Coll τ ⊣ τc, `opl = σ⟨ `op1 ⟩( σ⟨ `op2 ⟩(`op))).
    revert H2.
    generalize (σ⟨ `op1 ⟩( σ⟨ `op2 ⟩( `op))); intros.
    exists (exist (fun op => nra_type τc op τin (Coll τ)) n H2).
    reflexivity.
    assert (exists opr:τin ⇝ Coll τ ⊣ τc, `opr = σ⟨ `op2 ⟩( σ⟨ `op1 ⟩(`op))).
    revert H3.
    generalize (σ⟨ `op2 ⟩( σ⟨ `op1 ⟩(`op))); intros.
    exists (exist (fun op => nra_type τc op τin (Coll τ)) n H3).
    reflexivity.
    elim H4; elim H5; intros.
    rewrite <- H6.
    rewrite <- H7.
    apply (H x1 x0).
    assumption.
    assumption.
    assumption.
    assumption.
  Qed.

  (* σ⟨P⟩(P1 − P2) == σ⟨P⟩(P1) − σ⟨P⟩(P2) *)

  Definition tunbox_bool (y:{ x:data | x ▹ Bool }) : bool.
  Proof.
    elim y; clear y.
    intros.
    destruct x; try (assert False by (inversion p; contradiction) ; contradiction).
    exact b.
  Defined.

  Definition typed_nra_total_bool {τc} {τ} c (op:τ ⇝ Bool ⊣ τc):
    bindings_type c τc ->
    {x:data|(x ▹ τ)} -> bool.
  Proof.
    intros.
    apply tunbox_bool.
    apply (@typed_nra_total m τc τ Bool (`op) (proj2_sig op) c (`H0) H).
    elim H0; intros.
    exact p.
  Defined.

  Lemma typed_nra_total_bool_consistent {τc} {τ} c (op:τ ⇝ Bool ⊣ τc) (d: {x:data|(x ▹ τ)}) (Hcenv:bindings_type c τc) :
    match (brand_relation_brands ⊢ `op@ₐ`d ⊣ c) with
      | Some (dbool b) => Some b
      | _ => None
    end = Some (typed_nra_total_bool c op Hcenv d).
  Proof.
    unfold typed_nra_total_bool.
    unfold typed_nra_total.
    generalize (typed_nra_yields_typed_data c (`d) (`op) Hcenv (sig_ind (fun H : {x : data | x ▹ τ} => ` H ▹ τ)
                 (fun (x : data) (p : x ▹ τ) => p) d) 
                                            (proj2_sig op)); intros.
    destruct e; simpl.
    destruct a; simpl.
    rewrite e; clear e.
    destruct x; try (assert False by (inversion d0; contradiction) ; contradiction).
    reflexivity.
  Qed.

  Lemma typed_nra_total_bool_consistent2 {τc} {τ} c (op:τ ⇝ Bool ⊣ τc) (x:data) (pf:(x ▹ τ)) (Hcenv:bindings_type c τc) :
    match (brand_relation_brands ⊢ `op@ₐx ⊣ c) with
      | Some (dbool b) => Some b
      | _ => None
    end = Some (typed_nra_total_bool c op Hcenv (exist _ x pf)).
  Proof.
    apply (typed_nra_total_bool_consistent c op (exist _ x pf)).
  Qed.
  
  Lemma typed_lifted_predicate {τc} {τ} (op:τ ⇝ Bool ⊣ τc) c (d:data):
    bindings_type c τc ->
    data_type d τ ->
    exists b' : bool,
      (fun x' : data =>
         match brand_relation_brands ⊢ (`op)@ₐ x' ⊣ c with
           | Some (dbool b) => Some b
           | _ => None
         end) d = Some b'.
  Proof.
    intros.
    exists (typed_nra_total_bool c op H (exist _ d H0)).
    apply typed_nra_total_bool_consistent2.
  Qed.

  Lemma lift_filter_remove_one_false (l:list data) (f:data -> option bool) (a:data) :
    f a = Some false ->
    (lift_filter f (remove_one a l)) = lift_filter f l.
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    destruct (equiv_dec a a0); simpl.
    - rewrite e in *; clear e.
      rewrite H; simpl; clear H.
      destruct (lift_filter f l); reflexivity.
    - destruct (f a0); try reflexivity.
      rewrite IHl; reflexivity.
  Qed.
  
  Lemma lift_filter_remove_one {τ} (l:list data) (f:data -> option bool) (a:data) :
    Forall (fun d : data => data_type d τ) l ->
    data_type a τ ->
    (forall d : data, data_type d τ -> exists b' : bool, f d = Some b') ->
    (lift_filter f (remove_one a l)) = lift (remove_one a) (lift_filter f l).
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    destruct (equiv_dec a a0); intros; simpl.
    - rewrite e in *; clear e.
      case_eq (f a0); try reflexivity; simpl; intros.
      + inversion H; clear H. specialize (IHl H6).
        case_eq b; simpl; intros.
        * revert IHl.
          destruct (lift_filter f l); try reflexivity; intros; simpl.
          destruct (equiv_dec a0 a0); try congruence.
        * rewrite H in *; clear H.
          rewrite lift_filter_remove_one_false in IHl; try assumption.
          rewrite IHl at 1.
          destruct (lift_filter f l); reflexivity.
      + inversion H; clear H; elim (H1 a0 H0); intros; congruence.
    - destruct (f a0); try reflexivity.
      inversion H; clear H. specialize (IHl H5); clear H5 H2 H3.
      rewrite IHl.
      destruct (lift_filter f l); try reflexivity.
      destruct b; try reflexivity.
      simpl.
      destruct (equiv_dec a a0); congruence.
  Qed.

  Lemma remove_still_well_typed {τ} (l:list data) (a:data) :
    Forall (fun d : data => data_type d τ) l ->
    Forall (fun d : data => data_type d τ) (remove_one a l).
  Proof.
    intros.
    induction l.
    - simpl; apply Forall_nil.
    - simpl in *.
      inversion H; clear H.
      destruct (equiv_dec a a0).
      + assumption.
      + apply Forall_cons; auto.
  Qed.

  Lemma lift_filter_over_bminus {τ} (l1 l2 : list data) (f:data -> option bool):
    Forall (fun d : data => data_type d τ) l1 ->
    Forall (fun d : data => data_type d τ) l2 ->
    Forall (fun d : data => data_type d τ) (bminus l1 l2) ->
    (forall d : data, data_type d τ -> exists b' : bool, f d = Some b') ->
    lift dcoll (lift_filter f (bminus l1 l2)) =
    match lift dcoll (lift_filter f l2) with
      | Some d2 =>
        match lift dcoll (lift_filter f l1) with
          | Some d1 => rondcoll2 bminus d1 d2
          | None => None
        end
      | None => None
    end.
  Proof.
    intros.
    revert l2 H0 H1.
    induction l1; simpl; try reflexivity; intros.
    - destruct (lift_filter f l2); reflexivity.
    - inversion H; clear H x H3 H4.
      specialize (IHl1 H6); clear H6.
      case_eq (f a).
      + intros b eqf; simpl.
        case_eq b; intros; rewrite H in *; clear H.
        (* true *)
        * rewrite IHl1; simpl; try assumption.
          case_eq (lift_filter f l1); intros; try reflexivity; simpl.
          unfold lift; simpl.
          rewrite (lift_filter_remove_one l2 f a H0 H5 H2); simpl.
          destruct (lift_filter f l2); try reflexivity.
          rewrite (lift_filter_remove_one l2 f a H0 H5 H2); simpl.
          destruct (lift_filter f l2); try reflexivity.
          apply remove_still_well_typed; assumption.
        (* false *)
        * rewrite IHl1; simpl; try assumption.
          destruct (lift_filter f l1); try reflexivity; simpl.
          rewrite (lift_filter_remove_one_false); simpl.
          destruct (lift_filter f l2); try reflexivity.
          assumption.
          rewrite (lift_filter_remove_one_false); simpl.
          destruct (lift_filter f l2); try reflexivity.
          assumption.
          apply remove_still_well_typed; assumption.
      + intros.
        elim (H2 a); try assumption; intros.
        congruence.
  Qed.

  Lemma minus_select_distr {τc} {τin τ} (op:τ ⇝ Bool ⊣ τc) (op1 op2 opl opr: τin ⇝ (Coll τ) ⊣ τc) :
    (`opl = σ⟨`op⟩(`op1 − `op2)) ->
    (`opr = σ⟨`op⟩(`op1) − σ⟨`op⟩(`op2)) ->
    opl ≡τ opr.
  Proof.
    unfold tnra_eq.
    intros ? ? x c ? Hcenv.
    rewrite H; rewrite H0; clear H H0 opl opr; simpl.
    assert (exists d1, (brand_relation_brands ⊢ `op1@ₐx ⊣ c = Some d1 /\ (d1 ▹ (Coll τ))))
      by (apply (@typed_nra_yields_typed_data m τc τin); [assumption|assumption|apply (proj2_sig op1)]).
    assert (exists d2, (brand_relation_brands ⊢ `op2@ₐx ⊣ c = Some d2 /\ (d2 ▹ (Coll τ))))
      by (apply (@typed_nra_yields_typed_data m τc τin); [assumption|assumption|apply (proj2_sig op2)]).
    elim H; elim H0; clear H H0; intros.
    elim H; elim H0; clear H H0; intros.
    rewrite H; rewrite H1; clear H H1.
    simpl.
    invcs H0; invcs H2.
    rtype_equalizer.
    subst.
    simpl.
    assert (Forall (fun d : data => data_type d τ) (bminus dl0 dl))
      by (apply bminus_Forall; assumption).
    assert (exists f, (forall d : data,
                         data_type d τ ->
                         exists b' : bool,
                           f d = Some b') /\ f = ((fun x' : data =>
         match brand_relation_brands ⊢ (` op) @ₐ x' ⊣ c with
         | Some (dbool b) => Some b
         | _ => None
         end))).
    exists  ((fun x' : data =>
         match brand_relation_brands ⊢ (` op) @ₐ x' ⊣ c with
         | Some (dbool b) => Some b
         | _ => None
         end));
      split. intros. apply typed_lifted_predicate; try assumption. reflexivity.
    destruct H0 as [? [eqq dt]].
    revert dt.
    generalize ((fun x' : data =>
       match brand_relation_brands ⊢ (` op) @ₐ x' ⊣ c with
       | Some (dbool b) => Some b
       | _ => None
       end)); intros.
    subst.
    unfold olift2.
    eapply lift_filter_over_bminus; eauto.
  Qed.
 
End TNRARewrite.

