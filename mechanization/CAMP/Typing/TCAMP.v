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

Require Import Bool.
Require Import String.
Require Import List.
Require Import EquivDec.
Require Import Permutation.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import CAMPUtil.
Require Import CAMP.

Section TCAMP.
  (** Auxiliary lemmas *)

  Lemma rec_sort_is_sorted {A} (l:list (string*A)) :
    is_list_sorted ODT_lt_dec (domain (rec_sort l)) = true.
  Proof.
    generalize (@rec_sort_sorted). eauto.
  Qed.

  (** Auxiliary definitions and lemmas for type environments *)

  (** Typing for CAMP *)

  Context {m:basic_model}.
  Hint Resolve bindings_type_has_type.

  Reserved Notation "Γ  |= p ; a ~> b" (at level 90).

  (** Typing rules for CAMP Patterns *)

  Section t.
    Context (constants:tbindings).
  Inductive camp_type :
    tbindings -> camp -> rtype -> rtype -> Prop :=
    | PTconst Γ τ₁ {τ₂} d :
        data_type (normalize_data brand_relation_brands d) τ₂ ->
        Γ  |= pconst d ; τ₁ ~> τ₂
    | PTunop {Γ τ₁ τ₂ τ₃ u p} :
        Γ |= p ; τ₁ ~> τ₂ ->
        unary_op_type u τ₂ τ₃ ->
        Γ |= punop u p ; τ₁ ~> τ₃
    | PTbinop {Γ τ₁ τ₂₁ τ₂₂ τ₃ b p₁ p₂} :
        Γ |= p₁ ; τ₁ ~> τ₂₁ ->
        Γ |= p₂ ; τ₁ ~> τ₂₂ ->
        binary_op_type b τ₂₁ τ₂₂ τ₃ ->
        Γ |= pbinop b p₁ p₂ ; τ₁ ~> τ₃
    | PTmap {Γ τ₁ τ₂ p} :
        Γ |= p ; τ₁ ~> τ₂ ->
                 Γ |= pmap p ; Coll τ₁ ~> Coll τ₂
(*  | PTgroupBy {Γ τ₁ τ₂ p} :
        Γ |= p ; τ₁ ~> τ₂ ->
        Γ |= pgroupBy p ; Coll τ₁ ~> Coll (Coll τ₁) *)
    | PTassert {Γ τ₁ p} pf :
        Γ |= p ; τ₁ ~> Bool ->
        Γ |= passert p ; τ₁ ~> Rec Closed nil pf
    | PTorElse {Γ τ₁ τ₂ p₁ p₂} :
        Γ |= p₁ ; τ₁ ~> τ₂ ->
        Γ |= p₂ ; τ₁ ~> τ₂ ->
        Γ |= porElse p₁ p₂ ; τ₁ ~> τ₂
    | PTit Γ τ : Γ |= pit ; τ ~> τ 
    | PTletIt {Γ τ₁ τ₂ τ₃ p₁ p₂} :
        Γ |= p₁ ; τ₁ ~> τ₂ ->
        Γ |= p₂ ; τ₂ ~> τ₃ ->
        Γ |= pletIt p₁ p₂ ; τ₁ ~> τ₃
    | PTgetconstant {Γ} τ₁ s τout:
        tdot constants s = Some τout ->
        Γ |= pgetConstant s; τ₁ ~> τout
    | PTenv {Γ} τ₁ pf :
        Γ |= penv ; τ₁ ~> Rec Closed Γ pf
    | PTletEnv {Γ τ₁ τ₂ p₁ p₂} Γ' pf Γ'' :
        Γ |= p₁ ; τ₁ ~> Rec Closed Γ' pf ->
        Some Γ'' = merge_bindings Γ Γ' ->
        Γ'' |= p₂ ; τ₁ ~> τ₂ ->
        Γ |= pletEnv p₁ p₂ ; τ₁ ~> τ₂
    | PTLeft Γ τl τr :
        Γ |= pleft; (Either τl τr) ~> τl
    | PTRight Γ τl τr :
        Γ |= pright; (Either τl τr) ~> τr
       where "g |= p ; a ~> b" := (camp_type g p a b).

  End t.


  (** Auxiliary lemmas for the type soudness results *)

  Lemma  data_type_drec_nil pf :
    data_type (drec nil) (Rec Closed nil pf).
  Proof.
    apply dtrec_full.
    apply Forall2_nil.
  Qed.

  Hint Resolve data_type_drec_nil.

  Lemma concat_bindings_type {env₁ env₂ Γ₁ Γ₂} :
    bindings_type env₁ Γ₁ ->
    bindings_type env₂ Γ₂ ->
    bindings_type (env₁ ++ env₂)
                         (Γ₁ ++ Γ₂).
  Proof.
    induction env₁; inversion 1; subst; simpl; trivial.
    intros.
    constructor; intuition.
    apply Forall2_app; eauto.
  Qed.

  Lemma insertion_sort_insert_bindings_type {env Γ d r} s :
     bindings_type env Γ ->
     data_type d r ->
     bindings_type
     (insertion_sort_insert rec_field_lt_dec 
        (s, d) env)
     (insertion_sort_insert rec_field_lt_dec 
        (s, r) Γ).
   Proof.
     revert Γ. induction env; inversion 1; subst; simpl; intuition.
     - constructor; eauto.
     - destruct a; destruct y; simpl in *. subst.
       destruct (StringOrder.lt_dec s s1).
       + constructor; eauto.
       + destruct (StringOrder.lt_dec s1 s).
          * constructor; eauto.
             specialize (IHenv _ H4 H0).
             eauto.
          * eauto.
   Qed.

  Lemma rec_sort_bindings_type {env Γ} :
    bindings_type env Γ ->
    bindings_type (rec_sort env)
                         (rec_sort Γ).
  Proof.
    revert Γ.
    induction env; inversion 1; simpl; subst; trivial.
    destruct a; destruct y; simpl in *.
    intuition; subst.
    apply insertion_sort_insert_bindings_type; eauto.
  Qed.

  Lemma rec_concat_sort_bindings_type {env₁ env₂ Γ₁ Γ₂} :
    bindings_type env₁ Γ₁ ->
    bindings_type env₂ Γ₂ ->
    bindings_type (rec_concat_sort env₁ env₂)
                         (rec_concat_sort Γ₁ Γ₂).
    Proof.
      unfold rec_concat_sort.
      intros.
      apply rec_sort_bindings_type.
      apply concat_bindings_type; trivial.
    Qed.

  Lemma merge_bindings_type {env₁ env₂ env₃ Γ₁ Γ₂ Γ₃} :
        bindings_type env₁ Γ₁ ->
        bindings_type env₂ Γ₂ ->
        Some env₃ = merge_bindings env₁ env₂ ->
        Some Γ₃ = merge_bindings Γ₁ Γ₂ ->
        bindings_type env₃ Γ₃.
  Proof.
    unfold merge_bindings.
    destruct (Compat.compatible env₁ env₂); simpl; try discriminate.
    destruct (Compat.compatible Γ₁ Γ₂); simpl; try discriminate.
    inversion 3; inversion 1; subst.
    apply rec_concat_sort_bindings_type; trivial.
  Qed.

  (** Main type soudness lemma *)

  Notation "[ c & g ] |= p ; a ~> b" := (camp_type c g p a b) (at level 90).

  Theorem typed_camp_success_or_recoverable {c} {τc}
          {Γ τin τout} {p:camp} {env} {d} :
    bindings_type c τc ->
     bindings_type env Γ ->
     ([τc & Γ] |= p ; τin ~> τout) ->
     (data_type d τin) ->
        (exists x, camp_eval brand_relation_brands c p env d = Success x /\  (data_type x τout)) 
        \/ (camp_eval brand_relation_brands c p env d = RecoverableError).
  Proof.
    simpl.
    intros tconst tenv tcamp tdat.
    revert d env Γ τin τout tenv tcamp tdat.
    induction p; simpl; intros din env Γ τin τout tenv tcamp tdat;
    inversion tcamp; subst.
    (* pconst *)
    - eauto. 
    (* punop *)
    - destruct (IHp _ _ _ _ _ tenv H2 tdat) as [[dout[camp_evaleq tx]]|camp_evaleq];
        rewrite camp_evaleq; simpl; [|eauto].
        destruct (typed_unary_op_yields_typed_data _ _ tx H5) as [?[??]].
        rewrite H; simpl. eauto.
    (* pbinop *)
    - destruct (IHp1 _ _ _ _ _ tenv H3 tdat) as [[dout1[camp_evaleq1 tx1]]|camp_evaleq1];
        rewrite camp_evaleq1; simpl; [|eauto].
      destruct (IHp2 _ _ _ _ _ tenv H6 tdat) as [[dout2[camp_evaleq2 tx2]]|camp_evaleq2];
        rewrite camp_evaleq2; simpl; [|eauto].
      destruct (typed_binary_op_yields_typed_data _ _ _ tx1 tx2 H7) as [?[??]].
      rewrite H; simpl. eauto.
    (* pmap *)
    - inversion tdat; subst.
      rtype_equalizer. subst.
      induction dl; simpl.
      + left; econstructor; split; eauto. constructor; eauto.
      + inversion H2; subst.
         specialize (IHdl (dtcoll _ _ H4) H4).
         destruct (IHp _ _ _ _ _ tenv H1 H3) as [[dout[camp_evaleq tx]]|camp_evaleq];
           rewrite camp_evaleq; simpl; [|eauto].
        destruct  (gather_successes (map (camp_eval brand_relation_brands _ p env) dl)); simpl in *; intuition.
        * destruct H as [?[??]].
          inversion H; subst. left; econstructor; split; eauto.
          inversion H0; subst; rtype_equalizer.
          subst. constructor. constructor; eauto.
        * discriminate.
    (* pgroupBy *)
    (* 
    - inversion tdat; subst.
      rtype_equalizer. subst.
      induction dl; simpl.
      + left; econstructor; split; eauto. econstructor; eauto.
      + inversion H2; subst.
        specialize (IHdl (dtcoll _ _ H4) H4).
        destruct (IHp _ _ _ _ _ tenv H1 H3) as [[dout[camp_evaleq tx]]|[s camp_evaleq]].
        addddmit.
        addddmit. *)
    (* passert *)
    - destruct (IHp _ _ _ _ _ tenv H1 tdat) as [[dout[camp_evaleq tx]]|camp_evaleq];
        rewrite camp_evaleq; simpl; [|eauto].
      inversion tx; subst.
      destruct b; simpl; eauto.
    (* porElse *)
    - destruct (IHp1 _ _ _ _ _ tenv H2 tdat) as [[dout1[camp_evaleq1 tx1]]|camp_evaleq1];
        rewrite camp_evaleq1; simpl; [|eauto].
      destruct (IHp2 _ _ _ _ _ tenv H5 tdat) as [[dout2[camp_evaleq2 tx2]]|camp_evaleq2];
        try rewrite camp_evaleq2; simpl; [|eauto].
      eauto.
    (* pit *)
    - eauto.
    (* pletIt *)
    - destruct (IHp1 _ _ _ _ _ tenv H2 tdat) as [[dout1[camp_evaleq1 tx1]]|camp_evaleq1];
        rewrite camp_evaleq1; simpl; [|eauto].
      destruct (IHp2 _ _ _ _ _ tenv H5 tx1) as [[dout2[camp_evaleq2 tx2]]|camp_evaleq2];
        rewrite camp_evaleq2; simpl; [|eauto].
      eauto.
    (* pgetConstant *)
    - left.
      unfold tdot in *.
      unfold edot in *.
      unfold op2tpr.
      destruct (Forall2_lookupr_some tconst H1) as [? [eqq1 eqq2]].
      rewrite eqq1.
      eauto.
    (* penv *)
    - eauto.
    (* pletEnv *)
    - destruct (IHp1 _ _ _ _ _ tenv H1 tdat) as [[dout1[camp_evaleq1 tx1]]|camp_evaleq1];
        rewrite camp_evaleq1; simpl; [|eauto].
        inversion tx1; subst; rtype_equalizer.
        subst.
        case_eq (merge_bindings env dl); [|eauto]. intros.
        cut (bindings_type l Γ''); intros.
        destruct (IHp2 _ _ _ _ _ H0 H6 tdat) as [[dout2[camp_evaleq2 tx2]]|camp_evaleq2];
        rewrite camp_evaleq2; simpl; [|eauto].
        eauto.
        specialize (H5 eq_refl). rewrite <- H5 in *; clear H5 rl.
        apply (@merge_bindings_type env dl l Γ Γ' Γ'' tenv); auto.
    - inversion tdat; rtype_equalizer.
      + subst; eauto.
      + subst; eauto.
    - inversion tdat; rtype_equalizer.
      + subst; eauto.
      + subst; eauto.
  Qed.

  Hint Constructors camp_type.

  (** Additional lemma used in the correctness for typed translation from NNRC to CAMP *)
  Lemma camp_type_tenv_rec {τc Γ p τ₁ τ₂} :
    NoDup (domain Γ) ->
    [τc & Γ] |= p; τ₁ ~> τ₂ ->
    [τc & rec_sort Γ] |= p; τ₁ ~> τ₂.
  Proof.
    simpl.
    intros nod tdev.
    dependent induction tdev; simpl; eauto.
    - rewrite <- (Rec_rewrite Closed (rec_sort_is_sorted Γ) pf (@sort_sorted_is_id string ODT_string _ Γ pf)).
      eauto.
    - econstructor; eauto.
      unfold merge_bindings in *.      
      case_eq (Compat.compatible Γ Γ'); 
        intros comp; rewrite comp in *; try discriminate.
      inversion H; subst.
      assert (perm:Permutation Γ (rec_sort Γ)) 
        by (apply rec_sort_perm; auto).
      apply (compatible_perm_proper_l _ _ _ perm) in comp; eauto 2.
      rewrite comp.
      f_equal.
      unfold rec_concat_sort.
      rewrite rec_sort_rec_sort_app1; trivial.
  Qed.

  Lemma camp_type_const_sort_f {τc Γ p τ₁ τ₂} :
    [rec_sort τc & Γ] |= p; τ₁ ~> τ₂ ->
    [τc & Γ] |= p; τ₁ ~> τ₂.
  Proof.
    revert τc Γ τ₁ τ₂.
    induction p; simpl; inversion 1; rtype_equalizer; subst; eauto.
    unfold tdot, edot in *.
    rewrite (assoc_lookupr_drec_sort (odt:=ODT_string)) in H2.
    econstructor. apply H2.
  Qed.

  Lemma camp_type_const_sort_b {τc Γ p τ₁ τ₂} :
    [τc & Γ] |= p; τ₁ ~> τ₂ ->
    [rec_sort τc & Γ] |= p; τ₁ ~> τ₂.
  Proof.
    revert τc Γ τ₁ τ₂.
    induction p; simpl; inversion 1; rtype_equalizer; subst; eauto.
    econstructor.
    unfold tdot, edot.
    rewrite (assoc_lookupr_drec_sort (odt:=ODT_string)).
    apply H2.
  Qed.

  Lemma camp_type_const_sort {τc Γ p τ₁ τ₂} :
    [rec_sort τc & Γ] |= p; τ₁ ~> τ₂ <->
    [τc & Γ] |= p; τ₁ ~> τ₂.
  Proof.
    split; intros.
    - apply camp_type_const_sort_f; trivial.
    - apply camp_type_const_sort_b; trivial.
  Qed.

End TCAMP.

Notation "[ c & g ] |= p ; a ~> b" := (camp_type c g p a b) (at level 90) : camp_scope.

