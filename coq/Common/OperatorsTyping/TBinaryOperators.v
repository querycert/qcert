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
Require Import ZArith.
Require Import Compare_dec.
Require Import Program.
Require Import RelationClasses.
Require Import EquivDec.
Require Import Utils.
Require Import Types.
Require Import CommonData.
Require Import ForeignData.
Require Import ForeignOperators.
Require Import ForeignDataTyping.
Require Import Operators.
Require Import TUtil.
Require Import TData.
Require Import ForeignOperatorsTyping.

Section TBinaryOperators.
  (** Typing rules for binary operators *)

  Context {fdata:foreign_data}.
  Context {fbop:foreign_binary_op}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {h:brand_model}.
  Context {fboptyping:foreign_binary_op_typing}.

  Section typ.
    Inductive binary_op_type: binary_op -> rtype -> rtype -> rtype -> Prop :=
    | type_OpEqual {τ} :
        binary_op_type OpEqual τ τ Bool
    | type_OpRecConcat {τ₁ τ₂ τ₃} pf1 pf2 pf3 :
        rec_concat_sort τ₁ τ₂ = τ₃ ->
        binary_op_type OpRecConcat
                       (Rec Closed τ₁ pf1) (Rec Closed τ₂ pf2)
                       (Rec Closed τ₃ pf3)
    | type_OpRecMerge_closed {τ₁ τ₂ τ₃} pf1 pf2 pf3 : 
        merge_bindings τ₁ τ₂ = Some τ₃ ->
        binary_op_type OpRecMerge
                       (Rec Closed τ₁ pf1) (Rec Closed τ₂ pf2)
                       (Coll (Rec Closed τ₃ pf3))
    | type_OpRecMerge_open {τ₁ τ₂ τ₃} pf1 pf2 pf3 : 
        merge_bindings τ₁ τ₂ = Some τ₃ ->
        binary_op_type OpRecMerge
                       (Rec Open τ₁ pf1) (Rec Open τ₂ pf2)
                       (Coll (Rec Open τ₃ pf3))
    | type_OpAnd :
        binary_op_type OpAnd Bool Bool Bool
    | type_OpOr :
        binary_op_type OpOr Bool Bool Bool
    | type_OpLt :
        binary_op_type OpLt Nat Nat Bool  (* XXX Should it be generalized? *)
    | type_OpLe :
        binary_op_type OpLe Nat Nat Bool  (* XXX Should it be generalized? *)
    | type_OpBagUnion {τ} :
        binary_op_type OpBagUnion (Coll τ) (Coll τ) (Coll τ)
    | type_OpBagDiff {τ} :
        binary_op_type OpBagDiff (Coll τ) (Coll τ) (Coll τ)
    | type_OpBagMin {τ} :
        binary_op_type OpBagMin (Coll τ) (Coll τ) (Coll τ)
    | type_OpBagMax {τ} :
        binary_op_type OpBagMax (Coll τ) (Coll τ) (Coll τ)
    | type_OpBagNth {τ} :
        binary_op_type OpBagNth (Coll τ) Nat (Option τ)
    | type_OpContains {τ} :
        binary_op_type OpContains τ (Coll τ) Bool
    | type_OpStringConcat :
        binary_op_type OpStringConcat String String String
    | type_OpStringJoin :
        binary_op_type OpStringJoin String (Coll String) String
    | type_OpNatBinary (b:nat_arith_binary_op) :
        binary_op_type (OpNatBinary b) Nat Nat Nat
    | type_OpFloatBinary (b:float_arith_binary_op) :
        binary_op_type (OpFloatBinary b) Float Float Float
    | type_OpFloatCompare (b:float_compare_binary_op) :
        binary_op_type (OpFloatCompare b) Float Float Bool
    | type_OpForeignBinary {fb τin₁ τin₂ τout} :
        foreign_binary_op_typing_has_type fb τin₁ τin₂ τout ->
        binary_op_type (OpForeignBinary fb) τin₁ τin₂ τout.

  End typ.

  Tactic Notation "binary_op_type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "type_OpEqual"%string
    | Case_aux c "type_OpRecConcat"%string
    | Case_aux c "type_OpRecMerge_closed"%string
    | Case_aux c "type_OpRecMerge_open"%string
    | Case_aux c "type_OpAnd"%string
    | Case_aux c "type_OpOr"%string
    | Case_aux c "type_OpLt"%string
    | Case_aux c "type_OpLe"%string
    | Case_aux c "type_OpBagUnion"%string
    | Case_aux c "type_OpBagDiff"%string
    | Case_aux c "type_OpBagMin"%string
    | Case_aux c "type_OpBagMax"%string
    | Case_aux c "type_OpBagNth"%string
    | Case_aux c "type_OpContains"%string
    | Case_aux c "type_OpStringConcat"%string
    | Case_aux c "type_OpStringJoin"%string
    | Case_aux c "type_OpNatBinary"%string
    | Case_aux c "type_OpFloatBinary"%string
    | Case_aux c "type_OpFloatCompare"%string
    | Case_aux c "type_OpForeignBinary"%string].

  (** Type soundness lemmas for individual operators *)

  Lemma forall_typed_bunion {τ} d1 d2:
    Forall (fun d : data => data_type d τ) d1 ->
    Forall (fun d : data => data_type d τ) d2 ->
    Forall (fun d : data => data_type d τ) (bunion d1 d2).
  Proof.
    intros; rewrite Forall_forall in *.
    induction d1.
    simpl in *; intros.
    apply H0; assumption.
    simpl in *; intros.
    elim H1; intros; clear H1.
    apply (H x).
    left; assumption.
    assert (forall x : data, In x d1 -> data_type x τ).
    intros.
    apply (H x0).
    right; assumption.
    apply IHd1; assumption.
  Qed.

  Lemma bminus_in_remove (x a:data) (d1 d2:list data) :
    In x (bminus d1 (remove_one a d2)) -> In x (bminus d1 d2).
  Proof.
    revert d2.
    induction d1; simpl; intros.
    - induction d2; simpl in *.
      assumption.
      revert H.
      elim (EquivDec.equiv_dec a a0); unfold EquivDec.equiv_dec; intros.
      rewrite <- a1.
      right; assumption.
      simpl in H.
      elim H; intros; clear H.
      left; assumption.
      right; apply (IHd2 H0).
    - specialize (IHd1 (remove_one a0 d2)).
      apply IHd1.
      rewrite remove_one_comm; assumption.
  Qed.
    
  Lemma forall_typed_bminus {τ} d1 d2:
    Forall (fun d : data => data_type d τ) d1 ->
    Forall (fun d : data => data_type d τ) d2 ->
    Forall (fun d : data => data_type d τ) (bminus d1 d2).
  Proof.
    intros; rewrite Forall_forall in *.
    induction d1.
    simpl in *; intros.
    apply H0; assumption.
    simpl in *; intros.
    assert (forall x : data, In x d1 -> data_type x τ).
    intros.
    apply (H x0).
    right; assumption.
    assert (In x (bminus d1 d2))
      by (apply bminus_in_remove with (a:=a); assumption).
    apply IHd1; assumption.
  Qed.

  Lemma forall_typed_bmin {τ} d1 d2:
    Forall (fun d : data => data_type d τ) d1 ->
    Forall (fun d : data => data_type d τ) d2 ->
    Forall (fun d : data => data_type d τ) (bmin d1 d2).
  Proof.
    intros.
    unfold bmin.
    assert (Forall (fun d : data => data_type d τ) (bminus d2 d1)).
    apply forall_typed_bminus; assumption.
    apply forall_typed_bminus; assumption.
  Qed.

  Lemma forall_typed_bmax {τ} d1 d2:
    Forall (fun d : data => data_type d τ) d1 ->
    Forall (fun d : data => data_type d τ) d2 ->
    Forall (fun d : data => data_type d τ) (bmax d1 d2).
  Proof.
    intros.
    unfold bmax.
    assert (Forall (fun d : data => data_type d τ) (bminus d1 d2)).
    apply forall_typed_bminus; assumption.
    apply forall_typed_bunion; assumption.
  Qed.

  Lemma rec_concat_with_drec_concat_well_typed  dl dl0 τ₁ τ₂:
    is_list_sorted ODT_lt_dec (domain τ₁) = true ->
    is_list_sorted ODT_lt_dec (domain τ₂) = true ->
      is_list_sorted ODT_lt_dec (domain (rec_concat_sort τ₁ τ₂)) = true ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) dl τ₁ ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) dl0 τ₂ ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) (rec_sort (dl ++ dl0))
        (rec_concat_sort τ₁ τ₂).
  Proof.
    intros pf1 pf2 pf3 H H0.
    assert (domain dl = domain τ₁)
      by (apply (sorted_forall_same_domain); assumption).
    assert (domain dl0 = domain τ₂)
      by (apply (sorted_forall_same_domain); assumption).
    assert (rec_sort dl = dl)
      by (apply sort_sorted_is_id; rewrite H1; assumption).
    assert (rec_sort dl0 = dl0)
      by (apply sort_sorted_is_id; rewrite H2; assumption).
    assert (rec_sort τ₂ = τ₂)
      by (apply sort_sorted_is_id; assumption).
    assert (rec_sort τ₁ = τ₁)
      by (apply sort_sorted_is_id; assumption).
    unfold rec_concat_sort.
    induction H; simpl in *.
    rewrite H4; rewrite H5.
    assumption.
    assert (is_list_sorted ODT_lt_dec (domain l') = true).
    revert pf1.
    destruct l'.
    reflexivity.
    simpl.
    destruct (StringOrder.lt_dec (fst y) (fst p)); congruence.
    assert (is_list_sorted ODT_lt_dec
                (domain (rec_sort (l' ++ τ₂))) = true)
      by (apply (@rec_sort_sorted string ODT_string) with (l1 := l' ++ τ₂); reflexivity).
    specialize (IHForall2 H8 H9).
    inversion H1.
    specialize (IHForall2 H12).
    assert (is_list_sorted ODT_lt_dec (domain l') = true).
    revert pf1.
    destruct l'; try reflexivity; simpl.
    destruct (StringOrder.lt_dec (fst y) (fst p)); congruence.
    assert (is_list_sorted ODT_lt_dec (domain l') = true)
      by (apply (@rec_sorted_skip_first string ODT_string _ l' y); assumption).
    assert (rec_sort l' = l')
      by (apply rec_sorted_id; assumption).
    assert (is_list_sorted ODT_lt_dec (domain l) = true)
      by (apply (sorted_forall_sorted l l'); assumption).
    assert (rec_sort l = l)
      by (apply rec_sorted_id; assumption).
    specialize (IHForall2 H16 H14).
    clear H4 H5 H12 H10 H13 H14 H15 H16.
    elim H; intros; clear H H4.
    clear pf1 pf2.
    assert (is_list_sorted
              ODT_lt_dec
              (domain
                 (insertion_sort_insert rec_field_lt_dec x (rec_sort (l ++ dl0)))) =
            true).
    apply (insert_and_foralls_mean_same_sort l dl0 l' τ₂ x y); assumption.
    apply Forall2_cons_sorted; assumption.
  Qed.

  Lemma concat_well_typed {τ₁ τ₂ τ₃} d1 d2 pf1 pf2 pf3:
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    data_type d1 (Rec Closed τ₁ pf1) ->
    data_type d2 (Rec Closed τ₂ pf2) ->
    exists dl dl0 d3,
      d1 = drec dl /\
      d2 = drec dl0 /\
      ((rec_sort (dl ++ dl0)) = d3) /\
      data_type (drec d3) (Rec Closed τ₃ pf3).
  Proof.
    intros.
    destruct (data_type_Rec_inv H0); subst.
    destruct (data_type_Rec_inv H1); subst.
    apply dtrec_closed_inv in H0.
    apply dtrec_closed_inv in H1.
    do 3 eexists; do 3 (split; try reflexivity).
    apply dtrec_full.
    apply rec_concat_with_drec_concat_well_typed; assumption.
  Qed. 

  (** Main type-soundness lemma for binary operators *)

  Existing Instance rec_field_lt_strict.

  (* key idea: any overlap must have the same data.
      so we can give it the same type.  and we need only do that 
      for things not in the subset, since they are already compatible.
   *)
(* s is what we care about from l.
    l2 is what we take from if we don't care 
*)
  Definition mapTopNotSub s l2 (l:list (string*rtype)) :=
    map (fun xy => (fst xy, if in_dec string_dec (fst xy) s
                            then snd xy
                            else match lookup string_dec l2 (fst xy) with
                                   | Some y' => y'
                                   | None => Top
                                 end
                   )) l.

  Lemma mapTopNotSub_domain s l2 l :
    domain (mapTopNotSub s l2 l) = domain l.
  Proof.
    induction l; simpl; congruence.
  Qed.
  
  Lemma mapTopNotSub_in {s l x} l2:
    In (fst x) s -> In x l -> In x (mapTopNotSub s l2 l).
  Proof.
    induction l; simpl; intuition.
    subst. destruct x; simpl in *.
    match_destr; intuition.
  Qed.

  Lemma mapTopNotSub_in2 {s l x y} l2:
      ~ In x s -> In x (domain l) -> lookup string_dec l2 x = Some y -> In (x,y) (mapTopNotSub s l2 l).
  Proof.
    induction l; simpl; intuition.
    subst.
    match_destr; intuition.
    rewrite H1. intuition.
  Qed.

    Lemma in_mapTopNotSub {s l x} l2:
    In (fst x) s -> In x (mapTopNotSub s l2 l) -> In x l.
  Proof.
    induction l; simpl; intuition.
      destruct a; subst. simpl in *. 
      match_destr; intuition.
  Qed.
    
  Lemma mapTopNotSub_in_sublist {s l x} l2 :
    sublist s l ->
      In x s -> In x (mapTopNotSub (domain s) l2 l).
  Proof.
    intros.
    eapply mapTopNotSub_in; eauto.
    - destruct x. apply in_dom in H0; simpl; trivial.
    - eapply sublist_In; eauto.
  Qed.
    
  Lemma mapTopNotSub_sublist {s l s'} l2:
    sublist s l ->
    sublist s s' ->
    sublist s (mapTopNotSub (domain s') l2 l).
  Proof.
    revert s s'.
    induction l; inversion 1; subst.
    - constructor.
    - simpl; intros.
      destruct a; simpl in *.
      match_destr.
      + apply sublist_cons. apply IHl; trivial.
           eapply sublist_skip_l; eauto.
      + elim n. 
        eapply in_dom.
        eapply (sublist_In H0).
        simpl. left; reflexivity.
    - simpl; intros.
      destruct a; simpl in *.
      apply sublist_skip; auto.
  Qed.

  Lemma mapTopNotSub_sublist_same {s l} l2:
    sublist s l ->
    sublist s (mapTopNotSub (domain s) l2 l).
  Proof.
    intros. apply mapTopNotSub_sublist; trivial.
    reflexivity.
  Qed.
  

  Lemma mapTopNotSub_in_inv {s l2 l x} :
    In x (mapTopNotSub s l2 l) ->
    (In (fst x) s /\ In x l) \/
    (~ In (fst x) s /\
     (In x l2 \/
      (~ In (fst x) (domain l2) /\ snd x = Top))).
  Proof.
    induction l; simpl; intuition.
    destruct x. destruct a; simpl in *.
    inversion H0; simpl in *; subst.
    match_destr; intuition. 
    right; split; trivial.
    
    match_case; intros.
    - left. eapply lookup_in; eauto.
    -  apply lookup_none_nin in H.  intuition. 
  Qed.

  Lemma mapTopNotSub_compatible {t1 t2} rl1 rl2 :
    NoDup (domain rl1) -> NoDup (domain rl2) ->
    sublist t1 rl1 ->
    sublist t2 rl2 ->
  compatible t1 t2 = true ->
    compatible (mapTopNotSub (domain t1) t2 rl1)
               (mapTopNotSub (domain t2) t1 rl2) = true.
  Proof.
    unfold compatible, Compat.compatible.
    repeat rewrite forallb_forall.
    unfold compatible_with.
    intros.
    match_case; intros.
    match_destr. elim c; clear c; red.
    destruct x; simpl in *.
    apply assoc_lookupr_in in H5.
    generalize (mapTopNotSub_in_inv H4); simpl.
    intuition.
    - destruct (in_domain_in H6) as [r' inn].
       specialize (H3 _ inn).
       simpl in *.
       apply in_mapTopNotSub in H4; simpl; trivial.
       apply (sublist_In H1) in inn.
       generalize (nodup_in_eq H inn H4); intros; subst.
       match_case_in H3; intros.
       + rewrite H7 in H3.
         match_destr_in H3. unfold equiv in *; subst.
         apply assoc_lookupr_in in H7.
         apply in_mapTopNotSub in H5; simpl; trivial.
         * apply (sublist_In H2) in H7.
           generalize (nodup_in_eq H0 H7 H5); trivial.
         * eapply in_dom; eauto.
       + clear H3.
          apply mapTopNotSub_in_inv in H5.
          simpl in *.
          apply assoc_lookupr_none_nin in H7.
          intuition.
          generalize (sublist_In H1 _ H3); intros ? .
          eapply (nodup_in_eq H H8 H9); eauto.
    - apply mapTopNotSub_in_inv in H5. simpl in *.
      intuition.
      + generalize (sublist_In H2 _ H7); intros.
         eapply (nodup_in_eq H0); eauto.
      + apply in_dom in H8; intuition.
      + apply in_dom in H7. intuition.
    - apply mapTopNotSub_in_inv in H5. simpl in *.
      intuition.
      + apply in_dom in H7. intuition.
      + congruence.
  Qed. 

  Lemma Forall2_compat_mapTopNotSub {x x0 rl rl0 t2} t1:
    is_list_sorted ODT_lt_dec (domain rl) = true ->
    is_list_sorted ODT_lt_dec (domain rl0) = true ->
    sublist t2 rl0 ->
    Forall2  (fun (d : string * data) (r : string * rtype) =>
                fst d = fst r /\ snd d ▹ snd r) x rl ->
        Forall2  (fun (d : string * data) (r : string * rtype) =>
                fst d = fst r /\ snd d ▹ snd r) x0 rl0 ->
        compatible x x0 = true ->
        Forall2
          (fun (d : string * data) (r : string * rtype) =>
             fst d = fst r /\ snd d ▹ snd r) x (mapTopNotSub t1 t2 rl).
  Proof.
    revert x x0 rl0 t1 t2.
    induction rl; intros; inversion H2; subst; auto 1.
    clear H2.
    destruct x1; destruct a; simpl in H8; destruct H8; subst.
    simpl.
    constructor.
    - simpl; split; trivial.
      match_destr.
      match_case; intros; eauto 2.
      apply lookup_in in H2.
      destruct (Forall2_In_r H3 (sublist_In H1 _ H2)) as [[??] [?[??]]].
      simpl in *; subst.
      rewrite andb_true_iff in H4. destruct H4 as [cw _ ].
      unfold compatible_with in cw.
      match_case_in cw; intros.
      + rewrite H4 in cw. match_destr_in cw.
         unfold equiv in *; subst.
         apply assoc_lookupr_in in H4.
         assert (nd:NoDup (domain x0)).
         (rewrite (sorted_forall_same_domain H3); eauto 2).
         generalize (nodup_in_eq nd H4 H6); intros; subst.
         trivial.
      + apply assoc_lookupr_none_nin in H4. apply in_dom in H6.
         intuition.
    - eapply IHrl; eauto 3.
      + eapply is_list_sorted_cons_inv; eauto.
      + unfold compatible, Compat.compatible in *. rewrite forallb_forall in *.
         intros. apply H4; simpl; intuition.
  Qed.

  Lemma Forall2_compat_app_strengthen {x x0 rl rl0 t1 t2}:
    is_list_sorted ODT_lt_dec (domain rl) = true ->
    is_list_sorted ODT_lt_dec (domain rl0) = true ->
    sublist t1 rl ->
    sublist t2 rl0 ->
    compatible t1 t2 = true ->
    Forall2  (fun (d : string * data) (r : string * rtype) =>
                fst d = fst r /\ snd d ▹ snd r) x rl ->
        Forall2  (fun (d : string * data) (r : string * rtype) =>
                fst d = fst r /\ snd d ▹ snd r) x0 rl0 ->
        compatible x x0 = true -> 
        exists rl' rl0',
          compatible rl' rl0' = true /\
          sublist t1 rl' /\
          sublist t2 rl0' /\
          Forall2  (fun (d : string * data) (r : string * rtype) =>
                      fst d = fst r /\ snd d ▹ snd r) x rl' /\
          Forall2  (fun (d : string * data) (r : string * rtype) =>
                      fst d = fst r /\ snd d ▹ snd r) x0 rl0'.
  Proof.
    intros.
    exists (mapTopNotSub (domain t1) t2 rl).  
    exists (mapTopNotSub (domain t2) t1 rl0).
    intuition.
    - apply mapTopNotSub_compatible; eauto.
    - apply mapTopNotSub_sublist_same; trivial.
    - apply mapTopNotSub_sublist_same; trivial.
    - eapply Forall2_compat_mapTopNotSub; eauto.
    - eapply Forall2_compat_mapTopNotSub;
        try eapply H4; eauto.
      + unfold compatible in *. apply compatible_true_sym in H6; trivial.
         rewrite (sorted_forall_same_domain H5); eauto.
  Qed.                 

  Lemma sorted_sublists_sorted_concat (τ₁ τ₂ rl rl0:list (string*rtype)):
    is_list_sorted ODT_lt_dec (domain τ₁) = true ->
    is_list_sorted ODT_lt_dec (domain τ₂) = true ->
    is_list_sorted ODT_lt_dec (domain rl) = true ->
    is_list_sorted ODT_lt_dec (domain rl0) = true ->
    compatible rl rl0 = true ->
    sublist τ₁ rl ->
    sublist τ₂ rl0 ->
    sublist (rec_sort (τ₁ ++ τ₂)) (rec_sort (rl ++ rl0)).
  Proof.
    intros.
    eapply Sorted_incl_sublist; eauto; try apply insertion_sort_Sorted.
    intros.
    generalize (in_insertion_sort H6); intros inn.
    apply insertion_sort_in_strong.
    - apply compatible_asymmetric_over.
      apply compatible_app_compatible; trivial.
    - clear H6. revert x inn. apply sublist_In.
      apply sublist_app; trivial.
  Qed.

  Lemma typed_binary_op_yields_typed_data {τ₁ τ₂ τout} (d1 d2:data) (b:binary_op) :
    (d1 ▹ τ₁) -> (d2 ▹ τ₂) -> (binary_op_type  b τ₁ τ₂ τout) ->
    (exists x, binary_op_eval brand_relation_brands b d1 d2 = Some x /\ x ▹ τout).
  Proof.
    Hint Constructors data_type.
    intros.
    binary_op_type_cases (dependent induction H1) Case; simpl.
    - Case "type_OpEqual"%string.
      unfold unbdata.
      destruct (if data_eq_dec d1 d2 then true else false).
      exists (dbool true); split; [reflexivity|apply dtbool].
      exists (dbool false); split; [reflexivity|apply dtbool].
    - Case "type_OpRecConcat"%string.
      assert(exists dl dl0 d3,
               d1 = drec dl /\
               d2 = drec dl0 /\
               ((rec_sort (dl ++ dl0)) = d3) /\
               data_type (drec d3) (Rec Closed τ₃ pf3)).
      apply (concat_well_typed d1 d2 pf1 pf2 pf3); assumption.
      elim H2; clear H2; intros.
      elim H2; clear H2; intros.
      elim H2; clear H2; intros.
      elim H2; clear H2; intros.
      elim H3; clear H3; intros.
      elim H4; clear H4; intros.
      rewrite H2; rewrite H3; clear H0 H1.
      exists (drec x1).
      rewrite <- H4 in *.
      split; [reflexivity|assumption].
    - Case "type_OpRecMerge_closed"%string.
      destruct (data_type_Rec_inv H); subst.
      destruct (data_type_Rec_inv H0); subst.
      apply dtrec_closed_inv in H.
      apply dtrec_closed_inv in H0.
      unfold merge_bindings in *.
      destruct (Compat.compatible τ₁ τ₂); try discriminate.
      inversion H1; clear H1; subst.
      destruct (Compat.compatible x x0);
        (eexists; split; [reflexivity|]); eauto.
      econstructor. econstructor; eauto.
      apply dtrec_full.
      unfold rec_concat_sort.
      apply rec_concat_with_drec_concat_well_typed; auto.
    - Case "type_OpRecMerge_open"%string.
      destruct (data_type_Rec_inv H); subst.
      destruct (data_type_Rec_inv H0); subst.
      inversion H; clear H; subst; clear H6.
      inversion H0; clear H0; subst; clear H8.
      rtype_equalizer. subst.
      case_eq (merge_bindings x x0); intros.
      + unfold merge_bindings in *.
        case_eq (Compat.compatible τ₁ τ₂); intros eqq; rewrite eqq in *; try discriminate.
        inversion H1; clear H1; subst.
        case_eq (Compat.compatible x x0); intros eqq2; rewrite eqq2 in *;
          (eexists; split; [reflexivity | ]); eauto.
        * econstructor. econstructor; eauto.
          inversion H; clear H; subst.
          assert (is_list_sorted ODT_lt_dec (domain (rec_sort (rl ++ rl0))) = true)
            by (apply (@rec_sort_sorted string ODT_string _ (rl++rl0)); reflexivity).
          destruct (Forall2_compat_app_strengthen pf' pf'0 H5 H6 eqq H7 H9 eqq2) as [rl'[rl0' [?[?[?[??]]]]]].
          assert(pfrl':is_list_sorted ODT_lt_dec (domain rl') = true).
          rewrite <- (sorted_forall_same_domain H3).
          rewrite (sorted_forall_same_domain H7); trivial.
          assert(pfrl0':is_list_sorted ODT_lt_dec (domain rl0') = true).
          rewrite <- (sorted_forall_same_domain H4).
          rewrite (sorted_forall_same_domain H9); trivial.
          (* need a lemma about strengthening here *)
          apply (@dtrec_open _ _ _ _ (rec_sort (x ++ x0)) (rec_sort (rl' ++ rl0'))); try assumption.
          eauto.
          apply sorted_sublists_sorted_concat; trivial.
          apply rec_concat_with_drec_concat_well_typed; try assumption.
          unfold rec_concat_sort.
          eauto.
        * congruence.
      + exists (dcoll []); split; try reflexivity;
        apply dtcoll; apply Forall_nil.
    - Case "type_OpAnd"%string.
      dependent induction H; dependent induction H0; simpl.
      exists (dbool (b && b0)).
      split; [reflexivity|apply dtbool].
    - Case "type_OpOr"%string.
      dependent induction H; dependent induction H0; simpl.
      exists (dbool (b || b0)).
      split; [reflexivity|apply dtbool].
    - Case "type_OpLt"%string.
      dependent induction H; dependent induction H0; simpl.
      exists (dbool (if Z_lt_dec n n0 then true else false)).
      split; [reflexivity|apply dtbool].
    - Case "type_OpLe"%string.
      dependent induction H; dependent induction H0; simpl.
      exists (dbool (if Z_le_dec n n0 then true else false)).
      split; [reflexivity|apply dtbool].
    - Case "type_OpBagUnion"%string.
      dependent induction H; dependent induction H0; simpl.
      autorewrite with alg.
      exists (dcoll (bunion dl dl0)).
      split; [reflexivity|apply dtcoll].
      assert (r = τ) by (apply rtype_fequal; assumption).
      assert (r0 = τ) by (apply rtype_fequal; assumption).
      rewrite H1 in *; rewrite H2 in *.
      apply forall_typed_bunion; assumption.
    - Case "type_OpBagDiff"%string.
      dependent induction H; dependent induction H0; simpl.
      autorewrite with alg.
      exists (dcoll (bminus dl0 dl)).
      split; [reflexivity|apply dtcoll].
      assert (r = τ) by (apply rtype_fequal; assumption).
      assert (r0 = τ) by (apply rtype_fequal; assumption).
      rewrite H1 in *; rewrite H2 in *.
      apply forall_typed_bminus; assumption.
    - Case "type_OpBagMin"%string.
      dependent induction H; dependent induction H0; simpl.
      autorewrite with alg.
      exists (dcoll (bmin dl dl0)).
      split; [reflexivity|apply dtcoll].
      assert (r = τ) by (apply rtype_fequal; assumption).
      assert (r0 = τ) by (apply rtype_fequal; assumption).
      rewrite H1 in *; rewrite H2 in *.
      apply forall_typed_bmin; assumption.
    - Case "type_OpBagMax"%string.
      dependent induction H; dependent induction H0; simpl.
      autorewrite with alg.
      exists (dcoll (bmax dl dl0)).
      split; [reflexivity|apply dtcoll].
      assert (r = τ) by (apply rtype_fequal; assumption).
      assert (r0 = τ) by (apply rtype_fequal; assumption).
      rewrite H1 in *; rewrite H2 in *.
      apply forall_typed_bmax; assumption.
    - Case "type_OpBagNth"%string.
      dependent induction H; dependent induction H0; simpl.
      rtype_equalizer; subst.
      destruct n; simpl in *.
      + destruct dl.
        * exists dnone; split; eauto; repeat constructor.
        * inversion H; subst.
          exists (dsome d); split; [auto|];
            constructor; auto.
      + case_eq (nth_error dl (Pos.to_nat p)); intros.
        * apply nth_error_In in H0.
          rewrite Forall_forall in H.
          specialize (H d H0).
          exists (dsome d); split; [auto|];
            constructor; auto.
        * exists (dnone); split; [auto|repeat constructor].
      + exists (dnone); split; [auto|repeat constructor].
    - Case "type_OpContains"%string.
      inversion H0.
      rtype_equalizer; subst.
      dependent induction H0.
      rtype_equalizer; subst. subst.
      simpl.
      destruct (in_dec data_eq_dec d1 dl).
      + exists (dbool true).
        split; try reflexivity.
        apply dtbool.
      + exists (dbool false).
        split; try reflexivity.
        apply dtbool.
    - Case "type_OpStringConcat"%string.
      dependent induction H; dependent induction H0; simpl.
      eauto.
    - Case "type_OpStringJoin"%string.
      dependent induction H; dependent induction H0; simpl.
      rtype_equalizer; subst.
      assert (r = String)
        by (apply rtype_fequal; assumption); subst; clear x.
      unfold lifted_join; simpl.
      induction dl; simpl in *.
      + rewrite Forall_forall in H; simpl in *.
        exists (dstring ""); eauto.
      + inversion H; subst.
        specialize (IHdl H3).
        elim IHdl; clear IHdl; intros.
        elim H0; clear H0; intros.
        unfold lift in *.
        unfold lifted_stringbag in *.
        destruct (data_type_String_inv H2); subst.
        simpl.
        destruct (lift_map (ondstring (fun x2 : string => x2)) dl); try congruence.
        simpl.
        exists (dstring match l with
                  | [] => x0
                  | _ :: _ => x0 ++ s ++ String.concat s l
                        end).
        auto.
    - Case "type_OpNatBinary"%string.
      dependent induction H; dependent induction H0; simpl.
      eauto.
    - Case "type_OpFloatBinary"%string.
      dependent induction H; dependent induction H0; simpl.
      eauto.
    - Case "type_OpFloatCompare"%string.
      dependent induction H; dependent induction H0; simpl.
      eauto.
    - Case "type_OpForeignBinary"%string.
      eapply foreign_binary_op_typing_sound; eauto.
  Qed.

  (** Additional auxiliary lemmas *)

  Lemma tdot_rec_concat_sort_neq {A} (l:list (string*A)) a b xv :
       a <> b ->
       tdot (rec_concat_sort l [(a, xv)]) b = 
       tdot (rec_sort l) b.
   Proof.
     unfold tdot, edot; intros.
     unfold rec_concat_sort.
     apply (@assoc_lookupr_drec_sort_app_nin string ODT_string).
     simpl; intuition.
   Qed.

  Lemma tdot_rec_concat_sort_eq {A} (l : list (string * A)) a b :
               ~ In a (domain l) ->
               tdot (rec_concat_sort l [(a, b)]) a = Some b.
  Proof.
    unfold tdot.
    apply (@assoc_lookupr_insertion_sort_fresh string ODT_string).
  Qed.
  
End TBinaryOperators.

  Tactic Notation "binary_op_type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "type_OpEqual"%string
    | Case_aux c "type_OpRecConcat"%string
    | Case_aux c "type_OpRecMerge_closed"%string
    | Case_aux c "type_OpRecMerge_open"%string
    | Case_aux c "type_OpAnd"%string
    | Case_aux c "type_OpOr"%string
    | Case_aux c "type_OpLt"%string
    | Case_aux c "type_OpLe"%string
    | Case_aux c "type_OpBagUnion"%string
    | Case_aux c "type_OpBagDiff"%string
    | Case_aux c "type_OpBagMin"%string
    | Case_aux c "type_OpBagMax"%string
    | Case_aux c "type_OpBagNth"%string
    | Case_aux c "type_OpContains"%string
    | Case_aux c "type_OpStringConcat"%string
    | Case_aux c "type_OpStringJoin"%string
    | Case_aux c "type_OpNatBinary"%string
    | Case_aux c "type_OpFloatBinary"%string
    | Case_aux c "type_OpFloatCompare"%string
    | Case_aux c "type_OpForeignBinary"%string].

