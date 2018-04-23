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
Require Import ZArith.
Require Import Compare_dec.
Require Import Utils.
Require Import Types.
Require Import CommonData.
Require Import ForeignData.
Require Import ForeignOperators.
Require Import ForeignDataTyping.
Require Import Operators.
Require Import TData.
Require Import TUtil.
Require Import GroupBy.

Section TGroupBy.
  
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Import ListNotations.
  
  Definition GroupBy_type
             (g : string) 
             (sl : list string) 
             (k : record_kind)
             (τl : list (string * rtype)) 
             (pf : is_list_sorted ODT_lt_dec (domain τl) = true)
    : rtype
    := Coll
         (Rec Closed
              (rec_concat_sort
                 (rproject τl sl) [(g, Coll (Rec k τl pf))]) rec_sort_pf).

  Lemma typed_group_to_partitions_yields_typed_data
        {key:data} {values:list data} {τkeys pf τvalues} :
    key ▹ Rec Closed τkeys pf ->
    Forall (fun v => v ▹ τvalues) values ->
    forall g,
    exists d' : data,
      group_to_partitions g (key,values) = Some d'
      /\  d' ▹ Rec Closed (rec_concat_sort τkeys [(g,Coll τvalues)]) rec_sort_pf.
  Proof.
    Opaque rec_sort.
    intros.
    unfold group_to_partitions; simpl.
    dtype_inverter.
    eexists; split; [reflexivity | ].
    invcs H.
    rtype_equalizer; subst.
    intuition; subst.
    eapply dtrec; try reflexivity.
    - generalize (drec_sort_sorted  (rl ++ [(g,Coll τvalues)])); simpl; trivial.
    - apply rec_sort_Forall2; simpl.
      + repeat rewrite domain_app; f_equal.
        apply sorted_forall_same_domain; trivial.
      + apply Forall2_app; trivial; simpl.
        constructor; simpl; trivial.
        split; trivial.
        constructor; trivial.
        Transparent rec_sort.
  Qed.

  Lemma typed_to_partitions_yields_typed_data
        {g:string}
        (l:list (data*list data))
        {τkeys pf τvalues}  :
    Forall (fun kv =>
              (fst kv) ▹ Rec Closed τkeys pf /\
              Forall (fun v => v ▹ τvalues) (snd kv)) l ->
    exists dl' : list data,
      to_partitions g l = Some dl'
      /\ Forall (fun d' => d' ▹ Rec Closed (rec_concat_sort τkeys [(g,Coll τvalues)]) rec_sort_pf) dl'.
  Proof.
    unfold to_partitions; intros F.
    apply lift_map_Forall_exists_and.
    revert F.
    apply Forall_impl; intros.
    destruct a; destruct H as [typ F]; simpl in *.
    apply (typed_group_to_partitions_yields_typed_data typ F).
  Qed.

  Lemma typed_group_of_key_yields_typed_data eval_key k l τ :
    Forall (fun d => d ▹ τ) l ->
    Forall (fun d => exists y, eval_key d = Some y) l ->
    exists dl' : list data,
      group_of_key eval_key k l = Some dl'
      /\ Forall (fun d' => d' ▹ τ) dl'.
  Proof.
    intros.
    unfold group_of_key.
    destruct (lift_filter_Forall_exists
                (fun d : data => key_is_eq_r eval_key d k) l)
      as [dl' [eqq subl]].
    - revert H0. apply Forall_impl; intros ? [? eqq].
      unfold key_is_eq_r.
      rewrite eqq; simpl.
      match_destr; eauto.
    - exists dl'; split; trivial.
      rewrite subl; trivial.
  Qed.

  Lemma typed_group_by_nested_eval_yields_typed_data eval_key l τ τ' :
    Forall (fun d => d ▹ τ) l ->
    Forall (fun d => exists y, eval_key d = Some y /\ y ▹ τ') l ->
    exists dl' : list (data*list data),
      group_by_nested_eval eval_key l = Some dl'
      /\ Forall (fun d'dl' => (fst d'dl') ▹ τ' /\ Forall (fun d => d▹ τ) (snd d'dl')) dl'.
  Proof.
    intros F1 F2.
    unfold group_by_nested_eval.
    destruct (lift_map_Forall_exists_and (fun d : data => eval_key d) l F2)
      as [l1 [eqq Pl1]].
    rewrite eqq; simpl.
    apply lift_map_Forall_exists_and.
    apply bdistinct_Forall.
    revert Pl1.
    apply Forall_impl; intros.
    assert (F2': Forall (fun d : data => exists y : data, eval_key d = Some y) l).
    { revert F2; apply Forall_impl; firstorder. }
    destruct (typed_group_of_key_yields_typed_data _ a _ _ F1 F2')
      as [g [eqq3 F3]].
    rewrite eqq3; simpl.
    eauto.
  Qed.

  Lemma typed_group_by_nested_eval_keys_partition_yields_typed_data g eval_key l τ τkeys pf :
    Forall (fun d => d ▹ τ) l ->
    Forall (fun d => exists y, eval_key d = Some y /\ y ▹ Rec Closed τkeys pf) l ->
    exists dl' : list data,
      group_by_nested_eval_keys_partition g eval_key l = Some dl'
      /\ Forall (fun d' => d' ▹ Rec Closed (rec_concat_sort τkeys [(g,Coll τ)]) rec_sort_pf) dl'.
  Proof.
    intros F1 F2.
    unfold group_by_nested_eval_keys_partition.
    destruct (typed_group_by_nested_eval_yields_typed_data _ _ _ _ F1 F2)
      as [? [eqq3 F3]].
    rewrite eqq3; simpl.
    eapply typed_to_partitions_yields_typed_data; eauto.
  Qed.
  
  Lemma typed_group_by_nested_eval_table_yields_typed_data {d k τl pf} :
    dcoll d ▹ Coll (Rec k τl pf) ->
    forall g sl,
      sublist sl (domain τl) ->
    exists d' : data,
      lift dcoll (group_by_nested_eval_table g sl d) = Some d'
      /\ d' ▹ GroupBy_type g sl k τl pf .
  Proof.
    unfold GroupBy_type.
    intros.
    apply Col_inv in H.
    unfold group_by_nested_eval_table.
    assert (projsort: is_list_sorted ODT_lt_dec (domain (rproject τl sl)) = true).
    { apply (is_list_sorted_sublist pf).
      apply sublist_domain.
      apply sublist_rproject.
    }
    generalize (typed_group_by_nested_eval_keys_partition_yields_typed_data
                  g
                  (fun d =>
                     match d with
                     | drec r => Some (drec (rproject r sl))
                     | _ => None
                     end) d (Rec k τl pf) (rproject τl sl) projsort); intros HH.
    cut_to HH; trivial.
    - destruct HH as [? [eqq1 F1]].
      rewrite eqq1; simpl; eexists; split; try reflexivity.
      constructor; trivial.
    - clear HH.
      revert H; apply Forall_impl; intros.
      dtype_inverter.
      eexists; split; try reflexivity.
      apply dtrec_full.
      invcs H; rtype_equalizer; subst; trivial.
      apply (rproject_well_typed _ rl); trivial.
  Qed.

End TGroupBy.
