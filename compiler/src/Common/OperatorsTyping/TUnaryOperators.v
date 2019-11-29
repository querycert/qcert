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
Require Import Program.
Require Import RelationClasses.
Require Import EquivDec.
Require Import Utils.
Require Import Types.
Require Import CommonData.
Require Import ForeignData.
Require Import ForeignDataToJSON.
Require Import ForeignOperators.
Require Import ForeignDataTyping.
Require Import Operators.
Require Import TUtil.
Require Import TData.
Require Import TSortBy.
Require Import ForeignOperatorsTyping.

Section TUnaryOperators.
  (** Typing rules for unary operators *)

  Context {fdata:foreign_data}.
  Context {ftojson:foreign_to_JSON}.
  Context {fuop:foreign_unary_op}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.
  Context {fuoptyping:foreign_unary_op_typing}.

  Section typ.
    Inductive unary_op_type : unary_op -> rtype -> rtype -> Prop :=
    | type_OpIdentity τ :
        unary_op_type OpIdentity τ τ
    | type_OpNeg:
        unary_op_type OpNeg Bool Bool
    | type_OpRec {τ} s pf :
        unary_op_type (OpRec s) τ (Rec Closed ((s,τ)::nil) pf)
    | type_OpDot {τ' τout} k s pf:
        tdot τ' s = Some τout ->
        unary_op_type (OpDot s) (Rec k τ' pf) τout
    | type_OpRecRemove {τ} k s pf1 pf2:
        unary_op_type (OpRecRemove s) (Rec k τ pf1) (Rec k (rremove τ s) pf2)
    | type_OpRecProject {τ} k sl pf1 pf2:
        sublist sl (domain τ) -> 
        unary_op_type (OpRecProject sl) (Rec k τ pf1) (Rec Closed (rproject τ sl) pf2)
    | type_OpBag {τ}:
        unary_op_type OpBag τ (Coll τ)
    | type_OpSingleton τ :
        unary_op_type OpSingleton (Coll τ) (Option τ)
    | type_OpFlatten τ:
        unary_op_type OpFlatten (Coll (Coll τ)) (Coll τ)
    | type_OpDistinct τ:
        unary_op_type OpDistinct (Coll τ) (Coll τ)
    | type_OpOrderBy {τ} k sl pf1 pf2:
        sublist (List.map fst sl) (domain τ) ->
        order_by_has_sortable_type τ (List.map fst sl) ->
        unary_op_type (OpOrderBy sl) (Coll (Rec k τ pf1)) (Coll (Rec k τ pf2))
    | type_OpCount τ:
        unary_op_type OpCount (Coll τ) Nat
    | type_OpToString τ:
        unary_op_type OpToString τ String
    | type_OpToText τ:
        unary_op_type OpToText τ String
    | type_OpLength:
        unary_op_type OpLength String Nat
    | type_OpSubstring start olen:
        unary_op_type (OpSubstring start olen) String String
    | type_OpLike pat oescape:
        unary_op_type (OpLike pat oescape) String Bool
    | type_OpLeft τl τr:
        unary_op_type OpLeft τl (Either τl τr)
    | type_OpRight τl τr:
        unary_op_type OpRight τr (Either τl τr)
    | type_OpBrand b :
        unary_op_type (OpBrand b) (brands_type b) (Brand b)
    | type_OpUnbrand {bs} :
        unary_op_type OpUnbrand (Brand bs) (brands_type bs)
    | type_OpCast br {bs} :
        unary_op_type (OpCast br) (Brand bs) (Option (Brand br))
    | type_OpNatUnary (u:nat_arith_unary_op) :
        unary_op_type (OpNatUnary u) Nat Nat
    | type_OpNatSum:
        unary_op_type OpNatSum (Coll Nat) Nat
    | type_OpNatMin:
        unary_op_type OpNatMin (Coll Nat) Nat
    | type_OpNatMax:
        unary_op_type OpNatMax (Coll Nat) Nat
    | type_OpNatMean:
        unary_op_type OpNatMean (Coll Nat) Nat
    | type_OpFloatOfNat:
        unary_op_type OpFloatOfNat Nat Float
    | type_OpFloatUnary (u:float_arith_unary_op) :
        unary_op_type (OpFloatUnary u) Float Float
    | type_OpFloatTruncate:
        unary_op_type OpFloatTruncate Float Nat
    | type_OpFloatSum:
        unary_op_type OpFloatSum (Coll Float) Float
    | type_OpFloatMean:
        unary_op_type OpFloatMean (Coll Float) Float
    | type_OpFloatMin:
        unary_op_type OpFloatBagMin (Coll Float) Float
    | type_OpFloatMax:
        unary_op_type OpFloatBagMax (Coll Float) Float
    | type_OpForeignUnary {fu τin τout} :
        foreign_unary_op_typing_has_type fu τin τout ->
        unary_op_type (OpForeignUnary fu) τin τout.

  End typ.

  Tactic Notation "unary_op_type_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "type_OpIdentity"%string
    | Case_aux c "type_OpNeg"%string
    | Case_aux c "type_OpRec"%string
    | Case_aux c "type_OpDot"%string
    | Case_aux c "type_OpRecRemove"%string
    | Case_aux c "type_OpRecProject"%string
    | Case_aux c "type_OpBag"%string
    | Case_aux c "type_OpSingleton"%string
    | Case_aux c "type_OpFlatten"%string
    | Case_aux c "type_OpDistinct"%string
    | Case_aux c "type_OpOrderBy"%string
    | Case_aux c "type_OpCount"%string
    | Case_aux c "type_OpToString"%string
    | Case_aux c "type_OpToText"%string
    | Case_aux c "type_OpLength"%string
    | Case_aux c "type_OpSubstring"%string
    | Case_aux c "type_OpLike"%string
    | Case_aux c "type_OpLeft"%string
    | Case_aux c "type_OpRight"%string
    | Case_aux c "type_OpBrand"%string
    | Case_aux c "type_OpUnbrand"%string
    | Case_aux c "type_OpCast"%string
    | Case_aux c "type_OpNatUnary"%string
    | Case_aux c "type_OpNatSum"%string
    | Case_aux c "type_OpNatMin"%string
    | Case_aux c "type_OpNatMax"%string
    | Case_aux c "type_OpNatMean"%string
    | Case_aux c "type_OpFloatOfNat"%string
    | Case_aux c "type_OpFloatUnary"%string
    | Case_aux c "type_OpFloatTruncate"%string
    | Case_aux c "type_OpFloatSum"%string
    | Case_aux c "type_OpFloatMean"%string
    | Case_aux c "type_OpFloatBagMin"%string
    | Case_aux c "type_OpFloatBagMax"%string
    | Case_aux c "type_OpForeignUnary"%string].

  (** Type soundness lemmas for individual operators *)

  Lemma forall_typed_bdistinct {τ} d1:
    Forall (fun d : data => data_type d τ) d1 ->
    Forall (fun d : data => data_type d τ) (bdistinct d1).
  Proof.
    intros; rewrite Forall_forall in *.
    intros.
    induction d1.
    simpl in *.
    contradiction.
    simpl in *.
    assert (forall x : data, In x d1 -> data_type x τ)
      by (apply (forall_in_weaken (fun x => a = x)); assumption).
    destruct (mult (bdistinct d1) a).
    elim H0; intros; clear H0.
    rewrite <- H2 in *.
    apply (H a).
    left; reflexivity.
    specialize (IHd1 H1 H2); assumption.
    specialize (IHd1 H1 H0); assumption.
  Qed.

  Lemma rremove_well_typed τ s dl:
    Forall2
      (fun (d : string * data) (r : string * rtype) =>
         fst d = fst r /\ data_type (snd d) (snd r)) dl τ ->
    Forall2
      (fun (d : string * data) (r : string * rtype) =>
         fst d = fst r /\ data_type (snd d) (snd r)) (rremove dl s)
      (rremove τ s).
  Proof.
    intros F2.
    induction F2; simpl; trivial.
    destruct H; simpl in *.
    rewrite H.
    match_destr.
    auto.
  Qed.

  Lemma rproject_well_typed τ rl s dl:
    Forall2
      (fun (d : string * data) (r : string * rtype) =>
         fst d = fst r /\ data_type (snd d) (snd r)) dl rl ->
    sublist s (domain τ) ->
    sublist τ rl ->
    is_list_sorted ODT_lt_dec (domain τ) = true ->
    is_list_sorted ODT_lt_dec (domain rl) = true ->
    Forall2
      (fun (d : string * data) (r : string * rtype) =>
         fst d = fst r /\ data_type (snd d) (snd r)) (rproject dl s)
      (rproject τ s).
  Proof.
    intros.
    assert (sublist s (domain rl)) by
        (apply (sublist_trans s (domain τ) (domain rl)); try assumption;
         apply sublist_domain; assumption).
    assert (NoDup (domain rl))
      by (apply is_list_sorted_NoDup_strlt; assumption).
    rewrite (rproject_sublist τ rl s H2 H3); try assumption.
    clear H0 H1 H4 H2.
    induction H.
    - apply Forall2_nil.
    - inversion H5; subst.
      assert (is_list_sorted ODT_lt_dec (domain l') = true)
        by (apply (@rec_sorted_skip_first string ODT_string _ l' y); assumption).
      specialize (IHForall2 H1 H6).
      elim H; intros.
      simpl; rewrite H2.
      destruct (in_dec string_dec (fst y) s).
      apply Forall2_cons; try assumption; split; assumption.
      assumption.
  Qed.
  
  (* TODO: move this stuff *)
  Definition canon_brands_alt {br:brand_relation} (b:brands) :=
    fold_right meet [] (map (fun x => x::nil) b).

  Lemma canon_brands_alt_is_canon {br:brand_relation} (b:brands) :
    is_canon_brands brand_relation_brands (canon_brands_alt b).
  Proof.
    unfold canon_brands_alt.
    destruct b; simpl.
    - red; intuition.
    - apply brand_meet_is_canon.
  Qed.

  Lemma canon_brands_fold_right_hoist {br:brand_relation} (l:list brands) :
    fold_right
      (fun a b : brands => canon_brands brand_relation_brands (a ++ b))
      [] l =
    canon_brands brand_relation_brands
                 (fold_right (fun a b : brands => (a ++ b))
                             [] l).
  Proof.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl.
      rewrite app_commutative_equivlist.
      rewrite canon_brands_canon_brands_app1.
      rewrite app_commutative_equivlist.
      trivial.
  Qed.
  
  Lemma canon_brands_alt_equiv {br:brand_relation} (b:brands) :
    canon_brands brand_relation_brands b
    =  canon_brands_alt b.
  Proof.
    unfold canon_brands_alt.
    unfold meet; simpl.
    unfold brand_meet.
    rewrite canon_brands_fold_right_hoist.
    f_equal.
    generalize (fold_right_app_map_singleton b); simpl.
    auto.
  Qed.

  (** Main type-soundness lemma for unary operators *)
  Lemma typed_unary_op_yields_typed_data {τ₁ τout} (d1:data) (u:unary_op) :
    (d1 ▹ τ₁) -> (unary_op_type u τ₁ τout) ->
    (exists x, unary_op_eval brand_relation_brands u d1 = Some x /\ x ▹ τout).
  Proof.
    Hint Resolve dtsome dtnone.
    Hint Constructors data_type.
    intros.
    unary_op_type_cases (dependent induction H0) Case; simpl.
    - Case "type_OpIdentity"%string.
      eauto.
    - Case "type_OpNeg"%string.
      dependent induction H; simpl.
      exists (dbool (negb b)).
      split; [reflexivity|apply dtbool].
    - Case "type_OpRec"%string.
      exists (drec [(s,d1)]).
      split; [reflexivity|apply dtrec_full].
      apply Forall2_cons.
      split; [reflexivity|assumption].
      apply Forall2_nil.
    - Case "type_OpDot"%string.
      dependent induction H. rtype_equalizer; subst.
      unfold tdot in *.
      unfold edot in *.
      apply (Forall2_lookupr_some H1).
      eapply assoc_lookupr_nodup_sublist; eauto.
    - Case "type_OpRecRemove"%string.
      dependent induction H; rtype_equalizer. subst.
      exists (drec (rremove dl s)); split; try reflexivity.
      eapply dtrec; try (apply rremove_well_typed; try eassumption).
      + apply is_sorted_rremove; trivial.
      + apply sublist_filter; trivial.
      + intuition; congruence.
    - Case "type_OpRecProject"%string.
      dependent induction H.
      rtype_equalizer ; subst.
      exists (drec (rproject dl sl)); split; try reflexivity.
      apply dtrec_full.
      clear H0 pf1.
      apply (rproject_well_typed τ rl); try assumption.
    - Case "type_OpBag"%string.
      exists (dcoll [d1]); split; try
      reflexivity.  apply dtcoll; apply Forall_forall; intros.  elim H0;
      intros.  rewrite <- H1; assumption.  contradiction.
    - Case "type_OpSingleton"%string.
      inversion H; rtype_equalizer.
      subst.
      repeat (destruct dl; eauto).
      inversion H2; subst.
      eauto.
    - Case "type_OpFlatten"%string.
      dependent induction H.
      rewrite Forall_forall in *.
      unfold oflatten.
      induction dl; simpl in *.
      exists (dcoll []).
      split; try reflexivity.
      apply dtcoll; apply Forall_nil.
      assert (forall x : data, In x dl -> data_type x r) by
          (intros; apply (H x0); right; assumption).
      elim (IHdl H0); clear IHdl H0; intros.
      elim H0; clear H0; intros.
      unfold lift in H0.
      assert (exists a', lift_flat_map
           (fun x : data =>
            match x with
            | dcoll y => Some y
            | _ => None
            end) dl = Some a' /\ x0 = (dcoll a')).
      revert H0.
      destruct (lift_flat_map
       (fun x1 : data =>
        match x1 with
          | dcoll y => Some y
          | _ => None
        end) dl); intros.
      inversion H0.
      exists l; split; reflexivity.
      congruence.
      elim H2; clear H2; intros.
      elim H2; clear H2; intros.
      rewrite H2; clear H2 H0.
      assert (data_type a r)
        by (apply (H a); left; reflexivity).
      assert (r = Coll τ) by (apply rtype_fequal; assumption).
      rewrite H2 in *; clear H2.
      dependent induction H0.
      assert (r0 = τ) by (apply rtype_fequal; assumption).
      simpl.
      exists (dcoll (dl0 ++ x1)); split; try reflexivity.
      apply dtcoll.
      dependent induction H1.
      assert (r1 = τ) by (apply rtype_fequal; assumption).
      apply Forall_app; rewrite Forall_forall in *.
      rewrite H2 in *; assumption.
      rewrite H3 in *; assumption.
    - Case "type_OpDistinct"%string.
      dependent induction H.
      autorewrite with alg.
      exists (dcoll (bdistinct dl)).
      split; [reflexivity|apply dtcoll].
      assert (r = τ) by (apply rtype_fequal; assumption).
      rewrite H0 in *.
      apply forall_typed_bdistinct; assumption.
    - Case "type_OpOrderBy"%string.
      intros. apply (order_by_well_typed d1 sl H H0 H1).
    - Case "type_OpCount"%string.
      dependent induction H.
      autorewrite with alg.
      exists (dnat (Z_of_nat (bcount dl))).
      split; [reflexivity|apply dtnat].
    - Case "type_OpToString"%string.
      eauto.
    - Case "type_OpToText"%string.
      eauto.
    - Case "type_OpLength"%string.
      dtype_inverter.
      eauto.
    - Case "type_OpSubstring"%string.
      dtype_inverter.
      eauto.
    - Case "type_OpLike"%string.
      dtype_inverter.
      eauto.
    - Case "type_OpLeft"%string.
      eauto.
    - Case "type_OpRight"%string.
      eauto.
    - Case "type_OpBrand"%string.
      eexists; split; try reflexivity.
      apply dtbrand'.
      + eauto.
      + rewrite brands_type_of_canon; trivial.
      + rewrite canon_brands_equiv; reflexivity.
    - Case "type_OpUnbrand"%string.
      destruct d1; try solve[inversion H].
      apply dtbrand'_inv in H.
      destruct H as [isc [dt subb]].
      eexists; split; try reflexivity.
      rewrite subb in dt.
      trivial.
    - Case "type_OpCast"%string.
      inversion H; subst.
      match_destr; [| eauto].
      econstructor; split; try reflexivity.
      constructor. 
      econstructor; eauto.
    - Case "type_OpNatUnary"%string.
      dependent induction H; simpl.
      eauto.
    - Case "type_OpNatSum"%string.
      dependent induction H. revert r x H. induction dl; simpl; [eauto|intros].
      inversion H; subst. destruct (IHdl r x H3) as [x0 [x0eq x0d]].
      destruct H2; try solve[simpl in x; discriminate].
      simpl in *.
      destruct (some_lift x0eq); subst.
      rewrite e. simpl. eauto.
    - Case "type_OpNatMin"%string.
      dependent induction H.
      destruct r.
      destruct x0; simpl in x; try congruence.
      induction dl. rewrite Forall_forall in H.
      unfold lifted_min; simpl.
      exists (dnat 0). auto.
      inversion H. subst.
      specialize (IHdl H3).
      elim IHdl; clear IHdl; intros.
      elim H0; clear H0; intros.
      unfold lifted_min in *.
      unfold lift in *.
      unfold lifted_zbag in *.
      assert (Nat = (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Nat₀ e))
        by (apply rtype_fequal; reflexivity).
      rewrite <- H4 in H2.
      destruct (data_type_Nat_inv H2); subst.
      simpl.
      destruct (lift_map (ondnat (fun x3 : Z => x3)) dl); try congruence.
      simpl.
      exists (dnat (fold_right (fun x3 y : Z => Z.min x3 y) x1 l)).
      split; [reflexivity|auto].
    - Case "type_OpNatMax"%string.
      dependent induction H.
      destruct r.
      destruct x0; simpl in x; try congruence.
      induction dl. rewrite Forall_forall in H.
      unfold lifted_max; simpl.
      exists (dnat 0). auto.
      inversion H. subst.
      specialize (IHdl H3).
      elim IHdl; clear IHdl; intros.
      elim H0; clear H0; intros.
      unfold lifted_max in *.
      unfold lift in *.
      unfold lifted_zbag in *.
      assert (Nat = (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Nat₀ e))
        by (apply rtype_fequal; reflexivity).
      rewrite <- H4 in H2.
      destruct (data_type_Nat_inv H2); subst.
      simpl.
      destruct (lift_map (ondnat (fun x3 : Z => x3)) dl); try congruence.
      simpl.
      exists (dnat (fold_right (fun x3 y : Z => Z.max x3 y) x1 l)).
      split; [reflexivity|auto].
    - Case "type_OpNatMean"%string.
      assert(dsum_pf:exists x : data, lift dnat (lift_oncoll dsum d1) = Some x /\ x ▹ Nat).
      {dependent induction H. revert r x H. induction dl; simpl; [eauto|intros].
      inversion H; subst. destruct (IHdl r x H3) as [x0 [x0eq x0d]].
      destruct H2; try solve[simpl in x; discriminate].
      simpl in *.
      destruct (some_lift x0eq); subst.
      rewrite e. simpl. eauto.
      }
      destruct dsum_pf as [x [xeq xtyp]].
      dtype_inverter.
      apply some_lift in xeq.
      destruct xeq as [? eqq1 eqq2].
      simpl in eqq1.
      inversion eqq2; clear eqq2; subst.
      destruct (is_nil_dec d1); simpl.
      + subst; simpl; eauto.
      + exists (dnat (Z.quot x (Z_of_nat (length d1)))).
         split; [ | constructor ].
         unfold darithmean.
         rewrite eqq1; simpl.
         destruct d1; simpl; congruence.
    - Case "type_OpFloatOfNat"%string.
      dependent induction H; simpl.
      eauto.
    - Case "type_OpFloatUnary"%string.
      dependent induction H; simpl.
      eauto.
    - Case "type_OpFloatTruncate"%string.
      dependent induction H; simpl.
      eauto.
    - Case "type_OpFloatSum"%string.
      dependent induction H.
      destruct r.
      destruct x0; simpl in x; try congruence.
      induction dl; unfold lifted_fsum; simpl; [eauto|intros].
      inversion H; subst.
      destruct (IHdl H3) as [x0 [x0eq x0d]].
      inversion H2.
      subst.
      unfold lifted_fsum in *.
      simpl in *.
      destruct (some_lift x0eq); subst.
      simpl.
      unfold lifted_fbag in *; simpl.
      destruct (some_lift e0); subst.
      rewrite e1; simpl; eauto.
    - Case "type_OpFloatMean"%string.
      dependent induction H.
      destruct r.
      destruct x0; simpl in x; try congruence.
      induction dl; unfold lifted_farithmean; simpl; [eauto|intros].
      inversion H; subst.
      destruct (IHdl H3) as [x0 [x0eq x0d]].
      inversion H2.
      subst.
      unfold lifted_farithmean in *.
      simpl in *.
      destruct (some_lift x0eq); subst.
      simpl.
      unfold lifted_fbag in *; simpl.
      destruct (some_lift e0); subst.
      rewrite e1; simpl; eauto.
    - Case "type_OpFloatBagMin"%string.
      dependent induction H.
      destruct r.
      destruct x0; simpl in x; try congruence.
      induction dl; unfold lifted_fmin; simpl; [eauto|intros].
      inversion H; subst.
      destruct (IHdl H3) as [x0 [x0eq x0d]].
      inversion H2.
      subst.
      unfold lifted_fmin in *.
      simpl in *.
      destruct (some_lift x0eq); subst.
      simpl.
      unfold lifted_fbag in *; simpl.
      destruct (some_lift e0); subst.
      rewrite e1; simpl; eauto.
    - Case "type_OpFloatBagMax"%string.
      dependent induction H.
      destruct r.
      destruct x0; simpl in x; try congruence.
      induction dl; unfold lifted_fmax; simpl; [eauto|intros].
      inversion H; subst.
      destruct (IHdl H3) as [x0 [x0eq x0d]].
      inversion H2.
      subst.
      unfold lifted_fmax in *.
      simpl in *.
      destruct (some_lift x0eq); subst.
      simpl.
      unfold lifted_fbag in *; simpl.
      destruct (some_lift e0); subst.
      rewrite e1; simpl; eauto.
    - Case "type_OpForeignUnary"%string.
      eapply foreign_unary_op_typing_sound; eauto.
  Qed.

End TUnaryOperators.

Tactic Notation "unary_op_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "type_OpIdentity"%string
  | Case_aux c "type_OpNeg"%string
  | Case_aux c "type_OpRec"%string
  | Case_aux c "type_OpDot"%string
  | Case_aux c "type_OpRecRemove"%string
  | Case_aux c "type_OpRecProject"%string
  | Case_aux c "type_OpBag"%string
  | Case_aux c "type_OpSingleton"%string
  | Case_aux c "type_OpFlatten"%string
  | Case_aux c "type_OpDistinct"%string
  | Case_aux c "type_OpOrderBy"%string
  | Case_aux c "type_OpCount"%string
  | Case_aux c "type_OpToString"%string
  | Case_aux c "type_OpToText"%string
  | Case_aux c "type_OpLength"%string
  | Case_aux c "type_OpSubstring"%string
  | Case_aux c "type_OpLike"%string
  | Case_aux c "type_OpLeft"%string
  | Case_aux c "type_OpRight"%string
  | Case_aux c "type_OpBrand"%string
  | Case_aux c "type_OpUnbrand"%string
  | Case_aux c "type_OpCast"%string
  | Case_aux c "type_OpNatUnary"%string
  | Case_aux c "type_OpNatSum"%string
  | Case_aux c "type_OpNatMin"%string
  | Case_aux c "type_OpNatMax"%string
  | Case_aux c "type_OpNatMean"%string
  | Case_aux c "type_OpFloatOfNat"%string
  | Case_aux c "type_OpFloatUnary"%string
  | Case_aux c "type_OpFloatTruncate"%string
  | Case_aux c "type_OpFloatSum"%string
  | Case_aux c "type_OpFloatMean"%string
  | Case_aux c "type_OpFloatBagMin"%string
  | Case_aux c "type_OpFloatBagMax"%string
  | Case_aux c "type_OpForeignUnary"%string].

