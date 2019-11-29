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
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import RelationClasses.
Require Import EquivDec.
Require Import Utils.
Require Import Types.
Require Import ForeignData.
Require Import CommonData.
Require Import ForeignDataTyping.
Require Import TData.
Require Import RConsistentSubtype.

Section TDataInfer.
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.

  Context {m:brand_model}.

  Fixpoint infer_data_type (d:data) : option rtype
    := match d with
         | dunit => Some Unit
         | dnat n => Some Nat
         | dfloat n => Some Float
         | dbool b => Some Bool
         | dstring s => Some String
         | dcoll ld =>
           lift Coll
                ((fix infer_data_type_dcoll ld : option rtype
                  := match ld with
                       | nil => Some ⊥
                       | d::ld' => lift2 join (infer_data_type d) (infer_data_type_dcoll ld')
                     end
                 ) ld)
         | drec lsd => 
           match (fix infer_data_type_drec lsd : option (list(string*rtype))
                  := match lsd with
                       | nil => Some nil
                       | (s,d)::lsd' => 
                         match (infer_data_type d), (infer_data_type_drec lsd') with
                           | Some r, Some lsr' =>
                             Some ((s,r)::lsr')
                           | _, _ => None
                         end
                     end
                 ) lsd with
             | Some l => RecMaybe Closed l
             | None => None
           end
         | dleft d =>
            lift (fun t => Either t ⊥) (infer_data_type d)
         | dright d =>
            lift (fun t => Either ⊥ t) (infer_data_type d)
         | dbrand b d =>
           match is_canon_brands_dec brand_relation_brands b with
              | left pf => match infer_data_type d with
                           | Some t =>
                             if subtype_dec t (brands_type b)
                             then Some (Brand b)
                             else Some ⊤
                  | None => None
                end
              | right _ => None
           end
         | dforeign df => lift Foreign (foreign_data_typing_infer df)
       end.

  Lemma infer_data_type_drec_domain {d:list (string*data)} {r'} :
    (fix infer_data_type_drec lsd : option (list(string*rtype))
                  := match lsd with
                       | nil => Some nil
                       | (s,d)::lsd' => 
                         match (infer_data_type d), (infer_data_type_drec lsd') with
                           | Some r, Some lsr' =>
                             Some ((s,r)::lsr')
                           | _, _ => None
                         end
                     end
                 ) d = Some r' ->
     domain d = domain r'.
  Proof.
    revert r'.
    induction d; simpl.
    - inversion 1; subst. simpl; trivial.
    - destruct a.
      destruct (infer_data_type d0); try discriminate.
      case_option; try discriminate.
      intros; simpl in *.
      inversion H0; subst. simpl;
      f_equal. eauto.
  Qed.
    
  Lemma infer_data_type_normalized' {d} :
    data_normalized brand_relation_brands d ->
    {τ | infer_data_type d = Some τ}.
  Proof.
    induction d; intros dn
    ; try solve [simpl; eexists; invcs dn; reflexivity].
    - simpl.
      induction c.
      + eexists; simpl; reflexivity.
      + invcs H.
        destruct (IHc H3).
        * invcs dn.
            invcs H0.
            constructor; trivial.
        * apply some_lift in e.
          destruct e as [? eqs ?]; subst.
          rewrite eqs.
          { destruct H2.
            - invcs dn.
              invcs H0; trivial.
            - rewrite e; simpl.
              eexists; reflexivity.
          }
    - induction r; simpl.
      + eexists; reflexivity.
      + destruct a.
        invcs H.
        destruct (IHr H3).
        * invcs dn.
          invcs H0.
          constructor; trivial.
          eapply is_list_sorted_cons_inv; eauto.
        * simpl in e.
          case_option_in e; try discriminate.
          destruct (RecMaybe_some_pf e) as [pf ?]; subst.
          { destruct H2.
            - invcs dn.
              invcs H0.
              trivial.
            - simpl in e0.
              rewrite e0.
              assert (pff:is_list_sorted ODT_lt_dec (domain ((s,x)::l)) = true).
              + rewrite domain_cons.
                rewrite <- (infer_data_type_drec_domain eqs).
                invcs dn; simpl in *; trivial.
              + rewrite (RecMaybe_pf_some Closed _ pff).
                eexists; reflexivity.
          }
    - destruct IHd.
      + invcs dn; trivial.
      + simpl; rewrite e; simpl.
         eexists; reflexivity.
    - destruct IHd.
      + invcs dn; trivial.
      + simpl; rewrite e; simpl.
         eexists; reflexivity.
    - destruct IHd.
      + invcs dn; trivial.
      + simpl; rewrite e; simpl.
        match_destr.
        * match_destr; eexists; reflexivity.
        * elim n.
          invcs dn; tauto.
    - simpl.
      destruct (@foreign_data_typing_infer_normalized _ _ _ fd).
      + invcs dn; trivial.
      + rewrite e. simpl.
        eexists; reflexivity.
  Qed.

  Theorem infer_data_type_normalized {d} :
    data_normalized brand_relation_brands d ->
    {τ | infer_data_type d = Some τ}.
  Proof.
    case_eq (infer_data_type d); intros.
    - eexists; reflexivity.
    - apply infer_data_type_normalized' in H0.
      destruct H0; congruence.
  Defined.

  Theorem infer_data_type_correct {d τ} :
    infer_data_type d = Some τ ->
    d ▹ τ.
  Proof.
    Hint Constructors data_type Forall Forallt.
    revert τ.
    induction d; simpl; 
    try solve[inversion 1; subst; eauto 2].
    - intros τ eqs. apply some_lift in eqs.
      destruct eqs as [t ? ?]; subst τ.
      constructor.
      revert t H e.
      induction c; simpl; intros; [eauto|].
      invcs H.
      unfold lift2 in e.
      case_option_in e; try discriminate.
      case_option_in e; try discriminate.
      specialize (IHc _ H3 eqs0).
      invcs e.
      constructor.
      + rewrite <- (rtype_join_subtype_l); auto.
      + revert IHc.
        apply Forall_impl.
        intros.
        rewrite <- (rtype_join_subtype_r); auto.
    - intros τ eqs.
      case_option_in eqs; try discriminate.
      destruct (RecMaybe_some_pf eqs) as [pf ?]; subst.
      clear eqs; rename eqs0 into eqs.
      revert r l pf eqs H.
      induction r; simpl; intros.
      + invcs eqs. apply dtrec_full; constructor.
      + destruct a. invcs H.
        case_option_in eqs; try discriminate.
        case_option_in eqs; try discriminate.
        invcs eqs.
        specialize (IHr _ (is_list_sorted_cons_inv _ pf) eqs1 H3).
        specialize (H2 _ eqs0); simpl in H2.
        apply dtrec_closed_inv in IHr.
        apply dtrec_full.
        constructor; simpl; tauto.
    - intros τ eqs.
      apply some_lift in eqs.
      destruct eqs as [t ? ?]; subst τ.
      eauto.
    - intros τ eqs.
      apply some_lift in eqs.
      destruct eqs as [t ? ?]; subst τ.
      eauto.
    - intros τ eqs.
      case_option_in eqs
      ; match_case_in eqs; intros ? re1; rewrite re1 in eqs
      ; try discriminate.
      match_case_in eqs; intros ? re2; rewrite re2 in eqs
      ; try discriminate.
      invcs eqs.
      constructor; trivial.
      + eauto.
      + rewrite Forall_forall.
        intros ? inn τ look.
        specialize (IHd _ eqs0).
        rewrite <- (brands_type_sub_part _ _ _ look inn).
        rewrite <- s.
        trivial.
      + reflexivity.
      + invcs eqs.
        constructor.
        constructor; trivial.
        eauto.
    -intros τ eqs.
     apply some_lift in eqs.
     destruct eqs as [t ? ?]; subst τ.
     apply foreign_data_typing_infer_correct in e.
     eauto.
  Qed.

  Theorem infer_data_type_least {d τ₁ τ₂} : 
    infer_data_type d = Some τ₁ ->
    d ▹τ₂ ->
    τ₁ <: τ₂.
  Proof.
    Hint Constructors subtype.
    revert τ₁ τ₂.
    induction d; simpl;
      try solve[inversion 1; subst; intros; destruct (istop τ₂); subst; trivial; dtype_inverter; trivial
               | intros; invcs H; invcs H0; auto 2].
    - intros τ₁ τ₂ eqs ht.
      apply some_lift in eqs.
      destruct eqs as [? eqs' ?]; subst.
      destruct (istop τ₂); subst; trivial.
      destruct (data_type_dcoll_inv e ht) as [τ₂' ?]; subst.
      constructor.
      clear e.
      invcs ht.
      rtype_equalizer.
      subst.
      revert x H H2 eqs'; clear.
      induction c; simpl; intros τ fl1 fl2 eqs; invcs eqs; trivial.
      unfold lift2 in H0.
      case_option_in H0; try discriminate.
      case_option_in H0; try discriminate.
      invcs H0.
      invcs fl1.
      invcs fl2.
      apply (join_least (olattice:=rtype_olattice)).
      + apply H1; eauto.
      + apply IHc; eauto.
    - intros τ₁ τ₂ eqs ht.
      case_option_in eqs; try discriminate.
      destruct (RecMaybe_some_pf eqs) as [pf ?]; subst.
      clear eqs; rename eqs0 into eqs.
      invcs ht; trivial.
      constructor.
      + intros s τ look.
        apply lookup_in in look.
        generalize (sublist_In H1 _ look); intros inn2.
        clear H1 H2 rl_sub look pf0.
        revert rl pf' l pf H inn2 H3 eqs.
        clear.
        induction r; intros
        ; invcs H3; invcs H; invcs inn2.
        * destruct a.
          case_option_in eqs; try discriminate.
          case_option_in eqs; try discriminate.
          simpl in H2; destruct H2; subst.
          invcs eqs.
          simpl.
          match_destr; [| congruence].
          eexists; split; [reflexivity|].
          eauto.
        * destruct a.
          case_option_in eqs; try discriminate.
          case_option_in eqs; try discriminate.
          simpl in H2; destruct H2; subst.
          invcs eqs.
          destruct (IHr _ (is_list_sorted_cons_inv _ pf') _ (is_list_sorted_cons_inv _ pf)); trivial.
          simpl.
          match_destr; [| eauto].
          apply is_list_sorted_NoDup_strlt in pf.
          subst s.
          invcs pf.
          destruct H0 as [inn _].
          apply lookup_in in inn.
          apply in_dom in inn.
          intuition.
      + intuition; subst.
        rewrite <- (infer_data_type_drec_domain eqs) in H2.
        rewrite <- (sorted_forall_same_domain H3).
        trivial.
    - intros τ₁ τ₂ eqs ht.
      apply some_lift in eqs.
      destruct eqs as [? eqs' ?]; subst.
      destruct (istop τ₂); subst; trivial.
      destruct (data_type_dleft_inv e ht) as [τ₂' [? ?]]; subst.
      clear e.
      invcs ht; rtype_equalizer.
      subst.
      eauto.
    - intros τ₁ τ₂ eqs ht.
      apply some_lift in eqs.
      destruct eqs as [? eqs' ?]; subst.
      destruct (istop τ₂); subst; trivial.
      destruct (data_type_dright_inv e ht) as [τ₂' [? ?]]; subst.
      clear e.
      invcs ht; rtype_equalizer.
      subst.
      eauto.
    - intros τ₁ τ₂ eqs ht.
      match_destr_in eqs.
      case_option_in eqs; try discriminate.
      match_destr_in eqs.
      + invcs eqs.
        destruct (istop τ₂); subst; trivial.
        invcs ht; trivial.
        eauto.
      + invcs eqs.
        cut (τ₂ = ⊤); [intros; subst; reflexivity | ].
        invcs ht; trivial.
        elim n.
        revert H3 IHd eqs0.
        clear.
        (*        unfold brands_type. *)
        rewrite brands_type_alt.
        induction b; simpl; trivial; intros.
        invcs H3.
        specialize (IHb H2 IHd eqs0).
        rewrite fold_right_app.
        revert IHb.
        simpl.
        generalize (fold_right rtype_meet ⊤ (brands_type_list b)).
        intros.
        match_case; intros τ2 look.
        simpl.
        rewrite Forall_forall in H2.
        apply (meet_most (olattice:=rtype_olattice)); trivial.
        apply IHd; eauto.
    - intros τ₁ τ₂ eqs ht.
     apply some_lift in eqs.
     destruct eqs as [t ? ?]; subst.
     invcs ht; trivial.
     constructor.
     eapply foreign_data_typing_infer_least; eauto.
  Qed.

  Theorem data_has_principal_type {d} :
    data_normalized brand_relation_brands d ->
    {τ | d ▹τ & (forall τ', d ▹τ' -> τ <: τ')}.
  Proof.
    intros dn.
    destruct (infer_data_type_normalized dn) as [τ τeq].
    exists τ.
    - apply infer_data_type_correct; trivial.
    - intros. eapply infer_data_type_least; eauto.
  Defined.

  Theorem infer_data_type_complete {d τ} :
    d ▹τ -> {τ' | infer_data_type d = Some τ'}.
  Proof.
    intros.
    apply data_type_normalized in H.
    eapply infer_data_type_normalized in H.
    trivial.
  Defined.
  
  Lemma normalized_data_type_infer {d τ} :
    infer_data_type d = Some τ ->
    data_normalized brand_relation_brands d.
  Proof.
    intros i.
    apply infer_data_type_correct in i.
    eapply data_type_normalized; eauto.
  Qed.

  Section dt_dec.
    (** We can compute if the data_type relation holds using 
       by seeing if its inferred type (if any) is a subtype of the
       given type. *)
    Theorem data_type_dec d τ : {data_type d τ} + {~ data_type d τ}.
    Proof.
      case_eq (infer_data_type d); [intros r eqr|intros neqr].
      - destruct (subtype_dec r τ).
        + left.
          apply infer_data_type_correct in eqr.
          rewrite s in eqr. trivial.
        + right. intro dt. apply n.
          eapply infer_data_type_least; eauto.
      - right. intro dt. destruct (infer_data_type_complete dt).
        congruence.
    Defined.
  End dt_dec.

End TDataInfer.

