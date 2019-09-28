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
Require Import Compare_dec.
Require Import Program.
Require Import Eqdep_dec.
Require Import Bool.
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
Require Import TSortBy.
Require Import TUnaryOperators.
Require Import TBinaryOperators.

Section TOperatorsInfer.
  (* Lemma/definitions over types involved in the inference *)
  
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Hint Rewrite Bottom_proj Top_proj Unit_proj Nat_proj Float_proj Bool_proj String_proj : type_canon.
    
  (* An additional utility function for sortable types *)
  Definition tunrecsortable (sl:list string) (τ:rtype) : option rtype.
  Proof.
    case_eq (tunrec τ); intros.
    - destruct p; simpl in *.
      destruct (sublist_dec sl (domain l)).
      + destruct (order_by_has_sortable_type_dec l sl).
        * exact (Some τ).
        * exact None.
      + exact None. (* It is only well typed when sl is a sublist of domain l *)
    - exact None.
  Defined.

  (* destructer tactic *)
  Ltac destructer :=
    repeat progress
           (try
              match goal with
              | [H:context
                     [match ?p with
                      | exist _ _ _ => _
                      end] |- _] => destruct p
              | [H:context [match ?p with | _ => _ end] |- _ ] =>
                case_eq p; intros;
                repeat match goal with
                       | [H1: ?a = ?a |- _ ] => clear H1
                       | [H1: ?a = ?b |- _ ] => rewrite H1 in *
                       end
              | [H:Some _ = Some _ |- _ ] => inversion H; clear H
              | [H:ex _ |- _]  => destruct H
              | [H:_ /\ _ |- _]  => destruct H
              | [H:lift _ _ = Some _ |- _] => apply some_lift in H; destruct H
              | [H:lift _ _ = None |- _] => apply none_lift in H
                                                                 
              | [H:context [RecMaybe _ (rec_concat_sort _ _ )] |- _ ] => rewrite RecMaybe_rec_concat_sort in H
              | [H:RecMaybe _ _ = Some _ |- _ ] => apply RecMaybe_some_pf in H; destruct H
              | [H1:is_list_sorted StringOrder.lt_dec (domain ?l) = true,
                    H2:context[RecMaybe ?k ?l] |- _ ] =>
                rewrite (RecMaybe_pf_some _ _ H1) in H2
              | [H: tuncoll _ = _ |- _ ] => apply tuncoll_correct in H
              | [H: tsingleton _ = _ |- _ ] => apply tsingleton_correct in H
              | [H: tunrec _ = _ |- _ ] => apply tunrec_correct in H; destruct H

              | [H: ` _ = Bottom₀ |- _ ] => apply Bottom_canon in H
              | [H: ` _ = Brand₀ ?b |- _ ] => apply Brand_canon in H
              | [H: ` _ = Top₀ |- _ ] => apply Top_canon in H
              | [H: ` _ = Unit₀ |- _ ] => apply Unit_canon in H
              | [H: ` _ = Nat₀ |- _ ] => apply Nat_canon in H
              | [H: ` _ = Float₀ |- _ ] => apply Float_canon in H
              | [H: ` _ = Bool₀ |- _ ] => apply Bool_canon in H
              | [H: ` _ = String₀ |- _ ] => apply String_canon in H
              | [H: ` _ = Coll₀ ?A |- _] =>
                match A with
                |  String₀  => apply Coll_String_inside in H
                |  ` _  => apply Coll_canon in H
                | _ => destruct (Coll_inside _ _ H); subst; apply Coll_canon in H
                end
              | [H: ?a = ?a |- _ ] => clear H
              | [H: ?a = ?b |- _ ] => rewrite H in *
              | [H:binary_op_type _ _ _ _ |- _ ] => inversion H; clear H
              end; try autorewrite with type_canon in *; try unfold equiv, complement, rtype in *; simpl in *; try rtype_equalizer; try subst; try discriminate; try reflexivity).

  Section b.

    Context {fbop:foreign_binary_op}.
    Context {fboptyping:foreign_binary_op_typing}.

    Definition infer_binary_op_type (b:binary_op) (τ₁ τ₂:rtype) : option rtype :=
      match b with
      | OpEqual =>
        if (τ₁ == τ₂) then Some Bool else None
      | OpRecConcat => trecConcat τ₁ τ₂
      | OpRecMerge => lift Coll (tmergeConcat τ₁ τ₂)
      | OpAnd =>
        match (`τ₁, `τ₂) with
        | (Bool₀, Bool₀) => Some Bool
        | _ => None
        end
      | OpOr =>
        match (`τ₁, `τ₂) with
        | (Bool₀, Bool₀) => Some Bool
        | _ => None
        end
      | OpLt | OpLe =>
        match (`τ₁, `τ₂) with
        | (Nat₀, Nat₀) => Some Bool
        | (_, _) => None
        end
      | OpBagUnion | OpBagDiff | OpBagMin | OpBagMax =>
        match (tuncoll τ₁, tuncoll τ₂) with
        | (Some τ₁₀, Some τ₂₀) =>
          if (`τ₁₀ == `τ₂₀) then Some τ₁ else None
        | _ => None
        end
      | OpBagNth =>
        match (tuncoll τ₁, `τ₂) with
        | (Some τ₁₀, Nat₀) =>
          Some (Option τ₁₀)
        | _ => None
        end
      | OpContains =>
        match tuncoll τ₂ with
        | Some τ₂₀ =>
          if (`τ₁ == `τ₂₀) then Some Bool else None
        | None => None
        end
      | OpStringConcat =>
        match (`τ₁, `τ₂) with
        | (String₀, String₀) => Some String
        | (_, _) => None
        end
      | OpStringJoin =>
        match (`τ₁, `τ₂) with
        | (String₀, Coll₀ String₀) => Some String
        | (_, _) => None
        end
      | OpNatBinary _ =>
        match (`τ₁, `τ₂) with
        | (Nat₀, Nat₀) => Some Nat
        | _ => None
        end
      | OpFloatBinary _ =>
        match (`τ₁, `τ₂) with
        | (Float₀, Float₀) => Some Float
        | _ => None
        end
      | OpFloatCompare _ =>
        match (`τ₁, `τ₂) with
        | (Float₀, Float₀) => Some Bool
        | _ => None
        end
      | OpForeignBinary fb =>
        foreign_binary_op_typing_infer fb τ₁ τ₂
      end.

    Lemma infer_concat_trec {τ₁ τ₂ τout} :
      trecConcat τ₁ τ₂ = Some τout ->
      binary_op_type OpRecConcat τ₁ τ₂ τout.
    Proof.
      destruct τ₁ using rtype_rect; simpl; try discriminate.
      destruct τ₂ using rtype_rect; simpl; try discriminate.
      intros.
      destructer.
      econstructor; eauto.
    Qed.
    
    Lemma infer_merge_tmerge {τ₁ τ₂ τout} :
      tmergeConcat τ₁ τ₂ = Some τout ->
      binary_op_type OpRecMerge τ₁ τ₂ (Coll τout).
    Proof.
      destruct τ₁ using rtype_rect; simpl; try discriminate.
      destruct τ₂ using rtype_rect; simpl; try discriminate.
      intros.
      destructer;
        econstructor; eauto.
    Qed.

    Theorem infer_binary_op_type_correct (b:binary_op) (τ₁ τ₂ τout:rtype) :
      infer_binary_op_type b τ₁ τ₂ = Some τout ->
      binary_op_type b τ₁ τ₂ τout.
    Proof.
      Hint Constructors binary_op_type.
      Hint Resolve infer_concat_trec infer_merge_tmerge.
      binary_op_cases (case_eq b) Case; intros; simpl in *; destructer;
        try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity]; eauto 3.
      - constructor; apply foreign_binary_op_typing_infer_correct;
        apply H0.
    Qed.
  
    Theorem infer_binary_op_type_least {b:binary_op} {τ₁ τ₂:rtype} {τout₁ τout₂:rtype} :
      infer_binary_op_type b τ₁ τ₂ = Some τout₁ ->
      binary_op_type b τ₁ τ₂ τout₂ ->
      subtype τout₁ τout₂.
    Proof.
      intros binf btype.
      binary_op_cases (destruct b) Case; intros; simpl in *; destructer;
      try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - apply (foreign_binary_op_typing_infer_least binf H0). (* Handles foreign binary_op *)
    Qed.

    Theorem infer_binary_op_type_complete {b:binary_op} {τ₁ τ₂:rtype} (τout:rtype) :
      infer_binary_op_type b τ₁ τ₂ = None ->
      ~ binary_op_type b τ₁ τ₂ τout.
    Proof.
      intros binf btype.
      binary_op_cases (destruct b) Case; intros; simpl in *; try destructer;
      try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - Case "OpForeignBinary"%string.
        apply (foreign_binary_op_typing_infer_complete binf H0).
    Qed.

  End b.

(*  
  This would be nice to prove at some point.

  Require Import Morphisms.
  Require Import Basics.
    Global Instance binary_op_type_subtype_prop : Proper (eq ==> eq ==> eq ==> subtype ==> impl) binary_op_type.
    Proof.
      unfold Proper, respectful, impl, subtype; intros. subst.
      
      eapply unify_preserves_hastype; eauto.
    Qed.
  
   Theorem binary_op_type_dec  {b τ₁ τ₂ τout} : {binary_op_type b τ₁ τ₂ τout} + {~ binary_op_type b τ₁ τ₂ τout}.
    Proof.
      case_eq (infer_binary_op_type b τ₁ τ₂); [intros r eqr|intros neqr].
      - destruct (subtype_dec r τout).
        + left. apply infer_binary_op_type_correct in eqr.
          rewrite s in eqr. trivial.
        + right. intro dt. elim n. eapply infer_data_type_least; eauto.
      - right. intro dt. destruct (infer_data_type_complete dt). 
        congruence.
    Defined.
*)

  (** Type inference for unary operators *)

  Section u.
    Context {fuop:foreign_unary_op}.
    Context {fuoptyping:foreign_unary_op_typing}.
    
    Definition infer_unary_op_type (u:unary_op) (τ₁:rtype) : option rtype :=
      match u with
      | OpIdentity => Some τ₁
      | OpNeg =>
        match `τ₁ with
        | Bool₀ => Some Bool
        | _ => None
        end
      | OpRec s => Some (Rec Closed ((s, τ₁)::nil) eq_refl)
      | OpDot s => tunrecdot s τ₁
      | OpRecRemove s => tunrecremove s τ₁
      | OpRecProject sl => tunrecproject sl τ₁
      | OpBag => Some (Coll τ₁)
      | OpSingleton => tsingleton τ₁
      | OpFlatten =>
        match (tuncoll τ₁) with
        | Some τ₁₀ =>
          match tuncoll τ₁₀ with
          | Some _ => Some τ₁₀
          | _ => None
          end
        | None => None
        end
      | OpDistinct =>
        olift (fun x => Some (Coll x)) (tuncoll τ₁)
      | OpOrderBy sl =>
        match (tuncoll τ₁) with
        | Some τ₁₀ =>
          match tunrecsortable (List.map fst sl) τ₁₀ with
          | Some _ => Some τ₁
          | None => None
          end
        | None => None
        end
      | OpCount =>
        match `τ₁ with
        | Coll₀ _ => Some Nat
        | _ => None
        end
      | OpToString | OpToText => Some String
      | OpLength =>
        match `τ₁ with
        | String₀ => Some Nat
        | _ => None
        end
      | OpSubstring _ _ =>
        match `τ₁ with
        | String₀ => Some String
        | _ => None
        end
      | OpLike _ _ =>
        match `τ₁ with
        | String₀ => Some Bool
        | _ => None
        end
      | OpLeft =>
        Some (Either τ₁ ⊥)
      | OpRight =>
        Some (Either ⊥ τ₁)
      | OpBrand b =>
        if (rtype_eq_dec τ₁ (brands_type b)) (* Using equality is fine if subsumption is added to the language *)
        then Some (Brand b)
        else None
      | OpUnbrand =>
        match `τ₁ with
        | Brand₀ b => Some (brands_type b)
        | _ => None
        end
      | OpCast b =>
        match `τ₁ with
        | Brand₀ _ => Some (Option (Brand b))
        | _ => None
        end
      | OpNatUnary op =>
        match `τ₁ with
        | Nat₀ => Some Nat
        | _ => None
        end
      | OpNatSum
      | OpNatMin
      | OpNatMax
      | OpNatMean =>
        match `τ₁ with
        | Coll₀ Nat₀ => Some Nat
        | _ => None
        end
      | OpFloatOfNat =>
        match `τ₁ with
        | Nat₀ => Some Float
        | _ => None
        end
      | OpFloatUnary op =>
        match `τ₁ with
        | Float₀ => Some Float
        | _ => None
        end
      | OpFloatTruncate =>
        match `τ₁ with
        | Float₀ => Some Nat
        | _ => None
        end
      | OpFloatSum
      | OpFloatMean
      | OpFloatBagMin
      | OpFloatBagMax =>
        match `τ₁ with
        | Coll₀ Float₀ => Some Float
        | _ => None
        end
      | OpForeignUnary fu =>
        foreign_unary_op_typing_infer fu τ₁
      end.

    (** XXX TO GENERALIZE XXX *)
    Lemma empty_domain_remove {A} (l:list (string * A)) (s:string):
      domain l = nil -> domain (rremove l s) = nil.
    Proof.
      induction l; intros; [reflexivity|simpl in H; congruence].
    Qed.
  
    Lemma sorted_rremove_done {A} (l:list (string*A)) (a:(string*A)) (s:string) :
      is_list_sorted ODT_lt_dec (domain (a::l)) = true ->
      StringOrder.lt s (fst a) ->
      domain (rremove (a :: l) s) = domain (a :: l).
    Proof.
      intros.
      induction l.
      - simpl; destruct (string_dec s (fst a)); try congruence.
        subst.
        assert False by (apply (lt_contr3 (fst a) H0)); contradiction.
        reflexivity.
      - assert (is_list_sorted ODT_lt_dec (domain (a :: l)) = true)
          by (apply (rec_sorted_skip_second l a a0 H)).
        specialize (IHl H1); clear H1.
        simpl in *; destruct (string_dec s (fst a)).
        rewrite e in H0.
        assert False by (apply (lt_contr3 (fst a) H0)); contradiction.
        simpl in *.
        destruct (string_dec s (fst a0)).
        + assert (StringOrder.lt (fst a) (fst a0)).
          destruct (StringOrder.lt_dec (fst a) (fst a0)).
          assumption.
          rewrite e in H0.
          congruence.
          rewrite <- e in H1.
          assert False.
          apply asymmetry with (x := s) (y := (fst a)); assumption.
          contradiction.
        + simpl; inversion IHl; reflexivity.
    Qed.
    
    Lemma Forall_rremove {A} {a} {l:list (string * A)} :
      Forall (StringOrder.lt a) (domain l) ->
      forall s,
        Forall (StringOrder.lt a) (domain (rremove l s)).
    Proof.
      induction l; simpl; try constructor.
      inversion 1; subst; intros.
      destruct (string_dec s (fst a0)); try constructor; auto.
    Qed.

    Lemma is_sorted_rremove {A} (l:list (string * A)) (s:string):
      is_list_sorted ODT_lt_dec (domain l) = true ->
      is_list_sorted ODT_lt_dec (domain (rremove l s)) = true.
    Proof.
      Hint Resolve Forall_rremove.
      repeat rewrite sorted_StronglySorted by apply StringOrder.lt_strorder.
      induction l; simpl; try constructor.
      inversion 1; subst.
      destruct (string_dec s (fst a)); simpl; auto.
      constructor; auto.
    Qed.

    Lemma infer_dot_tunrec {s} {τ₁ τout} :
      tunrecdot s τ₁ = Some τout ->
      unary_op_type (OpDot s) τ₁ τout.
    Proof.
      unfold tunrecdot; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma infer_recremove_tunrec {s} {τ₁ τout} :
      tunrecremove s τ₁ = Some τout ->
      unary_op_type (OpRecRemove s) τ₁ τout.
    Proof.
      unfold tunrecremove; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma infer_recproject_tunrec {sl} {τ₁ τout} :
      tunrecproject sl τ₁ = Some τout ->
      unary_op_type (OpRecProject sl) τ₁ τout.
    Proof.
      unfold tunrecproject; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma infer_orderby_tunrec {sl} {τ₁ τout} :
      tunrecsortable (List.map fst sl) τ₁ = Some τout ->
      unary_op_type (OpOrderBy sl) (Coll τ₁) (Coll  τ₁).
    Proof.
      unfold tunrecsortable; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma infer_singleton_tsingleton {τ₁ τout} :
      tsingleton τ₁ = Some τout ->
      unary_op_type OpSingleton τ₁ τout.
    Proof.
      unfold tsingleton; intros.
      destructer.
      destruct x; try congruence.
      inversion H; simpl in *; clear H.
      destructer.
      assert ((exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ x) e) =
              Coll (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)).
      apply rtype_fequal.
      reflexivity.
      rewrite H.
      constructor; auto.
    Qed.

    Lemma infer_unary_op_type_correct (u:unary_op) (τ₁ τout:rtype) :
      infer_unary_op_type u τ₁ = Some τout ->
      unary_op_type u τ₁ τout.
    Proof.
      Hint Constructors unary_op_type.
      Hint Resolve infer_dot_tunrec infer_recremove_tunrec infer_recproject_tunrec
           infer_orderby_tunrec infer_singleton_tsingleton.
      unary_op_cases (case_eq u) Case; intros; simpl in *; destructer; unfold olift in *; try autorewrite with type_canon in *; destructer;
        try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity]; eauto 3.
      - constructor.
      - constructor; apply foreign_unary_op_typing_infer_correct;
        apply H0.
    Qed.

    Lemma infer_unary_op_type_least (u:unary_op) (τ₁ τout₁ τout₂:rtype) :
      infer_unary_op_type u τ₁ = Some τout₁ ->
      unary_op_type u τ₁ τout₂ ->
      subtype τout₁ τout₂.
    Proof.
      intros uinf utype.
      unary_op_cases (destruct u) Case; inversion utype; intros; simpl in *; destructer; unfold tunrecdot, tunrecremove, tunrecproject, tsingleton in *; destructer; try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - repeat econstructor. (* Handles subtype part of the proof for Left *)
      - repeat econstructor. (* Handles subtype part of the proof for Right *)
      - inversion H.         (* Handles subtype part of the proof for Unbrand *)
        subst.
        rewrite brands_type_of_canon.
        reflexivity.
      - apply (foreign_unary_op_typing_infer_least uinf H0). (* Handles foreign unary_op *)
    Qed.

    Lemma infer_unary_op_type_complete (u:unary_op) (τ₁ τout:rtype) :
      infer_unary_op_type u τ₁ = None ->
      ~ unary_op_type u τ₁ τout.
    Proof.
      intros uinf utype.
      unary_op_cases (destruct u) Case; inversion utype; intros; simpl in *; destructer; unfold tunrecdot, tunrecremove, tunrecproject, tunrecsortable, tsingleton in *; destructer; try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - Case "OpForeignUnary"%string.
        inversion utype.
        apply (foreign_unary_op_typing_infer_complete uinf H1).
    Qed.

  End u.
    
End TOperatorsInfer.

