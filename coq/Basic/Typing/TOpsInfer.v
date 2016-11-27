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

Section TOpsInfer.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import Program.
  Require Import Eqdep_dec.
  Require Import Bool.
  Require Import EquivDec.
  
  Require Import Utils Types BasicRuntime.
  Require Import ForeignDataTyping ForeignOpsTyping TData TOps TDataSort.

  (* Lemma/definitions over types involved in the inference *)
  
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Definition tuneither (τ:rtype) : option (rtype * rtype).
  Proof.
    destruct τ.
    destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - refine (Some ((exist _ x1 _),(exist _ x2 _))).
      + simpl in e; rewrite andb_true_iff in e; tauto.
      + simpl in e; rewrite andb_true_iff in e; tauto.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Definition tuncoll (τ:rtype) : option rtype.
  Proof.
    destruct τ.
    destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact (Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)). 
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Lemma tuncoll_correct (τ τ':rtype) :
    tuncoll τ = Some τ' ->
    τ = Coll τ'.
  Proof.
      destruct τ using rtype_rect; try discriminate.
      inversion 1; subst.
      reflexivity.
  Qed.

  Definition tsingleton (τ:rtype) : option rtype.
  Proof.
    destruct τ.
    destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact (Some (Option (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e))). 
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Lemma tsingleton_correct (τ τ':rtype) :
    tsingleton τ = Some (Option τ') ->
    τ = Coll τ'.
  Proof.
      destruct τ using rtype_rect; try discriminate.
      inversion 1; subst.
      rtype_equalizer; subst.
      reflexivity.
  Qed.

  Definition tunrec (τ: rtype) : option (record_kind * (list (string * rtype))).
  Proof.
    destruct τ; destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - generalize (from_Rec₀ srl e); intros.
      destruct H.
      exact (Some (k,x)).
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

   Lemma tunrec_correct k (τ:rtype) {l} :
    tunrec τ = Some (k,l) ->
    {pf | τ =  Rec k l pf}.
   Proof.
     destruct τ using rtype_rect; try discriminate.
     inversion 1; subst.
     match goal with
     | [H:context
            [match ?p with
             | _ => _
             end] |- _] => destruct p
     end.
     inversion H2; subst; clear H2.
     destruct e as [? [??]].
     rtype_equalizer; subst.
     eauto.
   Qed.

  Definition trecConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    destruct τ₁; destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - destruct τ₂; destruct x.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + generalize (from_Rec₀ srl e); intros.
        generalize (from_Rec₀ srl0 e0); intros.
        destruct H; destruct H0.
        destruct k; destruct k0; simpl.
        * exact None. (* Open record *)
        * exact None. (* Open record *)
        * exact None. (* Open record *)
        * generalize (rec_concat_sort x x0); intros.
          exact (RecMaybe Closed H).
      + exact None.
      + exact None.
      + exact None.
      + exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Definition tmergeConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    destruct τ₁; destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - destruct τ₂; destruct x.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + generalize (from_Rec₀ srl e); intros.
        generalize (from_Rec₀ srl0 e0); intros.
        destruct H; destruct H0.
        generalize (merge_bindings x x0); intros.
        destruct H as [rSome|rNone].
        destruct k; destruct k0; simpl in *.
        * exact (RecMaybe Open rSome).
        * exact None.
        * exact None.
        * exact (RecMaybe Closed rSome).
        * exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
    - exact None. 
    - exact None. 
    - exact None. 
    - exact None. 
  Defined.

  Definition tunrecdot (s:string) (τ:rtype) : option rtype.
  Proof.
    generalize (tunrec τ); intros.
    case_eq H; intros.
    - destruct p; simpl in *.
      exact (tdot l s).
    - exact None.
  Defined.

  Definition tunrecremove (s:string) (τ:rtype) : option rtype.
  Proof.
    generalize (tunrec τ); intros.
    case_eq H; intros.
    - destruct p; simpl in *.
      exact (RecMaybe r (rremove l s)).
    - exact None.
  Defined.

  Definition tunrecproject (sl:list string) (τ:rtype) : option rtype.
  Proof.
    generalize (tunrec τ); intros.
    case_eq H; intros.
    - destruct p; simpl in *.
      destruct (sublist_dec sl (domain l)).
      + exact (RecMaybe Closed (rproject l sl)). (* This is always a closed record *)
      + exact None. (* It is only well typed when sl is a sublist of domain l *)
    - exact None.
  Defined.

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

  (* Type inference for binary operators *)
  
  Definition recConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    generalize (tunrec τ₁); intros.
    case_eq H; intros.
    - generalize (tunrec τ₂); intros.
      case_eq H1; intros.
      destruct p; destruct p0; simpl in *.
      + generalize (rec_concat_sort l l0); intros.
        destruct r; destruct r0; simpl in *.
        * exact None.
        * exact None.
        * exact None.
        * exact (RecMaybe Closed H3).
      + exact None.
    - exact None.
  Defined.
  
  Definition mergeConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    generalize (tunrec τ₁); generalize (tunrec τ₂); intros.
    case_eq H; case_eq H0; intros.
    destruct p; destruct p0; simpl in *.
    generalize (merge_bindings l l0); intros.
    - destruct H3 as [rSome|rNone].
      destruct r; destruct r0; simpl in *.
      * exact (RecMaybe Open rSome).
      * exact None.
      * exact None.
      * exact (RecMaybe Closed rSome).
      * exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Lemma RecMaybe_rec_concat_sort k l1 l2 :
    RecMaybe k (rec_concat_sort l1 l2) = Some (Rec k (rec_concat_sort l1 l2) (drec_concat_sort_sorted l1 l2)).
  Proof.
    apply (RecMaybe_pf_some _).
  Qed.

  Lemma Bottom_proj : Bottom₀ = ` Bottom.
  Proof.
    reflexivity.
  Qed.

  Lemma Top_proj : Top₀ = ` Top.
  Proof.
    reflexivity.
  Qed.

  Lemma Unit_proj : Unit₀ = ` Unit.
  Proof.
    reflexivity.
  Qed.

  Lemma Nat_proj : Nat₀ = ` Nat.
  Proof.
    reflexivity.
  Qed.

  Lemma Bool_proj : Bool₀ = ` Bool.
  Proof.
    reflexivity.
  Qed.

  Lemma String_proj : String₀ = ` String.
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite Bottom_proj Top_proj Unit_proj Nat_proj Bool_proj String_proj : type_canon.
    
  Lemma Brand_canon {b} {τ₁:rtype} :` τ₁ = Brand₀ b -> τ₁ = Brand b.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply brand_ext.
  Qed.

  Lemma Bottom_canon {τ₁:rtype} :` τ₁ = Bottom₀ -> τ₁ = Bottom.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Top_canon {τ₁:rtype} :` τ₁ = Top₀ -> τ₁ = Top.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Unit_canon {τ₁:rtype} :` τ₁ = Unit₀ -> τ₁ = Unit.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Nat_canon {τ₁:rtype} :` τ₁ = Nat₀ -> τ₁ = Nat.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Bool_canon {τ₁:rtype} :` τ₁ = Bool₀ -> τ₁ = Bool.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma String_canon {τ₁:rtype} :` τ₁ = String₀ -> τ₁ = String.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Coll_canon {τ₁ τ₀:rtype} :` τ₁ = Coll₀ (` τ₀) -> τ₁ = Coll τ₀.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

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
              | [H: ` _ = Bool₀ |- _ ] => apply Bool_canon in H
              | [H: ` _ = String₀ |- _ ] => apply String_canon in H
              | [H: ` _ = Coll₀ ?A |- _] =>
                match A with
                |  ` _  => apply Coll_canon in H
                | _ => destruct (Coll_inside _ _ H); subst; apply Coll_canon in H
                end
                  
              | [H: ?a = ?a |- _ ] => clear H
              | [H: ?a = ?b |- _ ] => rewrite H in *
              | [H:binOp_type _ _ _ _ |- _ ] => inversion H; clear H
              end; try autorewrite with type_canon in *; try unfold equiv, complement, rtype in *; simpl in *; try rtype_equalizer; try subst; try discriminate; try reflexivity).

  Section b.

    Context {fbop:foreign_binary_op}.
    Context {fboptyping:foreign_binary_op_typing}.

    Definition infer_binop_type (b:binOp) (τ₁ τ₂:rtype) : option rtype :=
      match b with
      | AEq =>
        if (τ₁ == τ₂) then Some Bool else None
      | AConcat => trecConcat τ₁ τ₂
      | AMergeConcat => lift Coll (tmergeConcat τ₁ τ₂)
      | AAnd =>
        match (`τ₁, `τ₂) with
        | (Bool₀, Bool₀) => Some Bool
        | _ => None
        end
      | AOr =>
        match (`τ₁, `τ₂) with
        | (Bool₀, Bool₀) => Some Bool
        | _ => None
        end
      | ABArith _ =>
        match (`τ₁, `τ₂) with
        | (Nat₀, Nat₀) => Some Nat
        | _ => None
        end
      | ALt | ALe =>
        match (`τ₁, `τ₂) with
        | (Nat₀, Nat₀) => Some Bool
        | (_, _) => None
        end
      | AUnion | AMinus | AMin | AMax =>
        match (tuncoll τ₁, tuncoll τ₂) with
        | (Some τ₁₀, Some τ₂₀) =>
          if (`τ₁₀ == `τ₂₀) then Some τ₁ else None
        | _ => None
        end
      | AContains =>
        match tuncoll τ₂ with
        | Some τ₂₀ =>
          if (`τ₁ == `τ₂₀) then Some Bool else None
        | None => None
        end
      | ASConcat =>
        match (`τ₁, `τ₂) with
        | (String₀, String₀) => Some String
        | (_, _) => None
        end
      | AForeignBinaryOp fb =>
        foreign_binary_op_typing_infer fb τ₁ τ₂
      end.

    Lemma ATConcat_trec {τ₁ τ₂ τout} :
      trecConcat τ₁ τ₂ = Some τout ->
      binOp_type AConcat τ₁ τ₂ τout.
    Proof.
      destruct τ₁ using rtype_rect; simpl; try discriminate.
      destruct τ₂ using rtype_rect; simpl; try discriminate.
      intros.
      destructer.
      econstructor; eauto.
    Qed.
    
    Lemma ATMergeConcat_tmerge {τ₁ τ₂ τout} :
      tmergeConcat τ₁ τ₂ = Some τout ->
      binOp_type AMergeConcat τ₁ τ₂ (Coll τout).
    Proof.
      destruct τ₁ using rtype_rect; simpl; try discriminate.
      destruct τ₂ using rtype_rect; simpl; try discriminate.
      intros.
      destructer;
        econstructor; eauto.
    Qed.

    Theorem infer_binop_type_correct (b:binOp) (τ₁ τ₂ τout:rtype) :
      infer_binop_type b τ₁ τ₂ = Some τout ->
      binOp_type b τ₁ τ₂ τout.
    Proof.
      Hint Constructors binOp_type.
      Hint Resolve ATConcat_trec ATMergeConcat_tmerge.
      binOp_cases (case_eq b) Case; intros; simpl in *; destructer;
      try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity]; eauto 3.
      - constructor; apply foreign_binary_op_typing_infer_correct;
        apply H0.
    Qed.
  
    Theorem infer_binop_type_least {b:binOp} {τ₁ τ₂:rtype} {τout₁ τout₂:rtype} :
      infer_binop_type b τ₁ τ₂ = Some τout₁ ->
      binOp_type b τ₁ τ₂ τout₂ ->
      subtype τout₁ τout₂.
    Proof.
      intros binf btype.
      binOp_cases (destruct b) Case; intros; simpl in *; destructer;
      try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - apply (foreign_binary_op_typing_infer_least binf H0). (* Handles foreign binop *)
    Qed.

    Theorem infer_binop_type_complete {b:binOp} {τ₁ τ₂:rtype} (τout:rtype) :
      infer_binop_type b τ₁ τ₂ = None ->
      ~ binOp_type b τ₁ τ₂ τout.
    Proof.
      intros binf btype.
      binOp_cases (destruct b) Case; intros; simpl in *; try destructer;
      try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - Case "AForeignBinaryOp"%string.
        apply (foreign_binary_op_typing_infer_complete binf H0).
    Qed.

  End b.

(*  
  This would be nice to prove at some point.

  Require Import Morphisms.
  Require Import Basics.
    Global Instance binOp_type_subtype_prop : Proper (eq ==> eq ==> eq ==> subtype ==> impl) binOp_type.
    Proof.
      unfold Proper, respectful, impl, subtype; intros. subst.
      
      eapply unify_preserves_hastype; eauto.
    Qed.
  
   Theorem binop_type_dec  {b τ₁ τ₂ τout} : {binOp_type b τ₁ τ₂ τout} + {~ binOp_type b τ₁ τ₂ τout}.
    Proof.
      case_eq (infer_binop_type b τ₁ τ₂); [intros r eqr|intros neqr].
      - destruct (subtype_dec r τout).
        + left. apply infer_binop_type_correct in eqr.
          rewrite s in eqr. trivial.
        + right. intro dt. elim n. eapply infer_data_type_least; eauto.
      - right. intro dt. destruct (infer_data_type_complete dt). 
        congruence.
    Defined.
*)
  (* Type inference for unary operators *)

  Section u.
    Context {fuop:foreign_unary_op}.
    Context {fuoptyping:foreign_unary_op_typing}.
    
    Definition infer_unop_type (u:unaryOp) (τ₁:rtype) : option rtype :=
      match u with
      | AIdOp => Some τ₁
      | ANeg =>
        match `τ₁ with
        | Bool₀ => Some Bool
        | _ => None
        end
      | AColl => Some (Coll τ₁)
      | ASingleton => tsingleton τ₁
      | AFlatten =>
        match (tuncoll τ₁) with
        | Some τ₁₀ =>
          match tuncoll τ₁₀ with
          | Some _ => Some τ₁₀
          | _ => None
          end
        | None => None
        end
      | ADistinct =>
        olift (fun x => Some (Coll x)) (tuncoll τ₁)
      | AOrderBy sl =>
        match (tuncoll τ₁) with
        | Some τ₁₀ =>
          match tunrecsortable (List.map fst sl) τ₁₀ with
          | Some _ => Some τ₁
          | None => None
          end
        | None => None
        end
      | ARec s => Some (Rec Closed ((s, τ₁)::nil) eq_refl)
      | ADot s => tunrecdot s τ₁
      | ARecRemove s => tunrecremove s τ₁
      | ARecProject sl => tunrecproject sl τ₁
      | ACount =>
        match `τ₁ with
        | Coll₀ _ => Some Nat
        | _ => None
        end
      | ASum
      | ANumMin
      | ANumMax
      | AArithMean =>
        match `τ₁ with
        | Coll₀ Nat₀ => Some Nat
        | _ => None
        end
      | AToString => Some String
      | ASubstring _ _ =>
        match `τ₁ with
        | String₀ => Some String
        | _ => None
        end
      | ALike _ _ =>
        match `τ₁ with
        | String₀ => Some Bool
        | _ => None
        end
      | ALeft =>
        Some (Either τ₁ ⊥)
      | ARight =>
        Some (Either ⊥ τ₁)
      | ABrand b =>
        if (rtype_eq_dec τ₁ (brands_type b)) (* Using equality is fine if subsumption is added to the language *)
        then Some (Brand b)
        else None
      | AUnbrand =>
        match `τ₁ with
        | Brand₀ b => Some (brands_type b)
        | _ => None
        end
      | ACast b =>
        match `τ₁ with
        | Brand₀ _ => Some (Option (Brand b))
        | _ => None
        end
      | AUArith op =>
        match `τ₁ with
        | Nat₀ => Some Nat
        | _ => None
        end
      | AForeignUnaryOp fu =>
        foreign_unary_op_typing_infer fu τ₁
      end.

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

    Lemma ATDot_tunrec {s} {τ₁ τout} :
      tunrecdot s τ₁ = Some τout ->
      unaryOp_type (ADot s) τ₁ τout.
    Proof.
      unfold tunrecdot; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma ATRecRemove_tunrec {s} {τ₁ τout} :
      tunrecremove s τ₁ = Some τout ->
      unaryOp_type (ARecRemove s) τ₁ τout.
    Proof.
      unfold tunrecremove; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma ATRecProject_tunrec {sl} {τ₁ τout} :
      tunrecproject sl τ₁ = Some τout ->
      unaryOp_type (ARecProject sl) τ₁ τout.
    Proof.
      unfold tunrecproject; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma ATOrderBy_tunrec {sl} {τ₁ τout} :
      tunrecsortable (List.map fst sl) τ₁ = Some τout ->
      unaryOp_type (AOrderBy sl) (Coll τ₁) (Coll  τ₁).
    Proof.
      unfold tunrecsortable; intros.
      destructer.
      constructor; auto.
    Qed.

    Lemma ATSingleton_tsingleton {τ₁ τout} :
      tsingleton τ₁ = Some τout ->
      unaryOp_type ASingleton τ₁ τout.
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

    Lemma infer_unop_type_correct (u:unaryOp) (τ₁ τout:rtype) :
      infer_unop_type u τ₁ = Some τout ->
      unaryOp_type u τ₁ τout.
    Proof.
      Hint Constructors unaryOp_type.
      Hint Resolve ATDot_tunrec ATRecRemove_tunrec ATRecProject_tunrec
           ATOrderBy_tunrec ATSingleton_tsingleton.
      unaryOp_cases (case_eq u) Case; intros; simpl in *; destructer; unfold olift in *; try autorewrite with type_canon in *; destructer;
        try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity]; eauto 3.
      - constructor.
      - constructor; apply foreign_unary_op_typing_infer_correct;
        apply H0.
    Qed.

    Lemma infer_unop_type_least (u:unaryOp) (τ₁ τout₁ τout₂:rtype) :
      infer_unop_type u τ₁ = Some τout₁ ->
      unaryOp_type u τ₁ τout₂ ->
      subtype τout₁ τout₂.
    Proof.
      intros uinf utype.
      unaryOp_cases (destruct u) Case; inversion utype; intros; simpl in *; destructer; unfold tunrecdot, tunrecremove, tunrecproject, tsingleton in *; destructer; try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - repeat econstructor. (* Handles subtype part of the proof for Left *)
      - repeat econstructor. (* Handles subtype part of the proof for Right *)
      - inversion H.         (* Handles subtype part of the proof for Unbrand *)
        subst.
        rewrite brands_type_of_canon.
        reflexivity.
      - apply (foreign_unary_op_typing_infer_least uinf H0). (* Handles foreign unop *)
    Qed.

    Lemma infer_unop_type_complete (u:unaryOp) (τ₁ τout:rtype) :
      infer_unop_type u τ₁ = None ->
      ~ unaryOp_type u τ₁ τout.
    Proof.
      intros uinf utype.
      unaryOp_cases (destruct u) Case; inversion utype; intros; simpl in *; destructer; unfold tunrecdot, tunrecremove, tunrecproject, tunrecsortable, tsingleton in *; destructer; try congruence; try solve[ erewrite Rec_pr_irrel; reflexivity ].
      - Case "AForeignUnaryOp"%string.
        inversion utype.
        apply (foreign_unary_op_typing_infer_complete uinf H1).
    Qed.
    
  End u.
    
End TOpsInfer.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
