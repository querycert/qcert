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

Section TUtil.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import Program.
  Require Import Eqdep_dec.
  Require Import Bool.
  Require Import EquivDec.
  
  Require Import Utils Types BasicRuntime.

  (* Lemma/definitions over types involved in the inference *)
  
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.

  (* Useful function *)

  Definition tdot {A} (l:list (string * A)) (a:string) : option A := edot l a.

  (* Type deconstructors *)
  
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
        destruct H as [rSome|].
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
    - destruct H3 as [rSome|].
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

End TUtil.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
