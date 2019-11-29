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
Require Import Sorting.
Require Import Eqdep_dec.
Require Import Bool.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignType.
Require Import RType.

Section RTypeNorm.
  (** Syntax of types. Note that there is no guarantee yet that records are well formed. i.e., having distinct fields. *)

  Context {ftype:foreign_type}.
  Context {br:brand_relation}.

  Fixpoint normalize_rtype₀ (r:rtype₀) : rtype₀ :=
    match r with
    | Bottom₀ => Bottom₀
    | Top₀ => Top₀
    | Unit₀ => Unit₀
    | Nat₀ => Nat₀
    | Float₀ => Float₀
    | Bool₀ => Bool₀
    | String₀ => String₀
    | Coll₀ r' => Coll₀ (normalize_rtype₀ r')
    | Rec₀ k srl => Rec₀ k (rec_sort (map (fun sr => ((fst sr), (normalize_rtype₀ (snd sr)))) srl))
    | Either₀ tl tr => Either₀ (normalize_rtype₀ tl) (normalize_rtype₀ tr)
    | Arrow₀ tin tout => Arrow₀ (normalize_rtype₀ tin) (normalize_rtype₀ tout)
    | Brand₀ bl => Brand₀ (canon_brands brand_relation_brands bl)
    | Foreign₀ ft => Foreign₀ ft
    end.

  Lemma exists_normalized_in_rec_sort x r:
    In x
       (rec_sort
          (map
             (fun sr : string * rtype₀ =>
                (fst sr, normalize_rtype₀ (snd sr))) r)) ->
    exists y,
      (In y r /\
       snd x = (normalize_rtype₀ (snd y))).
  Proof.
    intros.
    induction r.
    - contradiction.
    - simpl in *.
      destruct a; simpl in *.
      assert (x = (s, normalize_rtype₀ r0) \/ In x (rec_sort
              (map
                 (fun sr : string * rtype₀ =>
                    (fst sr, normalize_rtype₀ (snd sr))) r))) by
          (apply in_rec_sort_insert; assumption).
      elim H0; clear H0; intros.
      + exists (s, r0).
        split; [left;reflexivity|].
        rewrite H0; reflexivity.
      + elim (IHr H0); intros.
        elim H1; clear H1; intros.
        exists x0.
        split; [right;assumption|assumption].
  Qed.
    
  Lemma normalize_rtype₀_wf (r:rtype₀) :
    wf_rtype₀ (normalize_rtype₀ r) = true.
  Proof.
    induction r; try reflexivity; simpl; try assumption.
    - apply andb_true_intro; split.
      + apply (@rec_sort_pf string ODT_string).
      + rewrite Forall_forall in H.
        rewrite forallb_forall; intros.
        elim (exists_normalized_in_rec_sort x r H0); intros.
        elim H1; clear H1; intros.
        rewrite H2.
        apply (H x0 H1).
    - apply andb_true_intro; split; assumption.
    - apply andb_true_intro; split; assumption.
    - destruct (is_canon_brands_dec brand_relation_brands
                                    (canon_brands brand_relation_brands b)).
      + reflexivity.
      + generalize (canon_brands_is_canon_brands brand_relation_brands b); intros.
        congruence.
  Qed.  

  Program Definition normalize_rtype₀_to_rtype (r₀:rtype₀) : rtype :=
    exist _ (normalize_rtype₀ r₀) _.
  Next Obligation.
    apply normalize_rtype₀_wf.
  Defined.
  
End RTypeNorm.

