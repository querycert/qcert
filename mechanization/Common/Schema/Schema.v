(*
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
Require Import Bool.
Require Import EquivDec.
Require Import Eqdep_dec.
Require Import Basics.
Require Import ListSet.
Require Import Program.Basics.
Require Import RelationClasses.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import ForeignData.
Require Import QResult.
Require Import Types.

Section Schema.
  Context {fdata:foreign_data}.

  Section brand_relation.
  
    Program Definition mk_brand_relation (br:list (string*string)) : qresult brand_relation :=
      if brand_relation_trans_dec br
      then
        if brand_relation_assym_dec br
        then
          qsuccess (mkBrand_relation br _ _)
        else
          qfailure (CompilationError "Brand relation is not assymetric")
      else
        qfailure (CompilationError "Brand relation is not transitive").
    Next Obligation.
      unfold holds, is_true; match_destr.
      congruence.
    Qed.
    Next Obligation.
      unfold holds, is_true; match_destr.
      congruence.
    Qed.
  End brand_relation.

  Section brand_model.
    Context {ftype:foreign_type}.

    Program Definition mk_brand_context (b:brand_relation) (bcds:brand_context_decls) :=
      mkBrand_context (rec_sort bcds) _.
    Next Obligation.
      specialize (rec_sort_sorted bcds (rec_sort bcds) eq_refl).
      eauto.
    Qed.
    
    Definition make_brand_model_from_decls_fails
               (b:brand_relation) (bcds:brand_context_decls) : qresult brand_model.
    Proof.
      generalize (mk_brand_context b bcds); intro m.
      generalize (make_brand_model b m); intros.
      destruct (is_true brand_model_domain_dec).
      - destruct (is_true brand_model_subtype_weak_dec).
        + specialize (H eq_refl).
          exact (qsuccess H).
        + exact (qfailure (CompilationError "Subtyping violation in brand model")).
      - exact (qfailure (CompilationError "Brand without a declared type in brand model")).
    Defined.

  End brand_model.

End Schema.
