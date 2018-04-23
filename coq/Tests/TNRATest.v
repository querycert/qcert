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

Require Import List.
Require Import String.

Require Import Utils.
Require Import CommonSystem.
Require Import NRASystem.

Require Import NRATest.

Require Import TrivialModel.

Section TNRATest.
  Local Open Scope string_scope.
  Local Open Scope nraext_scope.

  (**************
   * Input data *
   **************)
  (* Empty inheritance *)
  Definition myBR : brand_relation
    := mkBrand_relation nil (eq_refl _) (eq_refl _) .

  Definition myBC : brand_context
    := @mkBrand_context trivial_foreign_type myBR nil (eq_refl _).
  
  Instance myM : brand_model
    := mkBrand_model myBR myBC (eq_refl _) (eq_refl _).

  (* Person schema *)

  Definition person_rec_schema :=
    rec_sort (("name",String) :: ("age",Nat) :: ("zip",Nat) :: ("company",String) :: nil).
  Lemma person_rec_schema_pf :
    is_list_sorted ODT_lt_dec (domain person_rec_schema) = true.
  Proof. reflexivity. Qed.
  Definition person_schema :=
    Rec Closed person_rec_schema person_rec_schema_pf.

  Definition persons_schema :=
    Coll person_schema.
  
  (* Person table *)
  Lemma mkperson_typed name age zip company:
    (normalize_data brand_relation_brands (mkperson name age zip company)) ▹ person_schema.
  Proof.
    apply dtrec_full.
    apply Forall2_cons; simpl.
    split; [reflexivity|constructor].
    apply Forall2_cons; simpl.
    split; [reflexivity|constructor].
    apply Forall2_cons; simpl.
    split; [reflexivity|constructor].
    apply Forall2_cons; simpl.
    split; [reflexivity|constructor].
    apply Forall2_nil; simpl.
  Qed.

  Lemma mkpersons_typed l:
    normalize_data brand_relation_brands (mkpersons l) ▹ persons_schema.
  Proof.
    apply dtcoll.
    rewrite Forall_forall; intros.
    induction l; simpl in H.
    - contradiction.
    - elim H; intros; clear H.
      destruct a; destruct p; destruct p.
      rewrite <- H0. apply (mkperson_typed s0 z0 z s).
      apply (IHl H0).
  Qed.
    
  Lemma persons_typed:
    normalize_data brand_relation_brands persons ▹ persons_schema.
  Proof.
    apply mkpersons_typed.
  Qed.

  Lemma qpersons_typed {τin} :
    qpersons ▷ τin >=> persons_schema ⊣ nil.
  Proof.
    unfold qpersons.
    apply @type_NRAConst.
    apply persons_typed.
  Qed.

  (* Eval compute in persons. *)

  (* Company table *)

  (* Nothing *)

  Definition nothing_schema := Unit.

  Lemma nothing_typed :
    nothing ▹ nothing_schema.
  Proof.
    apply dtunit.
  Qed.

  (* count *)

  Lemma q0_wt {τin} :
    q0 ▷ (Coll τin) >=> Nat ⊣ nil.
  Proof.
    unfold q0.
    apply (@type_NRAUnop _ nil (Coll τin) (Coll τin) Nat).
    apply type_OpCount.
    apply type_NRAID.
  Qed.

  Definition q0t {τin} (d:data) (bpf: bindings_type nil nil) (pf: d ▹ (Coll τin)) : data :=
    (q0 @▷ d ⊣ nil) bpf
                   pf q0_wt.

  (* Eval compute in q0@persons.                  (* untyped *) *)
  (* Eval compute in (q0t (normalize_data persons) persons_typed). (* typed *) *)

  (* Eval compute in (q0_wt ⊨ 𝓐(q0)). (* checks the 'record domain' of q0 is empty *) *)

  (* simple maps *)

  Lemma q1_wt {τin} :
    q1 ▷ τin >=> persons_schema ⊣ nil.
  Proof.
    unfold q1.
    apply (@type_NRAMap _ nil τin person_schema person_schema).
    apply @type_NRAID.
    apply qpersons_typed.
  Qed.

  Definition q1t (d:data) (bpf: bindings_type nil nil) : data :=
    (q1 @▷ nothing ⊣ nil) bpf nothing_typed q1_wt.

  (* Eval compute in q1@persons.                  (* untyped *) *)
  (* Eval compute in (q1t nothing nothing_typed). (* typed *) *)

  (* Eval compute in (q1_wt ⊨ 𝓐(q1)). (* computes the 'record domain' of q1 *) *)
  
  Lemma q2_wt {τin} :
    q2 ▷ τin >=> (Coll Nat) ⊣ nil.
  Proof.
    unfold q2.
    apply (@type_NRAMap _ nil τin person_schema Nat).
    - apply (@type_NRAUnop trivial_basic_model nil person_schema person_schema Nat).
      apply (@type_OpDot _ _ _ _ _ _ person_rec_schema Nat) with (pf:= person_rec_schema_pf); try reflexivity.
      apply @type_NRAID.
    - apply qpersons_typed.
  Qed.

  (* Print q2. *)

  Definition q2t {τin} (d:data) (bpf: bindings_type nil nil) (pf: d ▹ τin) : data :=
    (q2 @▷ d ⊣ nil) bpf pf q2_wt.

  (* Eval compute in q2@nothing.                  (* untyped *) *)
  (* Eval compute in (q2t nothing nothing_typed). (* typed *) *)

  (* Eval compute in (q2_wt ⊨ 𝓐(q2)). (* checks the 'record domain' of q2 is empty *) *)

  (* simple select *)

  Lemma q3_wt {τin} :
    q3 ▷ τin >=> persons_schema ⊣ nil.
  Proof.
    unfold q3.
    apply @type_NRASelect.
    apply type_NRAConst.
    apply dtbool.
    apply qpersons_typed.
  Qed.
  
  Definition q3t {τin} (d:data) (bpf: bindings_type nil nil) (pf: d ▹ τin) : data :=
    (q3 @▷ d ⊣ nil) bpf pf q3_wt.

  (* Print q3. *)

  (* Eval compute in q3@nothing.                  (* untyped *) *)
  (* Eval compute in (q3t nothing nothing_typed). (* typed *) *)

  (* Eval compute in (q3_wt ⊨ 𝓐(q3)). (* computes the 'record domain' of q3 *) *)

  Lemma q4_wt {τin} :
    q4 ▷ τin >=> persons_schema ⊣ nil.
  Proof.
    unfold q4.
    apply @type_NRASelect.
    - apply (@type_NRABinop trivial_basic_model nil person_schema Nat Nat Bool).
      + apply type_OpEqual.
      + apply (@type_NRAUnop trivial_basic_model nil person_schema person_schema Nat).
        apply (@type_OpDot _ _ _ _ _ _ person_rec_schema Nat) with (pf:= person_rec_schema_pf); try reflexivity.
        apply type_NRAID.
      + apply type_NRAConst.
        apply dtnat.
    - apply qpersons_typed.
  Qed.
  
  Definition q4t {τin} (d:data) (bpf: bindings_type nil nil) (pf: d ▹ τin) : data :=
    (q4 @▷ d ⊣ nil) bpf pf q4_wt.

  (* Print q4. *)
  (* Eval compute in q4@nothing.                  (* untyped *) *)
  (* Eval compute in (q4t nothing nothing_typed). (* typed *) *)

  (* Eval compute in (q4_wt ⊨ 𝓐(q4)). (* computes the 'record domain' of q4 *) *)

End TNRATest.

