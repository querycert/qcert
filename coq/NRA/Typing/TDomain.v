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

Section TDomain.
  (* Record fields and record domain manipulation *)

  Require Import String.
  Require Import List.

  Require Import Utils BasicSystem.

  Require Import RAlg.
  Require Import TAlg.

  Context {ftype:foreign_type}.

  Definition tdomain (l:list (string * rtype₀)) : list string
    := map fst l.

  Definition tprojecto (l:list (string * rtype₀)) (ats:list string) : list (option (string * rtype₀)) :=
    projectr string_dec l ats.

  Fixpoint tprojectaux (l:list (option (string * rtype₀))) :=
    match l with
      | nil => nil
      | None :: r => tprojectaux r
      | (Some x) :: r => x :: (tprojectaux r)
    end.

  Definition tproject (l:list (string * rtype₀)) (ats:list string) :=
    tprojectaux (tprojecto l ats).

  Lemma lookup_in_domain l (a:string) :
    In a (tdomain l) -> (exists y, assoc_lookupr string_dec l a = Some y).
  Proof.
    induction l; simpl; intros.
    contradiction.
    simpl in H; elim H; intros; clear H.
    revert IHl.
    revert H0; destruct a0; intros.
    simpl in H0; rewrite H0 in *; clear H0.
    elim (string_dec a a); intros; try congruence.
    case (assoc_lookupr string_dec l a).
    intros; exists r0.
    reflexivity.
    exists r.
    reflexivity.
    elim (IHl H0); intros.
    rewrite H.
    exists x.
    destruct a0; reflexivity.
  Qed.

  Lemma lookup_in_included_domain ats l (a:string) :
    domains_included ats (tdomain l) -> In a ats -> (exists y, assoc_lookupr string_dec l a = Some y).
  Proof.
    intros.
    induction ats.
    simpl in H0.
    contradiction.
    assert (domains_included_alt (a0 :: ats) (tdomain l)); try (apply domains_included_eq; assumption).
    unfold domains_included_alt in H1, H0; simpl in H1, H0.
    elim H0; intros; clear H0.
    rewrite H2 in *; clear H2.
    assert (In a (tdomain l)).
    apply (H1 a); left; reflexivity.
    apply (lookup_in_domain l a); assumption.
    assert (domains_included ats (tdomain l)).
    apply domains_included_cons with (a := a0); assumption.
    apply (IHats H0 H2).
  Qed.

  Lemma preserves_tdomain (l:list (string * rtype₀)) (ats:list string) :
    domains_included ats (tdomain l) -> (tdomain (tproject l ats)) = ats.
  Proof.
    intros.
    induction ats; intros; simpl; try reflexivity.
    assert (domains_included_alt (a :: ats) (tdomain l)); try (apply domains_included_eq; assumption).
    unfold tproject, tprojecto.
    simpl.
    cut (exists y, assoc_lookupr string_dec l a = Some y).
    intros; elim H1; intros.
    rewrite H2. simpl.
    assert (domains_included ats (tdomain l)).
    apply domains_included_cons with (a := a); assumption.
    unfold tproject,tprojecto in IHats.
    rewrite (IHats H3).
    reflexivity.
    apply lookup_in_included_domain with (ats := a::ats).
    assumption.
    simpl; left; reflexivity.
  Qed.

End TDomain.

Section dom.
  Require Import TBrandModel.
  Lemma alg_domain {m:basic_model} {τin τout} (op:alg) :
    op ▷ τin >=> τout -> list string.
  Proof.
    intros.
    destruct τout.
    destruct x.
    - exact nil.    (* ⊥ *)
    - exact nil.    (* ⊤ *)
    - exact nil.    (* Unit *)
    - exact nil.    (* Nat *)
    - exact nil.    (* Bool *)
    - exact nil.    (* String *)
    - destruct x.   (* Coll *)
      + exact nil.    (* Coll ⊥ *)
      + exact nil.    (* Coll ⊤ *)
      + exact nil.    (* Coll Unit *)
      + exact nil.    (* Coll Nat *)
      + exact nil.    (* Coll Bool *)
      + exact nil.    (* Coll String *)
      + exact nil.    (* Coll (Coll ...) *)
      + exact (tdomain srl). (* Coll (Rec ...) *)
      + exact nil.
      + exact nil.
      + exact nil.
      + exact nil.
    - exact (tdomain srl). (* Rec ... *)
    - exact nil.
    - exact nil.
    - exact nil.
    - exact nil.
  Defined.

End dom.

Notation "d1 # d2" := (domains_disjoint d1 d2) (at level 70) : alg_scope.
Notation "x ∈ d"   := (in_domain d x)  (at level 70) : alg_scope.          (* ∈ = \in *)
Notation "x ∉ d"   := (not_in_domain d x)  (at level 70) : alg_scope.      (* ∉ = \notin *)
Notation "d1 ⊆ d2" := (domains_included d1 d2) (at level 70) : alg_scope.  (* ⊆ = \subseteq *)

Notation "pf ⊨ 𝓐( op )" := (alg_domain op pf) (at level 70) : alg_scope.  (* ⊨ = \vDash and 𝓐 = Unicode 1D4D0 *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
