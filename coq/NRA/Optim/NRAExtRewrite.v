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
Require Import CommonRuntime.
Require Import NRA.
Require Import NRAEq.
Require Import NRAExt.
Require Import NRAExtEq.
Require Import NRARewrite.

Section NRAExtRewrite.
  Local Open Scope nra_scope.
  Local Open Scope nraext_scope.

  Context {fruntime:foreign_runtime}.

  (* Equivalences for the algebra operators are based on equivalence for
     all input x *)

  (* An attempt at proving some of the relational algebra's algebraic
     equivalences. *)

  (* Pulls equivalences from core algebra *)

  Lemma pull_nra_opt (p1 p2:nraext) :
    (nra_of_nraext p1) ≡ₐ (nra_of_nraext p2) ->
    p1 ≡ₓ p2.
  Proof.
    unfold nra_eq, nraext_eq; intros.
    unfold nraext_eval.
    rewrite H; trivial.
  Qed.

  (* P1 ∧ P2 == P2 ∧ P1 *)

  Lemma eand_comm (p1 p2: nraext) :
    p2 ∧ p1 ≡ₓ p1 ∧ p2.
  Proof.
    apply pull_nra_opt.
    apply and_comm.
  Qed.

  (* (P1 ⋃ P2) ⋃ P3 == P1 ⋃ (P2 ⋃ P3) *)

  Lemma eunion_assoc (p1 p2 p3: nraext):
    (p1 ⋃ p2) ⋃ p3 ≡ₓ p1 ⋃ (p2 ⋃ p3).
  Proof.
    apply pull_nra_opt.
    apply union_assoc.
  Qed.
  
  (* σ⟨ P ⟩(P1 ⋃ P2) == σ⟨ P ⟩(P1) ⋃ σ⟨ P ⟩(P2) *)

  Lemma eunion_select_distr (p p1 p2: nraext) :
    σ⟨ p ⟩(p1 ⋃ p2) ≡ₓ σ⟨ p ⟩(p1) ⋃ σ⟨ p ⟩(p2).
  Proof.
    apply pull_nra_opt.
    apply union_select_distr.
  Qed.

  (* χ⟨ P1 ⟩( { P2 } ) ≡ { P1 ◯ P2 } *)

  Lemma emap_singleton (p1 p2:nraext) :
    χ⟨ p1 ⟩( ‵{| p2 |} ) ≡ₓ ‵{| p1 ◯ p2 |}.
  Proof.  
    apply pull_nra_opt.
    apply map_singleton.
  Qed.

  (* [ a : ID ] ◯ P ≡ [ a : P ] *)

  Lemma ecompose_rec_id s p:
    ‵[| (s, ID) |] ◯ p ≡ₓ ‵[| (s, p) |].
  Proof.
    apply pull_nra_opt.
    apply compose_rec_id.
  Qed.

  Lemma eflatten_map_coll p1 p2 :
    ♯flatten(χ⟨ ‵{| p1 |} ⟩( p2 )) ≡ₓ χ⟨ p1 ⟩( p2 ).
  Proof.
    apply pull_nra_opt.
    apply flatten_map_coll.
  Qed.

  (* Specific to extended nraebra *)
  
  (*
     a1, a2, a3 are distinct field names
     ===================================================================
     μ[s1][s2]( { [ s3 : P1; s1 : { P2 } ] } ) ≡ₓ { [ s3 : P1; s2 : P2 ] }
   *)

  Lemma eunnest_singleton s1 s2 s3 p1 p2 :
    s1 <> s2 /\ s2 <> s3 /\ s3 <> s1 ->
    μ[s1 ][ s2 ]( ‵{|‵[| (s3, p1)|] ⊕ ‵[| (s1, ‵{|p2|})|]|})
     ≡ₓ ‵{|‵[| (s3, p1)|] ⊕ ‵[| (s2, p2)|]|}.
  Proof.
    intros.
    apply pull_nra_opt.
    apply unnest_singleton; assumption.
  Qed.

  (* χ⟨ { ID } ⟩( P ) ≡ { { P } }*)
  
  Lemma emap_into_singleton p :
    χ⟨ ‵{| ID |} ⟩(‵{| p |}) ≡ₓ ‵{|‵{| p |}|}.
  Proof.
    apply pull_nra_opt.
    apply map_into_singleton.
  Qed.    

  (* ♯flatten( χ⟨ { { P1 } } ⟩( P2 ) ) ≡ χ⟨ { P1 } ⟩( P2 ) *)
  
  Lemma eflatten_over_map_into_singleton p1 p2 :
    ♯flatten( χ⟨ ‵{|‵{| p1 |}|} ⟩( p2 ) ) ≡ₓ χ⟨ ‵{| p1 |} ⟩( p2 ).
  Proof.
    apply pull_nra_opt.
    apply flatten_over_map_into_singleton.
  Qed.

  (* Join intro *)

  Lemma join_intro p1 p2 p3 :
    σ⟨ p1 ⟩( p2 × p3 ) ≡ₓ ⋈⟨ p1 ⟩(p2, p3).
  Proof.
    apply pull_nra_opt.
    simpl; unfold join.
    unfold nra_eq; intros ? ? _.
    reflexivity.
  Qed.
    
  (*****************)
  (* Rules Section *)
  (*****************)
  
  (* Composite rewrites, useful for rules optimization *)
  
  Lemma emap_singleton_rec s1 s2 :
    χ⟨‵[| (s1, ID) |] ⟩( ‵{|(ID) · s2 |}) ≡ₓ ‵{|‵[| (s1, (ID) · s2) |] |}.
  Proof.
    apply pull_nra_opt.
    apply map_singleton_rec.
  Qed.    

  (* χ⟨ ID.a ⟩( { P } ) ≡ { P.a } *)
  
  Lemma emap_dot_singleton s p :
    χ⟨ (ID)·s ⟩( ‵{| p |} ) ≡ₓ ‵{| p·s |}.
  Proof.
    apply pull_nra_opt.
    apply map_dot_singleton.
  Qed.

  (*
     μ[a1][PDATA]( { [ PBIND : p1; a1 : {p2} ] } ) ≡ₓ { [ PBIND : p1; PDATA : p2 ] }
   *)

  Lemma eunnest_singleton_context p1 p2 :
    μ["a1"]["PDATA"]( ‵{|‵[| ("PBIND", p1)|] ⊕ ‵[| ("a1", ‵{|p2|})|]|})
     ≡ₓ ‵{|‵[| ("PBIND", p1)|] ⊕ ‵[| ("PDATA", p2)|]|}.
  Proof.
    apply eunnest_singleton.
    split; try congruence.
    split; try congruence.
  Qed.

  (* χ⟨ [ PBIND : ID.PBIND; PDATA : ID.PDATA.WORLD ].PDATA ⟩({ p })
     ≡ { [ PBIND : p.PBIND; PDATA: p.PDATA.WORLD ].PDATA } *)
  
  Lemma esubstitute_in_bindings (p:nraext) :
    χ⟨ (‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PDATA"·"WORLD") |])·"PDATA" ⟩( ‵{| p |} )
     ≡ₓ ‵{|(‵[| ("PBIND", p·"PBIND") |] ⊕ ‵[| ("PDATA", p·"PDATA"·"WORLD") |])·"PDATA" |}.
  Proof.
    apply pull_nra_opt.
    apply substitute_in_bindings.
  Qed.

  (* [ PBIND : ID.PBIND; PDATA : ID.PBIND ].PDATA ≡ₐ ID.PBIND *)

  Lemma edot_from_duplicate_bind_r :
    (‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PBIND") |])·"PDATA" ≡ₓ ID·"PBIND".
  Proof.
    apply pull_nra_opt.
    apply dot_from_duplicate_bind_r.
  Qed.
    
  (* [ PBIND : ID.PBIND; PDATA : ID.PBIND ].PDATA ≡ₐ ID.PBIND *)

  Lemma edot_from_duplicate_bind_l :
    (‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PBIND") |])·"PBIND" ≡ₓ ID·"PBIND".
  Proof.
    apply pull_nra_opt.
    apply dot_from_duplicate_bind_l.
  Qed.

  (* [ PBIND : ID·PBIND; PDATA : ID·PBIND·WORLD ]·PDATA ≡ ID·PBIND·WORLD *)
  
  Lemma edot_dot_from_duplicate_bind :
    (‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PBIND"·"WORLD") |])·"PDATA"
     ≡ₓ ID·"PBIND"·"WORLD".
  Proof.
    apply pull_nra_opt.
    apply dot_dot_from_duplicate_bind.
  Qed.

  (*   [ PBIND : ID.PBIND;
         a1 : χ⟨ [ PBIND : ID.PBIND; PDATA : ID.PDATA.e ].PDATA ⟩ (
                 { [ PBIND : ID.PBIND; PDATA : ID.PBIND ] }
                 ) ]
     ≡ₐ [ PBIND : ID.PBIND; a1 : { ID.PBIND.e } ].
   *)

  Lemma ebig_nested_bind_simplify_one :
    ‵[| ("PBIND", ID·"PBIND") |]
     ⊕ ‵[| ("a1",
            χ⟨(‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PDATA"·"e") |])·"PDATA"
             ⟩( ‵{|‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID· "PBIND") |] |}))|]
     ≡ₓ ‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("a1", ‵{| ID·"PBIND"·"e" |}) |].
  Proof.
    apply pull_nra_opt.
    apply big_nested_bind_simplify_one.
  Qed.

End NRAExtRewrite.

