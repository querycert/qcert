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

Section CAMPSugartoNRA.

  Require Import String.
  Require Import List.

  Require Import Utils BasicRuntime.
  Require Import NRARuntime.
  Require Import CAMPRuntime RuleRuntime.
  Require Import CAMPtoNRA.
  
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.

  (* Mapping to NRA for the built-in operators -- useful for the paper as illustration *)

  (* and *)
  
  Definition nra_of_pand (p1 p2:pat) : nra :=
    nra_of_pat (pand p1 p2).

  Definition nra_for_pand (q1 q2:nra) : nra :=
    (♯flatten(χ⟨q2
             ⟩( unnest_two "PBIND1" "PBIND"
                  (χ⟨‵[| ("PDATA", (ID) · "PDATA")|]
                     ⊕ (‵[| ("PCONST", (ID) · "PCONST")|]
                        ⊕ ‵[| ("PBIND1", (ID) · "PBIND" ⊗ (ID) · "PBIND1")|])
                   ⟩( unnest_two "a1" "PBIND1"
                        (‵{|ID
                            ⊕ ‵[| ("a1",
                              χ⟨‵[||] ⟩( σ⟨ID ⟩( q1)))|]|}))))))%nra.


  Lemma nra_of_pand_works (p1 p2:pat) :
    nra_of_pat (pand p1 p2) = nra_for_pand (nra_of_pat p1) (nra_of_pat p2).
  Proof.
    simpl.
    reflexivity.
  Qed.
  
  (* WW *)

  Definition nra_of_WW (p:pat) :=
    nra_of_pat (WW p).

End CAMPSugartoNRA.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
