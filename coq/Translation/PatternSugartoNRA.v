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

Section PatternSugartoNRA.

  Require Import String.
  Require Import List.

  Require Import Utils BasicRuntime.
  Require Import NRARuntime.
  Require Import Pattern PatternSugar Rule.
  Require Import PatterntoNRA.
  
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.

  (* Mapping to NRA for the built-in operators -- useful for the paper as illustration *)

  (* and *)
  
  Definition alg_of_pand (p1 p2:pat) : alg :=
    alg_of_pat (pand p1 p2).

  Definition alg_for_pand (q1 q2:alg) : alg :=
    (♯flatten(χ⟨q2
             ⟩( unnest_two "PBIND1" "PBIND"
                  (χ⟨‵[| ("PDATA", (ID) · "PDATA")|]
                     ⊕ (‵[| ("PCONST", (ID) · "PCONST")|]
                        ⊕ ‵[| ("PBIND1", (ID) · "PBIND" ⊗ (ID) · "PBIND1")|])
                   ⟩( unnest_two "a1" "PBIND1"
                        (‵{|ID
                            ⊕ ‵[| ("a1",
                              χ⟨‵[||] ⟩( σ⟨ID ⟩( q1)))|]|}))))))%alg.


  Lemma alg_of_pand_works (p1 p2:pat) :
    alg_of_pat (pand p1 p2) = alg_for_pand (alg_of_pat p1) (alg_of_pat p2).
  Proof.
    simpl.
    reflexivity.
  Qed.
  
  (* WW *)

  Definition alg_of_WW (p:pat) :=
    alg_of_pat (WW p).

End PatternSugartoNRA.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
