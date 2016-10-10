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

Section QEnv.

  Require Import String List String EquivDec.
  
  Require Import BasicRuntime.
  Require Import Pattern Rule.

  (*********
   * Utils *
   *********)

  (* Initial variables for the input and environment *)
  (* Java equivalents: in NnrcToNrcmr as static fields *)
  Definition init_vid := "id"%string.
  Definition init_venv := "env"%string.
  Definition init_vinit := "init"%string.

  Context {fdata:foreign_data}.
  
  Definition unwrap_result res :=
    match res with
    | None => None
    | Some (dcoll l) => Some l
    | Some _ => None
    end.

  Require Import DData.

  Definition validate (oresult oexpected:option (list data))
    := match oresult, oexpected with
       | None, None => true
       | Some ((dcoll result)::nil), Some expected =>
         if permutation_dec result expected 
         then true
         else false
       | _,_ => false
       end.
  (* validate a successful run *)
  Definition validate_success (oresult:option (list data)) (expected:list data)
    := validate oresult (Some expected).
  
  (* We want to prove things of the form 
    validate result expected = true
    This can be proven just by eq_refl and implicit normalization,
    but normalization using compute (the default) is slow.
    This tactic explicitly normalizes using vm_compute.
    and then applies reflexivity.  This is *much* faster.
   *)

  (* Check Rule/CAMP result *)

  Definition validate_rule_success (res:option (list data)) exp : bool :=
    validate_success res exp.

  (* Check NRAEnv/NNRC/NNRCMR/CloudantMR result *)
  
  Definition validate_lifted_success (res:option data) exp : bool :=
    validate_success (unwrap_result res) exp.

End QEnv.

(* validate that the answer is correct.  Since the result is unordered,
      we check that the result answer is a permutation of the expected
       answer *)
Ltac fast_refl := vm_compute; reflexivity.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
