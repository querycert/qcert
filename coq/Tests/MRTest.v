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

Require Import List String.
Require Import EquivDec.

Require Import Utils BasicRuntime.
Require Import CompilerTest.

Section MRTest.

  Require Import NNRCRuntime CloudantMR.
  Require Import TrivialModel.

  (* ...                     ...
     ... WORD COUNT WAS HERE ...
     ...                     ... *)
  
  (* Small instrumentation for NNRCMR and CloudantMR *)

  Require Import Arith NNRCMR.
  
  Fixpoint nfirsts_aux (n:nat) (l:list mr): (list mr * option mr) :=
    if (eq_nat_dec n O) then (nil, None)
    else
      if (eq_nat_dec n 1) then
        match l with
        | nil => (nil, None)
        | x :: l' => (x::nil, Some x)
        end
      else
        match l with
        | nil => (nil, None)
        | x :: nil => (x::nil, Some x)
        | x :: l' =>
          let (chain, last) := nfirsts_aux (pred n) l' in
          (x :: chain, last)
        end.

  Definition nfirsts n (chain: nrcmr) :=
    match nfirsts_aux n chain.(mr_chain) with
    | (l, None) => mkMRChain chain.(mr_inputs_loc) l (("x"%string::nil, NRCVar "x"%string), nil)
    | (l, Some mr) =>
      let x_loc := mr_output_localized mr in
      mkMRChain chain.(mr_inputs_loc) l (("x"%string::nil, NRCVar "x"%string), x_loc::nil)
    end.

End MRTest.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
