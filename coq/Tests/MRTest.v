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

  Require Import Arith.
  
  Fixpoint nfirsts {A} (n:nat) (l:list A) : list A :=
    if (eq_nat_dec n O) then nil
    else
      match l with
      | nil => nil
      | x :: l' => x :: (nfirsts (pred n) l')
      end.

  
  
End MRTest.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
