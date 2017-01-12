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

Section CAMPSugartoNRAEnv.

  Require Import String.
  Require Import List.

  Require Import Utils BasicRuntime.
  Require Import NRAEnvRuntime.
  Require Import CAMPRuntime RuleRuntime.
  Require Import CAMPtoNRAEnv.
  
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.

  Definition cnraenv_of_pand (p1 p2:pat) : cnraenv :=
    cnraenv_of_pat (pand p1 p2).

  Definition cnraenv_for_pand (q1 q2: cnraenv) : cnraenv :=
    ANUnop AFlatten
         (ANAppEnv (ANMapEnv q2)
            (ANUnop AFlatten
               (ANMap (ANBinop AMergeConcat ANEnv ANID)
                  (ANMap (ANConst (drec nil))
                     (ANSelect ANID q1))))).
  
  Lemma cnraenv_of_pand_works (p1 p2:pat) :
    cnraenv_of_pat (pand p1 p2) = cnraenv_for_pand (cnraenv_of_pat p1) (cnraenv_of_pat p2).
  Proof.
    reflexivity.
  Qed.

  (* WW *)

  Definition cnraenv_of_WW (p:pat) :=
    cnraenv_of_pat (WW p).

End CAMPSugartoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
