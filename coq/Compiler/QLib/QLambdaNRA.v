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

Require Import CompilerRuntime.

Module QLambdaNRA(runtime:CompilerRuntime).
  Require String.
  Require QData QOperators.
  Require LambdaAlg LambdaAlgSugar.

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.

  Definition expr : Set
    := LambdaAlg.lalg.
  Definition lambda_expr : Set
    := LambdaAlg.lalg_lambda.
  Definition t : Set
    := expr.
  Definition var : Set
    := String.string.

  Definition lalambda : var -> expr -> lambda_expr
    := LambdaAlg.LALambda.
  Definition lavar : var -> expr
    := LambdaAlg.LAVar.
  Definition laconst : Data.data -> expr
    := LambdaAlg.LAConst.
  Definition ltable  : String.string -> expr
    := LambdaAlg.LATable.
  Definition labinop : Ops.Binary.op -> expr -> expr -> expr
    := LambdaAlg.LABinop.
  Definition launop : Ops.Unary.op -> expr -> expr
    := LambdaAlg.LAUnop.
  Definition lamap : lambda_expr -> expr -> expr
    := LambdaAlg.LAMap.
  Definition laselect : lambda_expr -> expr -> expr
    := LambdaAlg.LASelect.
  Definition lamapconcat : lambda_expr -> expr -> expr
    := LambdaAlg.LAMapConcat.

  Definition ladot : String.string -> expr -> expr 
    := LambdaAlgSugar.LADot.
  Definition laarrow : String.string -> expr -> expr 
    := LambdaAlgSugar.LAArrow.
  Definition lastruct : list (String.string * expr) -> expr 
    := LambdaAlgSugar.LAStruct.

  Definition latableify : expr -> expr
    := LambdaAlgSugar.la_tableify.

End QLambdaNRA.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
