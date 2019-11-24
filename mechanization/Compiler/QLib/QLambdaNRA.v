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
Require String.
Require QData.
Require QOperators.
Require LambdaNRA.
Require LambdaNRASugar.

Module QLambdaNRA(runtime:CompilerRuntime).

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.

  Definition expr : Set
    := LambdaNRA.lambda_nra.
  Definition lambda_expr : Set
    := LambdaNRA.lnra_lambda.
  Definition t : Set
    := expr.
  Definition var : Set
    := String.string.

  Definition lalambda : var -> expr -> lambda_expr
    := LambdaNRA.LNRALambda.
  Definition lavar : var -> expr
    := LambdaNRA.LNRAVar.
  Definition laconst : Data.qdata -> expr
    := LambdaNRA.LNRAConst.
  Definition latable  : String.string -> expr
    := LambdaNRA.LNRATable.
  Definition labinop : Ops.Binary.op -> expr -> expr -> expr
    := LambdaNRA.LNRABinop.
  Definition launop : Ops.Unary.op -> expr -> expr
    := LambdaNRA.LNRAUnop.
  Definition lamap : lambda_expr -> expr -> expr
    := LambdaNRA.LNRAMap.
  Definition lafilter : lambda_expr -> expr -> expr
    := LambdaNRA.LNRAFilter.
  Definition lamapproduct : lambda_expr -> expr -> expr
    := LambdaNRA.LNRAMapProduct.
  Definition laproduct : expr -> expr -> expr
    := LambdaNRA.LNRAProduct.

  Definition ladot : String.string -> expr -> expr 
    := LambdaNRASugar.LNRADot.
  Definition laarrow : String.string -> expr -> expr 
    := LambdaNRASugar.LNRAArrow.
  Definition lastruct : list (String.string * expr) -> expr 
    := LambdaNRASugar.LNRAStruct.
  Definition laflatmap : lambda_expr -> expr -> expr
    := LambdaNRASugar.LNRAFlatMap.

  Definition latableify : expr -> expr
    := LambdaNRASugar.la_tableify.

End QLambdaNRA.

