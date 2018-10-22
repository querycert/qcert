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

(** Imp with the Json data model *)

Require Import String.
Require Import Utils.
Require Import Imp.

Section Syntax.

  Definition imp_json_data := json.

  (* XXX This should contain at least:
         - all JS operators/expressions used in translation from NNRSimp to JsAst
         - all JS operators/expressions used to manipulate values in data but not in json (brands, nat, left, right, foreign)
     imp_json_op constructors names are based on JsAst names
     imp_json_runtime_op constructors namess are based on Qcert operators names ??
  *)
  Definition imp_json_op := json_op. (* See ./Utils/JSONOperators.v *)
  Inductive imp_json_runtime_op := (* XXX TODO -- Look at NNRSimptoJavaScriptAst XXX *)
  | JSONRuntimeEqual : imp_json_runtime_op
  | JSONRuntimeRecConcat : imp_json_runtime_op
  | JSONRuntimeRecMerge : imp_json_runtime_op
  | JSONRuntimeDistinct : imp_json_runtime_op
  | JSONRuntimeGroupBy : imp_json_runtime_op
  | JSONRuntimeDeref : imp_json_runtime_op
  | JSONRuntimeEither : imp_json_runtime_op
  | JSONRuntimeToLeft: imp_json_runtime_op
  | JSONRuntimeToRight: imp_json_runtime_op
  | JSONRuntimeRemove: imp_json_runtime_op
  | JSONRuntimeProject: imp_json_runtime_op
  | JSONRuntimeSingleton : imp_json_runtime_op
  | JSONRuntimeFlatten : imp_json_runtime_op
  | JSONRuntimeSort : imp_json_runtime_op
  | JSONRuntimeCount : imp_json_runtime_op
  | JSONRuntimeSubstring : imp_json_runtime_op
  | JSONRuntimeBrand : imp_json_runtime_op
  | JSONRuntimeUnbrand : imp_json_runtime_op
  | JSONRuntimeCast : imp_json_runtime_op
  | JSONRuntimeNatAbs : imp_json_runtime_op
  | JSONRuntimeNatLog2 : imp_json_runtime_op
  | JSONRuntimeNatSqrt : imp_json_runtime_op
  | JSONRuntimeNatSum : imp_json_runtime_op
  | JSONRuntimeNatMin : imp_json_runtime_op
  | JSONRuntimeNatMax : imp_json_runtime_op
  | JSONRuntimeNatArithMean : imp_json_runtime_op
  | JSONRuntimeFloatOfNat : imp_json_runtime_op
  | JSONRuntimeSum : imp_json_runtime_op
  | JSONRuntimeArithMean : imp_json_runtime_op
  .

  Definition imp_json_expr := @imp_expr imp_json_data imp_json_op imp_json_runtime_op.
  Definition imp_json_stmt := @imp_stmt imp_json_data imp_json_op imp_json_runtime_op.
  Definition imp_json_function := @imp_function imp_json_data imp_json_op imp_json_runtime_op.
  Definition imp_json := @imp imp_json_data imp_json_op imp_json_runtime_op.

End Syntax.
