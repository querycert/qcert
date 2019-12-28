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
Require Import CommonRuntime.
Require Import Imp.

Section ImpEJson.
  Section Syntax.
    Context {ftoejson:foreign_ejson}.

    Definition imp_ejson_data := ejson.

    (* XXX This should contain at least:
       - all JS operators/expressions used in translation from NNRSimp to JsAst
       - all JS operators/expressions used to manipulate values in data but not in json (brands, nat, left, right, foreign)
       imp_ejson_op constructors names are based on JsAst names
       imp_ejson_runtime_op constructors namess are based on Qcert operators names ??
     *)
    Definition imp_ejson_op := ejson_op. (* See ./Common/EJson/EJsonOperators.v *)
    Inductive imp_ejson_runtime_op := (* XXX TODO -- Look at NNRSimptoJavaScriptAst XXX *)
    | EJsonRuntimeEqual : imp_ejson_runtime_op
    | EJsonRuntimeCompare : imp_ejson_runtime_op
    | EJsonRuntimeRecConcat : imp_ejson_runtime_op
    | EJsonRuntimeRecMerge : imp_ejson_runtime_op
    | EJsonRuntimeDistinct : imp_ejson_runtime_op
    | EJsonRuntimeGroupBy : imp_ejson_runtime_op
    | EJsonRuntimeDeref : imp_ejson_runtime_op
    | EJsonRuntimeEither : imp_ejson_runtime_op
    | EJsonRuntimeToLeft: imp_ejson_runtime_op
    | EJsonRuntimeToRight: imp_ejson_runtime_op
    | EJsonRuntimeRemove: imp_ejson_runtime_op
    | EJsonRuntimeProject: imp_ejson_runtime_op
    | EJsonRuntimeSingleton : imp_ejson_runtime_op
    | EJsonRuntimeFlatten : imp_ejson_runtime_op
    | EJsonRuntimeSort : imp_ejson_runtime_op
    | EJsonRuntimeCount : imp_ejson_runtime_op
    | EJsonRuntimeLength : imp_ejson_runtime_op
    | EJsonRuntimeSubstring : imp_ejson_runtime_op
    | EJsonRuntimeBrand : imp_ejson_runtime_op
    | EJsonRuntimeUnbrand : imp_ejson_runtime_op
    | EJsonRuntimeCast : imp_ejson_runtime_op
    | EJsonRuntimeNatPlus : imp_ejson_runtime_op
    | EJsonRuntimeNatMinus : imp_ejson_runtime_op
    | EJsonRuntimeNatMult : imp_ejson_runtime_op
    | EJsonRuntimeNatDiv : imp_ejson_runtime_op
    | EJsonRuntimeNatRem : imp_ejson_runtime_op
    | EJsonRuntimeNatAbs : imp_ejson_runtime_op
    | EJsonRuntimeNatLog2 : imp_ejson_runtime_op
    | EJsonRuntimeNatSqrt : imp_ejson_runtime_op
    | EJsonRuntimeNatSum : imp_ejson_runtime_op
    | EJsonRuntimeNatMin : imp_ejson_runtime_op
    | EJsonRuntimeNatMax : imp_ejson_runtime_op
    | EJsonRuntimeNatArithMean : imp_ejson_runtime_op
    | EJsonRuntimeFloatOfNat : imp_ejson_runtime_op
    | EJsonRuntimeSum : imp_ejson_runtime_op
    | EJsonRuntimeArithMean : imp_ejson_runtime_op
    | EJsonRuntimeBunion : imp_ejson_runtime_op
    | EJsonRuntimeBminus : imp_ejson_runtime_op
    | EJsonRuntimeBmin : imp_ejson_runtime_op
    | EJsonRuntimeBmax : imp_ejson_runtime_op
    | EJsonRuntimeBnth : imp_ejson_runtime_op
    | EJsonRuntimeContains : imp_ejson_runtime_op
    | EJsonRuntimeStringJoin : imp_ejson_runtime_op
    | EJsonRuntimeToString : imp_ejson_runtime_op
    | EJsonRuntimeToText : imp_ejson_runtime_op
    .

    Definition imp_ejson_expr := @imp_expr imp_ejson_data imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson_stmt := @imp_stmt imp_ejson_data imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson_function := @imp_function imp_ejson_data imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson := @imp imp_ejson_data imp_ejson_op imp_ejson_runtime_op.

  End Syntax.

  Section Util.

    Local Open Scope string.

    Definition string_of_ejson_runtime_op (op: imp_ejson_runtime_op) :=
      match op with
      | EJsonRuntimeEqual => "equal"
      | EJsonRuntimeCompare => "compare"
      | EJsonRuntimeRecConcat => "concat"
      | EJsonRuntimeRecMerge => "mergeConcat"
      | EJsonRuntimeDistinct => "distinct"
      | EJsonRuntimeGroupBy => "groupBy" (* XXX TODO: to check XXX *)
      | EJsonRuntimeDeref => "deref"
      | EJsonRuntimeEither => "either"
      | EJsonRuntimeToLeft=> "toLeft"
      | EJsonRuntimeToRight=> "toRight"
      | EJsonRuntimeRemove=> "remove"
      | EJsonRuntimeProject=> "project"
      | EJsonRuntimeSingleton => "singleton"
      | EJsonRuntimeFlatten => "flatten"
      | EJsonRuntimeSort => "sort"
      | EJsonRuntimeCount => "count"
      | EJsonRuntimeLength => "stringLength"
      | EJsonRuntimeSubstring => "substring"
      | EJsonRuntimeBrand => "brand"
      | EJsonRuntimeUnbrand => "unbrand"
      | EJsonRuntimeCast => "cast"
      | EJsonRuntimeNatPlus => "natPlus"
      | EJsonRuntimeNatMinus => "natMinus"
      | EJsonRuntimeNatMult => "natMult"
      | EJsonRuntimeNatDiv => "natDiv"
      | EJsonRuntimeNatRem => "natRem"
      | EJsonRuntimeNatAbs => "natAbs"
      | EJsonRuntimeNatLog2 => "natLog2"
      | EJsonRuntimeNatSqrt => "natSqrt"
      | EJsonRuntimeNatSum => "natSum"
      | EJsonRuntimeNatMin => "natMin"
      | EJsonRuntimeNatMax => "natMax"
      | EJsonRuntimeNatArithMean => "natArithMean"
      | EJsonRuntimeFloatOfNat => "floatOfNat"
      | EJsonRuntimeSum => "sum"
      | EJsonRuntimeArithMean => "arithMean"
      | EJsonRuntimeBunion => "bunion"
      | EJsonRuntimeBminus => "bminus"
      | EJsonRuntimeBmin => "bmin"
      | EJsonRuntimeBmax => "bmax"
      | EJsonRuntimeBnth => "bnth"
      | EJsonRuntimeContains => "contains"
      | EJsonRuntimeStringJoin => "stringJoin"
      | EJsonRuntimeToString => "toString"
      | EJsonRuntimeToText => "toText"
      end.

  End Util.
End ImpEJson.
