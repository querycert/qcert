(*
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

(** This module contains extraction code for definitions and
operations on floating point numbers. *)

(** This module assumes Nat is extracted to int and Z is extracted to
int *)

Require Import JsAst.JsNumber.
Require Import FloatAdd.
Require Import EquivDec.
Require Import Extraction.

(* PrimFloat.float extraction via ExtrOCamlFloats depends on the kernel float Float64 library.
   This is annoying for building, and also causes problems because the type t is opaque
   and there is no non-magic way to get a float out of it
 *)

Extract Inlined Constant PrimFloat.float => "float".
Extract Inlined Constant float => "float".

Extract Inlined Constant float_nan => "Float.nan".
Extract Inlined Constant float_zero => "0.".
Extract Inlined Constant float_neg_zero => "(-0.)".
Extract Inlined Constant float_one => "1.".
Extract Inlined Constant float_neg_one => "(-1.)".
Extract Inlined Constant float_infinity => "Float.infinity".
Extract Inlined Constant float_neg_infinity => "Float.neg_infinity".

(*
Extract Inductive FloatClass.float_class =>
  "Float64.float_class"
  [ "PNormal" "NNormal" "PSubn" "NSubn" "PZero" "NZero" "PInf" "NInf" "NaN" ].
Extract Inductive PrimFloat.float_comparison =>
  "Float64.float_comparison"
    [ "FEq" "FLt" "FGt" "FNotComparable" ].

*)
Extract Inlined Constant float_max_value => "Float.max_float".
Extract Inlined Constant float_min_value => "Float.min_value".

Extract Inlined Constant float_from_string => "(fun x -> float_of_string (Util.string_of_char_list x))".
Extract Inlined Constant float_to_string => "(fun x -> Util.char_list_of_string (Util.qcert_string_of_float x))".

Extract Inlined Constant float_neg => "(fun x -> Float.neg x)".

Extract Inlined Constant float_floor => "(fun x -> Float.floor x)".
Extract Inlined Constant float_absolute => "(fun x -> Float.abs x)".

Extract Inlined Constant float_sign => "(fun x -> Util.float_sign x)".

(** Defines additional operations on FLOATs *)

(** Binary operations *)
Extract Inlined Constant float_add => "(fun x y -> x +. y)".
Extract Inlined Constant float_sub => "(fun x y -> x -. y)".
Extract Inlined Constant float_mult => "(fun x y -> x *. y)".
Extract Inlined Constant float_div => "(fun x y -> x /. y)".

(** Unary operations *)
Extract Inlined Constant float_sqrt => "(fun x -> Float.sqrt x)".
Extract Inlined Constant float_exp => "(fun x -> Float.exp x)".
Extract Inlined Constant float_log => "(fun x -> Float.log x)".
Extract Inlined Constant float_log10 => "(fun x -> Float.log10 x)".
Extract Inlined Constant float_ceil => "(fun x -> Float.ceil x)".

Extract Constant float_eq => "(fun n1 n2 -> n1 = n2)".
(* Extract Constant float_eq_dec => "(fun n1 n2 -> n1 = n2)". *)


Extract Inlined Constant float_pow => "(fun x y -> x ** y)".
Extract Inlined Constant float_min => "(fun x y -> min x y)".
Extract Inlined Constant float_max => "(fun x y -> max x y)".
Extract Inlined Constant float_ne => "(fun x y -> x <> y)".

Extract Inlined Constant float_lt => "(fun x y -> x < y)".
Extract Inlined Constant float_le  => "(fun x y -> x <= y)".
Extract Inlined Constant float_gt  => "(fun x y -> x > y)".
Extract Inlined Constant float_ge  => "(fun x y -> x >= y)".

Require Import ZArith.
Extract Inlined Constant float_of_int => "(fun x -> float_of_int x)".

Extract Inlined Constant float_truncate => "(fun x -> truncate x)".

Extract Inlined Constant JsNumber.to_string => "(fun x -> Util.char_list_of_string (Util.qcert_string_of_float x))".
