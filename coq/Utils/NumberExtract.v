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

Require Import JsAst.JsNumber.
Require Import Extraction.

Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> failwith ""FIXME: No extraction from binary float allowed yet."")"
]. 

Extract Constant JsNumber.of_int => "fun x -> float_of_int x".

Extract Constant JsNumber.nan => "nan".
Extract Constant JsNumber.zero => "0.".
Extract Constant JsNumber.neg_zero => "(-0.)".
Extract Constant JsNumber.one => "1.".
Extract Constant JsNumber.infinity => "infinity".
Extract Constant JsNumber.neg_infinity => "neg_infinity".
Extract Constant JsNumber.max_value => "max_float".
Extract Constant JsNumber.min_value => "(Int64.float_of_bits Int64.one)".
Extract Constant JsNumber.pi => "(4. *. atan 1.)".
Extract Constant JsNumber.e => "(exp 1.)".
Extract Constant JsNumber.ln2 => "(log 2.)".
Extract Constant JsNumber.floor => "floor".
Extract Constant JsNumber.absolute => "abs_float".

Extract Constant JsNumber.from_string =>
  "(fun s ->
    try
      let s = (String.concat """" (List.map (String.make 1) s)) in
      if s = """" then 0. else float_of_string s
    with Failure ""float_of_string"" -> nan)
   (* Note that we're using `float_of_string' there, which does not have the same
      behavior than JavaScript.  For instance it will read ""022"" as 22 instead of
      18, which should be the JavaScript result for it. *)".

Extract Constant JsNumber.to_string =>
  "(fun f -> 
    prerr_string (""Warning:  JsNumber.to_string called.  This might be responsible for errors.  Argument value:  "" ^ string_of_float f ^ ""."");
    prerr_newline();
    let string_of_number n =
      let sfn = string_of_float n in
      (if (sfn = ""inf"") then ""Infinity"" else
       if (sfn = ""-inf"") then ""-Infinity"" else
       if (sfn = ""nan"") then ""NaN"" else
       let inum = int_of_float n in
       if (float_of_int inum = n) then (string_of_int inum) else (string_of_float n)) in
    let ret = ref [] in (* Ugly, but the API for OCaml string is not very functional... *)
    String.iter (fun c -> ret := c :: !ret) (string_of_number f);
    List.rev !ret)
   (* Note that this is ugly, we should use the spec of JsNumber.to_string here (9.8.1). *)".

Extract Constant JsNumber.add => "(+.)".
Extract Constant JsNumber.sub => "(-.)".
Extract Constant JsNumber.mult => "( *. )".
Extract Constant JsNumber.div => "(/.)".
Extract Constant JsNumber.fmod => "mod_float".
Extract Constant JsNumber.neg => "(~-.)".
Extract Constant JsNumber.sign => "(fun f -> float_of_int (compare f 0.))".
  Require Import EquivDec.
Lemma number_eq_dec : EqDec number eq.
  admit.
Admitted.
  
Extract Constant number_eq_dec => "(fun n1 n2 -> 0 = compare n1 n2)".
(* Extract Constant JsNumber.number_comparable => "(fun n1 n2 -> 0 = compare n1 n2)". *)
Extract Constant JsNumber.lt_bool => "(<)".

Extract Constant JsNumber.to_int32 => 
"fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let i31 = 2. ** 31. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    (if int32bit >= i31 then int32bit -. i32 else int32bit)
  | _ -> 0.". (* LATER:  do in Coq.  Spec is 9.5, p. 47.*)

Extract Constant JsNumber.to_uint32 =>
"fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    int32bit
  | _ -> 0.". (* LAER:  do in Coq.  Spec is 9.6, p47.*)

Extract Constant JsNumber.modulo_32 => "(fun x -> let r = mod_float x 32. in if x < 0. then r +. 32. else r)".
Extract Constant JsNumber.int32_bitwise_not => "fun x -> Int32.to_float (Int32.lognot (Int32.of_float x))".
Extract Constant JsNumber.int32_bitwise_and => "fun x y -> Int32.to_float (Int32.logand (Int32.of_float x) (Int32.of_float y))".
Extract Constant JsNumber.int32_bitwise_or => "fun x y -> Int32.to_float (Int32.logor (Int32.of_float x) (Int32.of_float y))".
Extract Constant JsNumber.int32_bitwise_xor => "fun x y -> Int32.to_float (Int32.logxor (Int32.of_float x) (Int32.of_float y))".
Extract Constant JsNumber.int32_left_shift => "(fun x y -> Int32.to_float (Int32.shift_left (Int32.of_float x) (int_of_float y)))".
Extract Constant JsNumber.int32_right_shift => "(fun x y -> Int32.to_float (Int32.shift_right (Int32.of_float x) (int_of_float y)))".
Extract Constant JsNumber.uint32_right_shift => 
"(fun x y ->
  let i31 = 2. ** 31. in
  let i32 = 2. ** 32. in
  let newx = if x >= i31 then x -. i32 else x in
  let r = Int32.to_float (Int32.shift_right_logical (Int32.of_float newx) (int_of_float y)) in
  if r < 0. then r +. i32 else r)".


