(*
 * Copyright 2015-2018 Clause
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

(* Unary operators *)

Require Import String.
Require Import List.
Require Import ZArith.
Require Import Float.
Require Import ListAdd.
Require Import Lift.
Require Import Assoc.
Require Import Bindings.
Require Import JSON.

Section JSONOperators.

  Import ListNotations.

  Inductive json_op :=     (* XXX TODO XXX *)(* JsAst *)                     (* Syntax *)
  | JSONOpNot : json_op                          (* unary_op_not *)              (* !v *)
  | JSONOpNeg : json_op                          (* unary_op_neg *)              (* -v *)
  | JSONOpAnd : json_op                          (* binary_op_and *)             (* v1 && v2 *)
  | JSONOpOr : json_op                           (* binary_op_or *)              (* v1 || v2 *)
  | JSONOpLt : json_op                           (* binary_op_lt *)              (* v1 < v2 *)
  | JSONOpLe : json_op                           (* binary_op_le *)              (* v1 <= v2 *)
  | JSONOpGt : json_op                           (* binary_op_gt *)              (* v1 > v2 *)
  | JSONOpGe : json_op                           (* binary_op_ge *)              (* v1 >= v2 *)
  | JSONOpAddString : json_op                    (* binary_op_add *)             (* v1 + v2 *)
  | JSONOpAddNumber : json_op                    (* binary_op_add *)             (* v1 + v2 *)
  | JSONOpSub : json_op                          (* binary_op_sub *)             (* v1 - v2 *)
  | JSONOpMult : json_op                         (* binary_op_mult *)            (* v1 * v2 *)
  | JSONOpDiv : json_op                          (* binary_op_div *)             (* v1 / v2 *)
  | JSONOpStrictEqual : json_op                  (* binary_op_strict_equal *)    (* v1 === v2 *)
  | JSONOpStrictDisequal : json_op               (* binary_op_strict_disequal *) (* v1 !== v2 *)
(*| JSONOpIn : json_op *)                        (* binary_op_in *)              (* v1 in v2 *) (* XXX either 'in' or hasOwnProperty, not both *)
  (* Array Stuff *)
  | JSONOpArray : json_op                        (* expr_array *)                (* [ v1, ...vn ] XXX Nary? *)
  | JSONOpArrayLength : json_op                  (* expr_access? *)              (* v.length *)
  | JSONOpArrayPush : json_op                    (* expr_access? *)              (* v.push(v2) or var v' = v.slice(); v'.push(v2) XXX Does not actually claim to be mutable from a semantic stand-point *)
  | JSONOpArrayAccess : json_op                  (* array_get *)                 (* v[i] *)
  (* Object Stuff *)
  | JSONOpObject : list string -> json_op        (* expr_object *)               (* { a1:v1, ...an:vn } XXX Nary? *)
  | JSONOpAccess : string -> json_op             (* expr_access *)               (* v['a'] or v.a *)
  | JSONOpHasOwnProperty : string -> json_op     (* expr_call ?? XXX *)          (* v.hasOwnProperty('a') *)
  | JSONOpToString : json_op                     (* expr_call ?? XXX *)          (* v.toString() *)
  (* Math stuff *)
  | JSONOpMathMin : json_op                      (* expr_call *)                 (* Math.min(e1, e2) *)
  | JSONOpMathMax : json_op                      (* expr_call *)                 (* Math.max(e1, e2) *)
  | JSONOpMathMinApply : json_op                 (* expr_call *)                 (* Math.min.apply(Math, e) *)
  | JSONOpMathMaxApply : json_op                 (* expr_call *)                 (* Math.max.apply(Math, e) *)
  | JSONOpMathPow : json_op                      (* expr_call *)                 (* Math.pow(e1, e2) *)
  | JSONOpMathExp : json_op                      (* expr_call *)                 (* Math.exp(e) *)
  | JSONOpMathAbs : json_op                      (* expr_call *)                 (* Math.abs(e) *)
  | JSONOpMathLog : json_op                      (* expr_call *)                 (* Math.log2(e) *)
  | JSONOpMathLog10 : json_op                    (* expr_call *)                 (* Math.log10(e) *)
  | JSONOpMathSqrt : json_op                     (* expr_call *)                 (* Math.sqrt(e) *)
  | JSONOpMathCeil : json_op                     (* expr_call *)                 (* Math.ceil(e) *)
  | JSONOpMathFloor : json_op                    (* expr_call *)                 (* Math.floor(e) *)
  | JSONOpMathTrunc : json_op                    (* expr_call *)                 (* Math.trunc(e) *)
  .

  Definition json_op_eval (op:json_op) (j:list json) : option json :=
    match op with
    | JSONOpNot =>
      match j with
      | [jbool b] => Some (jbool (negb b))
      | _ => None
      end
    | JSONOpNeg =>
      match j with
      | [jnumber n] => Some (jnumber (float_neg n))
      | _ => None
      end
    | JSONOpAnd =>
      match j with
      | [jbool b1; jbool b2] => Some (jbool (andb b1 b2))
      | _ => None
      end
    | JSONOpOr =>
      match j with
      | [jbool b1; jbool b2] => Some (jbool (orb b1 b2))
      | _ => None
      end
    | JSONOpLt =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jbool (float_lt n1 n2))
      | _ => None
      end
    | JSONOpLe =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jbool (float_le n1 n2))
      | _ => None
      end
    | JSONOpGt =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jbool (float_gt n1 n2))
      | _ => None
      end
    | JSONOpGe =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jbool (float_ge n1 n2))
      | _ => None
      end
    | JSONOpAddString =>
      match j with
      | [jstring s1; jstring s2] => Some (jstring (s1 ++ s2))
      | _ => None
      end
    | JSONOpAddNumber =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jnumber (float_add n1 n2))
      | _ => None
      end
    | JSONOpSub =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jnumber (float_sub n1 n2))
      | _ => None
      end
    | JSONOpMult =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jnumber (float_mult n1 n2))
      | _ => None
      end
    | JSONOpDiv =>
      match j with
      | [jnumber n1; jnumber n2] => Some (jnumber (float_div n1 n2))
      | _ => None
      end
    | JSONOpStrictEqual => None (* XXX TODO *)
    | JSONOpStrictDisequal => None (* XXX TODO *)
    | JSONOpArray => Some (jarray j)
    | JSONOpArrayLength =>
      match j with
      | [jarray ja] => Some (jnumber (float_of_int (Z_of_nat (List.length ja))))
      | _ => None
      end
    | JSONOpArrayPush =>
      match j with
      | [jarray ja; je] => Some (jarray (ja ++ [je]))
      | _ => None
      end
    | JSONOpArrayAccess =>
      match j with
      | [jarray ja; jnumber n] => None (* XXX TODO XXX *)
      | _ => None
      end
    | JSONOpObject atts =>
      lift jobject (zip atts j)
    | JSONOpAccess att =>
      match j with
      | [jobject jl] =>
        edot jl att
      | _ => None
      end
    | JSONOpHasOwnProperty a =>
      match j  with
      | [jobject jl] =>
        if in_dec string_dec a (domain jl)
        then Some (jbool true)
        else Some (jbool false)
      | _ => None
      end
    | JSONOpToString => None (* XXX TODO XXX *)
    | JSONOpMathMin => None (* XXX TODO XXX *)
    | JSONOpMathMax => None (* XXX TODO XXX *)
    | JSONOpMathMinApply => None (* XXX TODO XXX *)
    | JSONOpMathMaxApply => None (* XXX TODO XXX *)
    | JSONOpMathExp => None (* XXX TODO XXX *)
    | JSONOpMathPow => None (* XXX TODO XXX *)
    | JSONOpMathAbs => None (* XXX TODO XXX *)
    | JSONOpMathLog => None (* XXX TODO XXX *)
    | JSONOpMathLog10 => None (* XXX TODO XXX *)
    | JSONOpMathSqrt => None (* XXX TODO XXX *)
    | JSONOpMathCeil => None (* XXX TODO XXX *)
    | JSONOpMathFloor => None (* XXX TODO XXX *)
    | JSONOpMathTrunc => None (* XXX TODO XXX *)
    end.

End JSONOperators.
