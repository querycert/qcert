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
Require Import ForeignEJSON.
Require Import EJSON.

Section EJSONOperators.

  Import ListNotations.

  Inductive ejson_op :=     (* XXX TODO XXX *)(* JsAst *)                     (* Syntax *)
  | EJSONOpNot : ejson_op                          (* unary_op_not *)              (* !v *)
  | EJSONOpNeg : ejson_op                          (* unary_op_neg *)              (* -v *)
  | EJSONOpAnd : ejson_op                          (* binary_op_and *)             (* v1 && v2 *)
  | EJSONOpOr : ejson_op                           (* binary_op_or *)              (* v1 || v2 *)
  | EJSONOpLt : ejson_op                           (* binary_op_lt *)              (* v1 < v2 *)
  | EJSONOpLe : ejson_op                           (* binary_op_le *)              (* v1 <= v2 *)
  | EJSONOpGt : ejson_op                           (* binary_op_gt *)              (* v1 > v2 *)
  | EJSONOpGe : ejson_op                           (* binary_op_ge *)              (* v1 >= v2 *)
  | EJSONOpAddString : ejson_op                    (* binary_op_add *)             (* v1 + v2 *)
  | EJSONOpAddNumber : ejson_op                    (* binary_op_add *)             (* v1 + v2 *)
  | EJSONOpSub : ejson_op                          (* binary_op_sub *)             (* v1 - v2 *)
  | EJSONOpMult : ejson_op                         (* binary_op_mult *)            (* v1 * v2 *)
  | EJSONOpDiv : ejson_op                          (* binary_op_div *)             (* v1 / v2 *)
  | EJSONOpStrictEqual : ejson_op                  (* binary_op_strict_equal *)    (* v1 === v2 *)
  | EJSONOpStrictDisequal : ejson_op               (* binary_op_strict_disequal *) (* v1 !== v2 *)
  (*| EJSONOpIn : ejson_op *)                        (* binary_op_in *)              (* v1 in v2 *) (* XXX either 'in' or hasOwnProperty, not both *)
  (* Array Stuff *)
  | EJSONOpArray : ejson_op                        (* expr_array *)                (* [ v1, ...vn ] XXX Nary? *)
  | EJSONOpArrayLength : ejson_op                  (* expr_access? *)              (* v.length *)
  | EJSONOpArrayPush : ejson_op                    (* expr_access? *)              (* v.push(v2) or var v' = v.slice(); v'.push(v2) XXX Does not actually claim to be mutable from a semantic stand-point *)
  | EJSONOpArrayAccess : ejson_op                  (* array_get *)                 (* v[i] *)
  (* Object Stuff *)
  | EJSONOpObject : list string -> ejson_op        (* expr_object *)               (* { a1:v1, ...an:vn } XXX Nary? *)
  | EJSONOpAccess : string -> ejson_op             (* expr_access *)               (* v['a'] or v.a *)
  | EJSONOpHasOwnProperty : string -> ejson_op     (* expr_call ?? XXX *)          (* v.hasOwnProperty('a') *)
  | EJSONOpToString : ejson_op                     (* expr_call ?? XXX *)          (* v.toString() *)
  (* Math stuff *)
  | EJSONOpMathMin : ejson_op                      (* expr_call *)                 (* Math.min(e1, e2) *)
  | EJSONOpMathMax : ejson_op                      (* expr_call *)                 (* Math.max(e1, e2) *)
  | EJSONOpMathMinApply : ejson_op                 (* expr_call *)                 (* Math.min.apply(Math, e) *)
  | EJSONOpMathMaxApply : ejson_op                 (* expr_call *)                 (* Math.max.apply(Math, e) *)
  | EJSONOpMathPow : ejson_op                      (* expr_call *)                 (* Math.pow(e1, e2) *)
  | EJSONOpMathExp : ejson_op                      (* expr_call *)                 (* Math.exp(e) *)
  | EJSONOpMathAbs : ejson_op                      (* expr_call *)                 (* Math.abs(e) *)
  | EJSONOpMathLog : ejson_op                      (* expr_call *)                 (* Math.log2(e) *)
  | EJSONOpMathLog10 : ejson_op                    (* expr_call *)                 (* Math.log10(e) *)
  | EJSONOpMathSqrt : ejson_op                     (* expr_call *)                 (* Math.sqrt(e) *)
  | EJSONOpMathCeil : ejson_op                     (* expr_call *)                 (* Math.ceil(e) *)
  | EJSONOpMathFloor : ejson_op                    (* expr_call *)                 (* Math.floor(e) *)
  | EJSONOpMathTrunc : ejson_op                    (* expr_call *)                 (* Math.trunc(e) *)
  .

  Section Evaluation.
    Context {fejson:foreign_ejson}.

    Definition ejson_op_eval (op:ejson_op) (j:list ejson) : option ejson :=
      match op with
      | EJSONOpNot =>
        match j with
        | [ejbool b] => Some (ejbool (negb b))
        | _ => None
        end
      | EJSONOpNeg =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_neg n))
        | _ => None
        end
      | EJSONOpAnd =>
        match j with
        | [ejbool b1; ejbool b2] => Some (ejbool (andb b1 b2))
        | _ => None
        end
      | EJSONOpOr =>
        match j with
        | [ejbool b1; ejbool b2] => Some (ejbool (orb b1 b2))
        | _ => None
        end
      | EJSONOpLt =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_lt n1 n2))
        | _ => None
        end
      | EJSONOpLe =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_le n1 n2))
        | _ => None
        end
      | EJSONOpGt =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_gt n1 n2))
        | _ => None
        end
      | EJSONOpGe =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_ge n1 n2))
        | _ => None
        end
      | EJSONOpAddString =>
        match j with
        | [ejstring s1; ejstring s2] => Some (ejstring (s1 ++ s2))
        | _ => None
        end
      | EJSONOpAddNumber =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_add n1 n2))
        | _ => None
        end
      | EJSONOpSub =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_sub n1 n2))
        | _ => None
        end
      | EJSONOpMult =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_mult n1 n2))
        | _ => None
        end
      | EJSONOpDiv =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_div n1 n2))
        | _ => None
        end
      | EJSONOpStrictEqual => None (* XXX TODO *)
      | EJSONOpStrictDisequal => None (* XXX TODO *)
      | EJSONOpArray => Some (ejarray j)
      | EJSONOpArrayLength =>
        match j with
        | [ejarray ja] => Some (ejnumber (float_of_int (Z_of_nat (List.length ja))))
        | _ => None
        end
      | EJSONOpArrayPush =>
        match j with
        | [ejarray ja; je] => Some (ejarray (ja ++ [je]))
        | _ => None
        end
      | EJSONOpArrayAccess =>
        match j with
        | [ejarray ja; ejnumber n] => None (* XXX TODO XXX *)
        | _ => None
        end
      | EJSONOpObject atts =>
        lift ejobject (zip atts j)
      | EJSONOpAccess att =>
        match j with
        | [ejobject jl] =>
          edot jl att
        | _ => None
        end
      | EJSONOpHasOwnProperty a =>
        match j  with
        | [ejobject jl] =>
          if in_dec string_dec a (domain jl)
          then Some (ejbool true)
          else Some (ejbool false)
        | _ => None
        end
      | EJSONOpToString => None (* XXX TODO XXX *)
      | EJSONOpMathMin => None (* XXX TODO XXX *)
      | EJSONOpMathMax => None (* XXX TODO XXX *)
      | EJSONOpMathMinApply => None (* XXX TODO XXX *)
      | EJSONOpMathMaxApply => None (* XXX TODO XXX *)
      | EJSONOpMathExp => None (* XXX TODO XXX *)
      | EJSONOpMathPow => None (* XXX TODO XXX *)
      | EJSONOpMathAbs => None (* XXX TODO XXX *)
      | EJSONOpMathLog => None (* XXX TODO XXX *)
      | EJSONOpMathLog10 => None (* XXX TODO XXX *)
      | EJSONOpMathSqrt => None (* XXX TODO XXX *)
      | EJSONOpMathCeil => None (* XXX TODO XXX *)
      | EJSONOpMathFloor => None (* XXX TODO XXX *)
      | EJSONOpMathTrunc => None (* XXX TODO XXX *)
      end.
  End Evaluation.

End EJSONOperators.
