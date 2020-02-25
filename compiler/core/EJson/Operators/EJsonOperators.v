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

(* Unary operators *)

Require Import Bool.
Require Import EquivDec.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import Utils.
Require Import Float.
Require Import ListAdd.
Require Import Lift.
Require Import Assoc.
Require Import Bindings.
Require Import ForeignEJson.
Require Import EJson.

Section EJsonOperators.

  Import ListNotations.

  Inductive ejson_op :=
  | EJsonOpNot : ejson_op                          (* unary_op_not *)              (* !v *)
  | EJsonOpNeg : ejson_op                          (* unary_op_neg *)              (* -v *)
  | EJsonOpAnd : ejson_op                          (* binary_op_and *)             (* v1 && v2 *)
  | EJsonOpOr : ejson_op                           (* binary_op_or *)              (* v1 || v2 *)
  | EJsonOpLt : ejson_op                           (* binary_op_lt *)              (* v1 < v2 *)
  | EJsonOpLe : ejson_op                           (* binary_op_le *)              (* v1 <= v2 *)
  | EJsonOpGt : ejson_op                           (* binary_op_gt *)              (* v1 > v2 *)
  | EJsonOpGe : ejson_op                           (* binary_op_ge *)              (* v1 >= v2 *)
  | EJsonOpAddString : ejson_op                    (* binary_op_add *)             (* v1 + v2 *)
  | EJsonOpAddNumber : ejson_op                    (* binary_op_add *)             (* v1 + v2 *)
  | EJsonOpSub : ejson_op                          (* binary_op_sub *)             (* v1 - v2 *)
  | EJsonOpMult : ejson_op                         (* binary_op_mult *)            (* v1 * v2 *)
  | EJsonOpDiv : ejson_op                          (* binary_op_div *)             (* v1 / v2 *)
  | EJsonOpStrictEqual : ejson_op                  (* binary_op_strict_equal *)    (* v1 === v2 *)
  | EJsonOpStrictDisequal : ejson_op               (* binary_op_strict_disequal *) (* v1 !== v2 *)
  (* Array Stuff *)
  | EJsonOpArray : ejson_op                        (* expr_array *)                (* [ v1, ...vn ] *)
  | EJsonOpArrayLength : ejson_op                  (* expr_member *)               (* v.length *)
  | EJsonOpArrayPush : ejson_op                    (* array_push *)                (* var v' = v.slice(); v'.push(v2) XXX Does not actually claim to be mutable from a semantic stand-point *)
  | EJsonOpArrayAccess : ejson_op                  (* array_get *)                 (* v[i] *)
  (* Object Stuff *)
  | EJsonOpObject : list string -> ejson_op        (* expr_object *)               (* { a1:v1, ...an:vn } *)
  | EJsonOpAccess : string -> ejson_op             (* expr_member *)               (* v['a'] *)
  | EJsonOpHasOwnProperty : string -> ejson_op     (* object_hasOwnProperty *)     (* v.hasOwnProperty('a') *)
  (* Math stuff *)
  | EJsonOpMathMin : ejson_op                      (* expr_call *)                 (* Math.min(e1, e2) *)
  | EJsonOpMathMax : ejson_op                      (* expr_call *)                 (* Math.max(e1, e2) *)
  | EJsonOpMathPow : ejson_op                      (* expr_call *)                 (* Math.pow(e1, e2) *)
  | EJsonOpMathExp : ejson_op                      (* expr_call *)                 (* Math.exp(e) *)
  | EJsonOpMathAbs : ejson_op                      (* expr_call *)                 (* Math.abs(e) *)
  | EJsonOpMathLog : ejson_op                      (* expr_call *)                 (* Math.log2(e) *)
  | EJsonOpMathLog10 : ejson_op                    (* expr_call *)                 (* Math.log10(e) *)
  | EJsonOpMathSqrt : ejson_op                     (* expr_call *)                 (* Math.sqrt(e) *)
  | EJsonOpMathCeil : ejson_op                     (* expr_call *)                 (* Math.ceil(e) *)
  | EJsonOpMathFloor : ejson_op                    (* expr_call *)                 (* Math.floor(e) *)
  | EJsonOpMathTrunc : ejson_op                    (* expr_call *)                 (* Math.trunc(e) *)
  .

  Section Evaluation.
    Context {fejson:foreign_ejson}.

    Definition ejson_op_eval (op:ejson_op) (j:list ejson) : option ejson :=
      match op with
      | EJsonOpNot =>
        match j with
        | [ejbool b] => Some (ejbool (negb b))
        | _ => None
        end
      | EJsonOpNeg =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_neg n))
        | _ => None
        end
      | EJsonOpAnd =>
        match j with
        | [ejbool b1; ejbool b2] => Some (ejbool (andb b1 b2))
        | _ => None
        end
      | EJsonOpOr =>
        match j with
        | [ejbool b1; ejbool b2] => Some (ejbool (orb b1 b2))
        | _ => None
        end
      | EJsonOpLt =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_lt n1 n2))
        | _ => None
        end
      | EJsonOpLe =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_le n1 n2))
        | _ => None
        end
      | EJsonOpGt =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_gt n1 n2))
        | _ => None
        end
      | EJsonOpGe =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejbool (float_ge n1 n2))
        | _ => None
        end
      | EJsonOpAddString =>
        match j with
        | [ejstring s1; ejstring s2] => Some (ejstring (s1 ++ s2))
        | _ => None
        end
      | EJsonOpAddNumber =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_add n1 n2))
        | _ => None
        end
      | EJsonOpSub =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_sub n1 n2))
        | _ => None
        end
      | EJsonOpMult =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_mult n1 n2))
        | _ => None
        end
      | EJsonOpDiv =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_div n1 n2))
        | _ => None
        end
      | EJsonOpStrictEqual =>
        (* XXX Only defined on atomic values, is this right? *)
        match j with
        | [ejnull; ejnull] => Some (ejbool true)
        | [ejbool b1; ejbool b2] => Some (ejbool (if bool_dec b1 b2 then true else false))
        | [ejnumber n1; ejnumber n2] => Some (ejbool (if float_eq_dec n1 n2 then true else false))
        | [ejbigint n1; ejbigint n2] => Some (ejbool (if Z.eq_dec n1 n2 then true else false))
        | [ejstring s1; ejstring s2] => Some (ejbool (if string_dec s1 s2 then true else false))
        | _ => Some (ejbool false)
        end
      | EJsonOpStrictDisequal =>
        (* XXX Only defined on atomic values, is this right? *)
        match j with
        | [ejnull; ejnull] => Some (ejbool false)
        | [ejbool b1; ejbool b2] => Some (ejbool (if bool_dec b1 b2 then false else true))
        | [ejnumber n1; ejnumber n2] => Some (ejbool (if float_eq_dec n1 n2 then false else true))
        | [ejbigint n1; ejbigint n2] => Some (ejbool (if Z.eq_dec n1 n2 then false else true))
        | [ejstring s1; ejstring s2] => Some (ejbool (if string_dec s1 s2 then false else true))
        | _ => Some (ejbool false)
        end
      | EJsonOpArray => Some (ejarray j)
      | EJsonOpArrayLength =>
        match j with
        | [ejarray ja] => Some (ejbigint (Z_of_nat (List.length ja)))
        | _ => None
        end
      | EJsonOpArrayPush =>
        match j with
        | [ejarray ja; je] => Some (ejarray (ja ++ [je]))
        | _ => None
        end
      | EJsonOpArrayAccess =>
        match j with
        | [ejarray ja; ejbigint n] =>
          let natish := ZToSignedNat n in
          if (fst natish) then
            match List.nth_error ja (snd natish) with
            | None => None
            | Some d => Some d
            end
          else None
        | _ => None
        end
      | EJsonOpObject atts =>
        lift ejobject (zip atts j)
      | EJsonOpAccess att =>
        match j with
        | [ejobject jl] =>
          edot jl att
        | _ => None
        end
      | EJsonOpHasOwnProperty a =>
        match j with
        | [ejobject jl] =>
          if in_dec string_dec a (domain jl)
          then Some (ejbool true)
          else Some (ejbool false)
        | _ => None
        end
      | EJsonOpMathMin =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_min n1 n2))
        | _ => None
        end
      | EJsonOpMathMax =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_max n1 n2))
        | _ => None
        end
      | EJsonOpMathExp =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_exp n))
        | _ => None
        end
      | EJsonOpMathPow =>
        match j with
        | [ejnumber n1; ejnumber n2] => Some (ejnumber (float_pow n1 n2))
        | _ => None
        end
      | EJsonOpMathAbs =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_absolute n))
        | _ => None
        end
      | EJsonOpMathLog =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_log n))
        | _ => None
        end
      | EJsonOpMathLog10 =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_log10 n))
        | _ => None
        end
      | EJsonOpMathSqrt =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_sqrt n))
        | _ => None
        end
      | EJsonOpMathCeil =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_ceil n))
        | _ => None
        end
      | EJsonOpMathFloor =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_floor n))
        | _ => None
        end
      | EJsonOpMathTrunc =>
        match j with
        | [ejnumber n] => Some (ejnumber (float_of_int (float_truncate n))) (* XXX yields a number to be consistent with JS semantics *)
        | _ => None
        end
      end.
  End Evaluation.

End EJsonOperators.
