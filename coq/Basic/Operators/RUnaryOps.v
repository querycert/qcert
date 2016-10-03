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

(* Unary operators *)

Section RUnaryOps.

  Require Import String.
  Require Import EquivDec.
  Require Import Utils.
  Require Import BrandRelation.
  Require Import RUtilOps.
  Require Import ForeignData.
  Require Import ForeignOps.

  Context {fdata:foreign_data}.
  Context {fuop:foreign_unary_op}.
  
  Inductive ArithUOp
    := ArithAbs (* Absolute value *) 
     | ArithLog2 (* Base2 logarithm *)
     | ArithSqrt (* square root *)
  .

  Inductive SortDesc
    := Descending | Ascending.

  Definition SortCriteria :=
    list (string * SortDesc).

  Inductive unaryOp : Set :=
  | AIdOp : unaryOp                       (* Identity *)
  | ANeg: unaryOp                         (* boolean negation *)
  | AColl : unaryOp                       (* singleton bag *)
  | ASingleton : unaryOp                  (* un-coll a singleton collectin *)
  | AFlatten : unaryOp                    (* flatten *)
  | ADistinct: unaryOp                    (* distinct *)
  | AOrderBy : SortCriteria -> unaryOp    (* sort returns a sorted collection but no guarantee on how long order is maintained!! *)
  | ARec : string -> unaryOp              (* record construction.  Constructs a record with a single field (the string argument) *)
  | ADot : string -> unaryOp              (* record field access.  Given a record, returns the value associated with the provided field *)
  | ARecRemove : string -> unaryOp        (* record field removal.  Transforms a record by removing the named field *)
  | ARecProject : list string -> unaryOp  (* record field removal.  Transforms a record by removing the named field *)
  | ACount: unaryOp                       (* bag count *)
  | ASum : unaryOp                        (* sum of natural numbers in a bag *)
  | ANumMin : unaryOp                     (* min over a collection of numeric values *)
  | ANumMax : unaryOp                     (* max over a collection of numeric values *)
  | AArithMean : unaryOp                  (* arithmetic mean of natural numbers in a bag *)
  | AToString : unaryOp                   (* data to string.  Important for test cases *)
  | ALeft : unaryOp                       (* create a dleft *)
  | ARight : unaryOp                      (* create a dright *)
  | ABrand : brands -> unaryOp            (* box a branded value *)
  | AUnbrand : unaryOp                    (* un-box a branded value *)
  | ACast : brands -> unaryOp             (* coerce a branded value into sub-brands.   *)
  | AUArith : ArithUOp -> unaryOp         (* Arithmetic operations *)
  | AForeignUnaryOp (fu:foreign_unary_op_type) : unaryOp
  .

  Global Instance ArithUOp_eqdec : EqDec ArithUOp eq.
  Proof.
    change (forall x y : ArithUOp,  {x = y} + {x <> y}).
    decide equality.
  Defined.

  Global Instance SortCriteria_eqdec : EqDec SortCriteria eq.
  Proof.
    change (forall x y : SortCriteria,  {x = y} + {x <> y}).
    decide equality; try apply string_dec.
    decide equality; try apply string_dec.
    decide equality; try apply string_dec.
  Defined.

  Global Instance unaryOp_eqdec : EqDec unaryOp eq.
  Proof.
    change (forall x y : unaryOp,  {x = y} + {x <> y}).
    decide equality; try apply string_dec.
    - apply SortCriteria_eqdec.
    - induction l; decide equality; apply string_dec.
    - induction b; decide equality; apply string_dec.
    - induction b; decide equality; apply string_dec.
    - apply ArithUOp_eqdec.
    - apply foreign_unary_op_dec.
  Defined.

  Local Open Scope string.

  Global Instance ToString_ArithUOp : ToString ArithUOp
    := {toString :=
          fun (op:ArithUOp) =>
            match op with
            | ArithAbs => "ArithAbs"
            | ArithLog2 => "ArithLog2"
            | ArithSqrt => "Sqrt"
            end
       }.

  Definition ToString_SortDesc sd :=
    match sd with
    | Ascending => "asc"
    | Descending => "desc"
    end.
  
  Definition ToString_SortCriteria (sc : string * SortDesc) :=
    let (att,sd) := sc in
    bracketString "(" (att ++ "," ++ (ToString_SortDesc sd)) ")".
  
  Global Instance ToString_unaryOp : ToString unaryOp
    := {toString :=
          fun (op:unaryOp) =>
            match op with
            | AIdOp => "AIdOp"
            | ANeg => "ANeg"
            | AColl => "AColl"
            | ASingleton => "ASingleton"
            | AFlatten => "AFlatten"
            | ADistinct => "ADistinct"
            | AOrderBy ls =>
              "(AOrderBy"
                ++ (bracketString "[" (joinStrings "," (List.map ToString_SortCriteria ls)) "]")
                ++ ")"
            | ARec f => "(ARec " ++ f ++ ")"
            | ADot s => "(ADot " ++ s ++ ")"
            | ARecRemove s => "(ArecRemove " ++ s ++ ")"
            | ARecProject ls => "(ARecProject "
                                  ++ (bracketString "[" (joinStrings "," ls) "]")
                                  ++ ")"
            | ACount => "ACount"
            | ASum => "ASum"
            | ANumMin => "ANumMin"
            | ANumMax => "ANumMax"
            | AArithMean => "AArithMean"
            | AToString => "AToString"
            | ALeft => "ALeft"
            | ARight => "ARight"
            | ABrand b => "(ABrand " ++ (@toString _ ToString_brands b)++ ")"
            | AUnbrand => "AUnbrand"
            | ACast b => "(ACast " ++ (@toString _ ToString_brands b) ++ ")"
            | AUArith aop => "(AUArith " ++ toString aop ++ ")"
            | AForeignUnaryOp fu => toString fu
          end
     }.

End RUnaryOps.

Require Import String RUtil.

Tactic Notation "unaryOp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AIdOp"%string
  | Case_aux c "ANeg"%string
  | Case_aux c "AColl"%string
  | Case_aux c "ASingleton"%string
  | Case_aux c "AFlatten"%string
  | Case_aux c "ADistinct"%string
  | Case_aux c "AOrderBy"%string
  | Case_aux c "ARec"%string
  | Case_aux c "ADot"%string
  | Case_aux c "ARecRemove"%string
  | Case_aux c "ARecProject"%string
  | Case_aux c "ACount"%string
  | Case_aux c "ASum"%string
  | Case_aux c "ANumMin"%string
  | Case_aux c "ANumMax"%string
  | Case_aux c "AArithMean"%string
  | Case_aux c "AToString"%string
  | Case_aux c "ALeft"%string
  | Case_aux c "ARight"%string
  | Case_aux c "ABrand"%string
  | Case_aux c "AUnbrand"%string
  | Case_aux c "ACast"%string 
  | Case_aux c "AUArith"%string
  | Case_aux c "AForeignUnaryOp"%string
  ].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)