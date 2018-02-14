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

Section UnaryOperators.
  Require Import Ascii.
  Require Import String.
  Require Import ZArith.
  Require Import EquivDec.
  Require Import Utils.
  Require Import BrandRelation.
  Require Import ForeignData.
  Require Import DataSort.
  Require Import ForeignOperators.
  Require Import OperatorsUtils.

  Context {fdata:foreign_data}.
  Context {fuop:foreign_unary_op}.
  
  Inductive nat_arith_unary_op
    := NatAbs  (**r absolute value *) 
     | NatLog2 (**r base2 logarithm *)
     | NatSqrt (**r square root *)
  .
  Inductive number_arith_unary_op
    := NumberNeg   (**r negative *)
     | NumberSqrt  (**r square root *)
     | NumberExp   (**r exponent *)
     | NumberLog   (**r logarithm base 2 *)
     | NumberLog10 (**r logarithm base 10 *)
     | NumberCeil  (**r ceiling *)
     | NumberFloor (**r floor *)
     | NumberAbs   (**r absolute value *)
  .

  Inductive unary_op : Set :=
  | OpIdentity : unary_op                             (**r identity, returns its value *)
  | OpNeg : unary_op                                  (**r boolean negation *)
  | OpRec : string -> unary_op                        (**r create a record with a single field *)
  | OpDot : string -> unary_op                        (**r record field access *)
  | OpRecRemove : string -> unary_op                  (**r record remove the given fields *)
  | OpRecProject : list string -> unary_op            (**r record projects on the given fields *)
  | OpBag : unary_op                                  (**r create a singleton bag *)
  | OpSingleton : unary_op                            (**r value within a singleton bag *)
  | OpFlatten : unary_op                              (**r flattens a bag of bags *)
  | OpDistinct: unary_op                              (**r distinct values in a bag *)
  | OpOrderBy : SortCriterias -> unary_op             (**r sorts a collection of records *)
  | OpCount : unary_op                                (**r bag count *)
  | OpToString : unary_op                             (**r convert any data to a string *)
  | OpSubstring : Z -> option Z -> unary_op           (**r returns the substring starting with the nth character, for m characters (or the rest of the string) *)
  | OpLike (pattern:string)
              (escape:option ascii) : unary_op        (**r like expression (as in sql) *)
  | OpLeft : unary_op                                 (**r create a left value *)
  | OpRight : unary_op                                (**r create a right value *)
  | OpBrand : brands -> unary_op                      (**r brands a value *)
  | OpUnbrand : unary_op                              (**r content of a branded value *)
  | OpCast : brands -> unary_op                       (**r coerce a branded value into one of its sub-brands *)
  | OpNatUnary : nat_arith_unary_op -> unary_op       (**r arithmetic operations on natural numbers *)
  | OpNatSum : unary_op                               (**r sum of natural numbers in a bag *)
  | OpNatMin : unary_op                               (**r minimum of natural numbers in a bag *)
  | OpNatMax : unary_op                               (**r maximum of natural numbers in a bag *)
  | OpNatMean : unary_op                              (**r arithmetic mean of natural numbers in a bag *)
  | OpNumberOfNat : unary_op                          (**r coercion from natural number to float *)
  | OpNumberUnary : number_arith_unary_op -> unary_op (**r arithmetic operations on floats *)
  | OpNumberTruncate : unary_op                       (**r truncate *)
  | OpNumberSum : unary_op                            (**r sum *) 
  | OpNumberMean : unary_op                           (**r arithmetic mean *)
  | OpNumberBagMin : unary_op                         (**r minimum *)
  | OpNumberBagMax : unary_op                         (**r maximum *)
  | OpForeignUnary
      (fu:foreign_unary_op_type) : unary_op           (**r foreign unary operators *)
  .

  Global Instance nat_arith_unary_op_eqdec : EqDec nat_arith_unary_op eq.
  Proof.
    change (forall x y : nat_arith_unary_op,  {x = y} + {x <> y}).
    decide equality.
  Defined.

  Global Instance number_arith_unary_op_eqdec : EqDec number_arith_unary_op eq.
  Proof.
    change (forall x y : number_arith_unary_op,  {x = y} + {x <> y}).
    decide equality.
  Defined.

  Global Instance SortCriterias_eqdec : EqDec SortCriterias eq.
  Proof.
    change (forall x y : SortCriterias,  {x = y} + {x <> y}).
    decide equality; try apply string_dec.
    decide equality; try apply string_dec.
    decide equality; try apply string_dec.
  Defined.

  Global Instance unary_op_eqdec : EqDec unary_op eq.
  Proof.
    change (forall x y : unary_op,  {x = y} + {x <> y}).
    decide equality; try apply string_dec.
    - induction l; decide equality; apply string_dec.
    - apply SortCriterias_eqdec.
    - apply option_eqdec.
    - apply Z_eqdec.
    - apply equiv_dec.
    - induction b; decide equality; apply string_dec.
    - induction b; decide equality; apply string_dec.
    - apply nat_arith_unary_op_eqdec.
    - apply number_arith_unary_op_eqdec.
    - apply foreign_unary_op_dec.
  Defined.

  Local Open Scope string.

  Global Instance ToString_nat_arith_unary_op : ToString nat_arith_unary_op
    := {toString :=
          fun (op:nat_arith_unary_op) =>
            match op with
            | NatAbs => "NatAbs"
            | NatLog2 => "NatLog2"
            | NatSqrt => "NatSqrt"
            end
       }.

  Global Instance ToString_number_arith_unary_op : ToString number_arith_unary_op
    := {toString :=
          fun (op:number_arith_unary_op) =>
            match op with
            | NumberNeg => "NumberNeg"
            | NumberSqrt => "NumberSqrt"
            | NumberExp => "NumberExp"
            | NumberLog => "NumberLog"
            | NumberLog10 => "NumberLog10"
            | NumberCeil => "NumberCeil"
            | NumberFloor => "NumberFloor"
            | NumberAbs => "NumberAbs"
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
  
  Global Instance ToString_unary_op : ToString unary_op
    := {toString :=
          fun (op:unary_op) =>
            match op with
            | OpIdentity => "OpIdentity"
            | OpNeg => "OpNeg"
            | OpRec f => "(OpRec " ++ f ++ ")"
            | OpDot s => "(OpDot " ++ s ++ ")"
            | OpRecRemove s => "(OpRecRemove " ++ s ++ ")"
            | OpRecProject ls => "(OpRecProject "
                                      ++ (bracketString "[" (joinStrings "," ls) "]")
                                      ++ ")"
            | OpBag => "OpBag"
            | OpSingleton => "OpSingleton"
            | OpFlatten => "OpFlatten"
            | OpDistinct => "OpDistinct"
            | OpOrderBy ls =>
              "(OpOrderBy"
                ++ (bracketString "[" (joinStrings "," (List.map ToString_SortCriteria ls)) "]")
                ++ ")"
            | OpCount => "OpCount"
            | OpToString => "OpToString"
            | OpSubstring start len =>
              "(OpSubstring " ++ (toString start)
                                 ++ (match len with
                                     | None => ""
                                     | Some len => " " ++ (toString len)
                                     end
                                    ) ++ ")"
            | OpLike pattern oescape =>
              "(OpLike " ++ pattern
                            ++ (match oescape with
                                | None => ""
                                | Some escape => " ESCAPE " ++ (String escape EmptyString)
                                end
                               ) ++ ")"
            | OpLeft => "OpLeft"
            | OpRight => "OpRight"
            | OpBrand b => "(OpBrand " ++ (@toString _ ToString_brands b)++ ")"
            | OpUnbrand => "OpUnbrand"
            | OpCast b => "(OpCast " ++ (@toString _ ToString_brands b) ++ ")"
            | OpNatUnary aop => "(OpNatUnary " ++ toString aop ++ ")"
            | OpNatSum => "OpNatSum"
            | OpNatMin => "OpNatMin"
            | OpNatMax => "OpNatMax"
            | OpNatMean => "OpNatMean"
            | OpNumberOfNat => "OpNumberOfNat"
            | OpNumberUnary aop => "(OpNumberUnary " ++ toString aop ++ ")"
            | OpNumberTruncate => "OpNumberTruncate"
            | OpNumberSum => "OpNumberSum"
            | OpNumberMean => "OpNumberMean"
            | OpNumberBagMin => "OpNumberBagMin"
            | OpNumberBagMax => "OpNumberBagMax"
            | OpForeignUnary fu => toString fu
            end
       }.

End UnaryOperators.

Tactic Notation "unary_op_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "OpIdentity"%string
  | Case_aux c "OpNeg"%string
  | Case_aux c "OpRec"%string
  | Case_aux c "OpDot"%string
  | Case_aux c "OpRecRemove"%string
  | Case_aux c "OpRecProject"%string
  | Case_aux c "OpBag"%string
  | Case_aux c "OpSingleton"%string
  | Case_aux c "OpFlatten"%string
  | Case_aux c "OpDistinct"%string
  | Case_aux c "OpOrderBy"%string
  | Case_aux c "OpCount"%string
  | Case_aux c "OpToString"%string
  | Case_aux c "OpSubstring"%string
  | Case_aux c "OpLike"%string
  | Case_aux c "OpLeft"%string
  | Case_aux c "OpRight"%string
  | Case_aux c "OpBrand"%string
  | Case_aux c "OpUnbrand"%string
  | Case_aux c "OpCast"%string 
  | Case_aux c "OpNatUnary"%string
  | Case_aux c "OpNatSum"%string
  | Case_aux c "OpNatMin"%string
  | Case_aux c "OpNatMax"%string
  | Case_aux c "OpNatMean"%string
  | Case_aux c "OpNumberOfNat"%string
  | Case_aux c "OpNumberUnary"%string
  | Case_aux c "OpNumberTruncate"%string
  | Case_aux c "OpNumberSum"%string
  | Case_aux c "OpNumberMean"%string
  | Case_aux c "OpNumberBagMin"%string
  | Case_aux c "OpNumberBagMax"%string
  | Case_aux c "OpForeignUnary"%string
  ].

