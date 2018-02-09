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

(* Utilities methods used for defining the semantics of the operators *)

Section OperatorsUtils.
  Require Import String.
  Require Import List.
  Require Import Utils.
  Require Import ZArith.
  Require Import BrandRelation.
  Require Import ForeignData.
  Require Import Data.
  Require Import DataLift.
  Require Import Iterators.
  Require Import JsAst.JsNumber.

  Import ListNotations.

  Context {fdata:foreign_data}.

  Definition boolToString (b:bool) : string
    := if b then "TRUE"%string else "FALSE"%string.

  Definition bracketString (open s close:string)
    := append open (append s close).

  Definition stringToString (s:string) : string
(*    := bracketString "'"%string s "'"%string. *)
    := s.

  Definition string_sort := insertion_sort StringOrder.le_dec.

  Global Instance ToString_Z : ToString Z
    := { toString := Z_to_string10}.

  Global Instance ToString_nat : ToString nat
    := { toString := nat_to_string10}.

  Global Instance ToString_number : ToString number
    := { toString := to_string}.

  Global Instance ToString_bool : ToString bool
    := { toString := boolToString}.

  Instance ToString_brands : ToString brands
    := { toString := fun b => (joinStrings " & " b)}.
    
  Fixpoint dataToString (d:data) : string
    := match d with
           | dunit => "UNIT"%string
           | dnat n => toString n
           | dnumber n => toString n
           | dbool b => toString b
           | dstring s => stringToString s
           | dcoll l => bracketString 
                          "["%string
                          (joinStrings ", "
                                       (string_sort (map dataToString l)))
                          "]"%string
           | drec lsd => bracketString
             "{"%string
                (joinStrings "," 
                             (map (fun xy => let '(x,y):=xy in 
                                             (append (stringToString x) (append "->"%string
                                             (dataToString y)))
                                  ) lsd))
                "}"%string
           | dleft d => bracketString
                          "Left("%string
                          (dataToString d)
                          ")"%string
           | dright d => bracketString
                          "Right("%string
                          (dataToString d)
                          ")"%string
           | dbrand b d => (bracketString
                              "<"
                              (append (@toString _ ToString_brands b)
                                      (append ":" (dataToString d)))
                              ">")
           | dforeign fd => toString fd
       end.

  Global Instance ToString_data : ToString data
    := { toString := dataToString}.
  
  Fixpoint dsum (ns:list data) : option Z
    := match ns with
         | nil => Some 0%Z
         | dnat n::ls => lift (Zplus n) (dsum ls)
         | _ => None
       end.

  Definition darithmean (ns:list data) : option Z
    := match ns with
         | nil  => Some (0%Z)
         | _ => lift (fun x => Z.quot x (Z_of_nat (length ns))) (dsum ns)
       end.

  Definition lifted_zbag (l : list data) : option (list Z) :=
    lift_map (ondnat (fun x => x)) l.
  Definition lifted_min (l : list data) : option data :=
    lift dnat (lift bnummin (lifted_zbag l)).
  Definition lifted_max (l : list data) : option data :=
    lift dnat (lift bnummax (lifted_zbag l)).

End OperatorsUtils.

