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

Require Import List.
Require Import String.
Require Import Utils.
Require Import ZArith.
Require Import BrandRelation.
Require Import ForeignData.
Require Import Data.
Require Import DataLift.
Require Import Iterators.

Section OperatorsUtils.
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

  Global Instance ToString_float : ToString float
    := { toString := float_to_string}.

  Global Instance ToString_bool : ToString bool
    := { toString := boolToString}.

  Instance ToString_brands : ToString brands
    := { toString := fun b => (concat " & " b)}.

  Fixpoint dsum (ns:list data) : option Z
    := match ns with
         | nil => Some 0%Z
         | dnat n::ls => lift (Zplus n) (dsum ls)
         | _ => None
       end.

  Definition darithmean (ns:list data) : option Z
    := match ns with
         | nil  => Some (0%Z)
         | _ => lift (fun x => Z.quot x (Z_of_nat (List.length ns))) (dsum ns)
       end.

  Definition lifted_stringbag (l : list data) : option (list string) :=
    lift_map (ondstring (fun x => x)) l.
  Definition lifted_zbag (l : list data) : option (list Z) :=
    lift_map (ondnat (fun x => x)) l.
  Definition lifted_min (l : list data) : option data :=
    lift dnat (lift bnummin (lifted_zbag l)).
  Definition lifted_max (l : list data) : option data :=
    lift dnat (lift bnummax (lifted_zbag l)).

  Definition lifted_fbag (l : list data) : option (list float) :=
    lift_map (ondfloat (fun x => x)) l.

  Definition lifted_fsum (l:list data) : option data :=
    lift dfloat (lift float_list_sum (lifted_fbag l)).
  Definition lifted_farithmean (l:list data) : option data :=
    lift dfloat (lift float_list_arithmean (lifted_fbag l)).
  Definition lifted_fmin (l : list data) : option data :=
    lift dfloat (lift float_list_min (lifted_fbag l)).
  Definition lifted_fmax (l : list data) : option data :=
    lift dfloat (lift float_list_max (lifted_fbag l)).

  Definition lifted_join (sep : string) (l : list data) : option data :=
    lift dstring (lift (concat sep) (lifted_stringbag l)).

End OperatorsUtils.

