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

(** This modules defines conversions between numbers and strings. This
relies on an intermediate representation of numbers in base 'n'. The
main use for this is when defining fresh names. *)

Require Import Ascii.
Require Import String.
Require Import ZArith.
Require Import Equivalence.
Require Import EquivDec.
Require Import Compare_dec.

Require Import Qcert.Utils.Digits.
Require Import Qcert.Utils.CoqLibAdd.
Require Import Qcert.Utils.Float.
Require Import Qcert.Utils.StringAdd.

(** * Preliminaries *)

Section ToString.
  Local Open Scope string.

  Definition boolToString (b:bool) : string
    := if b then "true" else "false".

  Definition quote_char (a:ascii)
    := match a with
       | """"%char => "\"""
       | _ => String a EmptyString
       end.

  Definition quote_string (s:string)
    := flat_map_string quote_char s.

  Definition stringToStringQuote (quotel:string) (s:string)
    := "" ++ quotel ++ "" ++ quote_string s ++ "" ++ quotel ++ "".

  Definition stringToString (s:string) : string
    := s.

  Global Instance ToString_Z : ToString Z
    := { toString := Z_to_string10}.

  Global Instance ToString_nat : ToString nat
    := { toString := nat_to_string10}.

  Global Instance ToString_float : ToString float
    := { toString := float_to_string}.

  Global Instance ToString_bool : ToString bool
    := { toString := boolToString}.
End ToString.
