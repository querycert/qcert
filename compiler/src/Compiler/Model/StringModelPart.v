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

Require Extraction.
Require String.

(** Defines the foreign support for a native string type.
     Posits axioms for the basic data/operators, and 
     defines how they are extracted to ocaml (using helper functions
     defined in qcert/compiler/utils/Util.ml)
     *)

Axiom STRING : Set.

Axiom STRING_eq : STRING -> STRING -> bool.
Conjecture STRING_eq_correct :
  forall f1 f2, (STRING_eq f1 f2 = true <-> f1 = f2).

Axiom STRING_tostring : STRING -> String.string.

Extract Constant STRING => "string".
Extract Inlined Constant STRING_eq => "(fun x y -> x = y)".
Extract Inlined Constant STRING_tostring => "(fun x -> QcertUtils.Util.char_list_of_string x)".

