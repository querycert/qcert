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

(* Qcert Compiler Extraction *)

(* Configuration of the extraction *)

Require Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt ExtrOcamlZInt.
Require Import ExtrOcamlFloatNatIntZInt.
Extraction Blacklist String List.

Require Import Digits.
Require Import TechRule DesignerRule.

Extract Constant Digits.nat_to_string10 => "(fun x -> Util.char_list_of_string (string_of_int x))".

Extract Constant TechRule.tech_rule => "camp_rule".
Extract Constant DesignerRule.designer_rule => "camp_rule".
Extract Constant TechRule.tech_rule_to_camp_rule => "(fun fruntime x -> x)".
Extract Constant DesignerRule.designer_rule_to_camp_rule => "(fun fruntime x -> x)".

(* Qcert modules *)

Require EnhancedCompiler.

Extraction "QcertCompiler" EnhancedCompiler.EnhancedCompiler.

