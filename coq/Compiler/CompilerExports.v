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

(* Compiler Top *)
Require Export EnhancedCompiler EnhancedModel.
Require Export QDriver.
Module Export CD := QDriver EnhancedModel.EnhancedRuntime.

Export EnhancedCompiler.QEval.
Export CompEnhanced.
Export Enhanced.Data Enhanced.Ops.Unary Enhanced.Ops.Binary.

(* Some core Coq libraries and notations *)
Require Export ZArith.
Open Scope Z_scope.
Require Export String.
Open Scope string_scope.
Require Export List.
Export ListNotations.

(* Some additional modules, notably rules and notations *)
Require Export Utils CommonSystem.
Require Export CAMPRule CAMPRuleSugar CompEnv.
Open Scope camp_scope.

