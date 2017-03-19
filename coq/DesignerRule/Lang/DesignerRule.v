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

(* This file defines  *)
Section DesignerRule.

  (* begin hide *)
  Require Import Utils BasicRuntime.
  Require Export CAMP.
  (* end hide *)

  Context {fruntime:foreign_runtime}.

  Axiom designer_rule : Set.
  Axiom designer_rule_to_camp : designer_rule -> pat.
  
End DesignerRule.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
