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

Require Import CompilerRuntime.
Module Compiler (runtime:CompilerRuntime).

  Require CompData CompOperators.
  Require CompOQL CompLambdaNRA CompPattern CompRule CompEnv.
  Require CompDriver CompUtil CompType EvalTop.

  Module RType := CompType.CompType runtime.
  Module Data := CompData.CompData runtime.
  Module Ops := CompOperators.CompOperators runtime.

  Module OQL := CompOQL.CompOQL runtime.
  Module LambdaNRA := CompLambdaNRA.CompLambdaNRA runtime.
  Module Pattern := CompPattern.CompPattern runtime.
  Module Rule := CompRule.CompRule runtime.

  Module CompDriver := CompDriver.CompDriver runtime.
  Module CompUtil := CompUtil.CompUtil runtime.

  Module EvalTop := EvalTop.EvalTop runtime.

End Compiler.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
