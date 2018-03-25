(*
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

Require Import Qcert.Compiler.Driver.CompLang.
Require Import Qcert.Compiler.EnhancedCompiler.

Section HelloWorld.
  Definition bm := EnhancedCompiler.QType.empty_brand_model tt eq_refl.

  Definition config := @EnhancedCompiler.QDriver.default_dv_config bm.
  Definition source := L_nraenv.
  Definition target := L_javascript.

  Definition compile : query -> query :=
    @EnhancedCompiler.QDriver.compile_from_source_target bm _ config source target.

  Section example.
    Require Import String.
    Require Import Qcert.Common.Data.Data.
    Require Import Qcert.NRAEnv.Lang.NRAEnv.
  
    Definition a1 :=
      NRAEnvConst (dstring "Hello World!").

    (* Eval vm_compute in compile (Q_nraenv a1). *)
  End example.

End HelloWorld.

