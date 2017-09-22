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

(* Notations *)

Require Import List.
Require Import Utils CommonRuntime.

Delimit Scope data_scope with data.

Notation "⊥" := (dunit) : data_scope. (* null value *)

Notation "[||]" := (drec nil) : data_scope. (* records *)
Notation "[| x1 ; .. ; xn |]" := (drec (cons x1 .. (cons xn nil) ..)) : data_scope.

Notation "{||}" := (dcoll nil) : data_scope. (* collections *)
Notation "{| x1 ; .. ; xn |}" := (dcoll (cons x1 .. (cons xn nil) ..)) : data_scope.

Section NRAEnvTest.
  Require Import String ZArith.
  Open Scope Z_scope.

  Require Import NRAEnvRuntime.
  Require Import cNRAEnv.

  Local Open Scope string_scope.
  Local Open Scope nraenv_core_scope.
  Local Open Scope data_scope.
  Require Import TrivialModel.


  Example merge_env_example
    := [| ("A", dconst 1); ("B", dconst 3) |].
  
  Example merge_succeeds : nraenv_core
    := χᵉ⟨ (ENV·"A") ♯+ (ENV·"C") ⟩ ◯ₑ (ENV ⊗ ‵ [| ("B", dconst 3) ; ("C", dconst 4) |]).

  Remark merge_succeeds_result :
    nil ⊢ₑ merge_succeeds @ₑ dunit ⊣ nil ; merge_env_example =
                                           Some {| dconst 5 |}.
  Proof. reflexivity. Qed.

  Example merge_fails : nraenv_core
    := χᵉ⟨ (ENV·"A") ♯+ (ENV·"C") ⟩ ◯ₑ (ENV ⊗ ‵ [| ("B", dconst 2) ; ("C", dconst 4) |]).

  Remark merge_fails_result :
    nil ⊢ₑ merge_fails @ₑ dunit ⊣ nil ; merge_env_example =
                                           Some {||}.
  Proof. reflexivity. Qed.

End NRAEnvTest.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
