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
Require Import Utils.
Require Import CommonRuntime.

Delimit Scope data_scope with data.

Notation "⊥" := (dunit) : data_scope. (* null value *)

Notation "[||]" := (drec nil) : data_scope. (* records *)
Notation "[| x1 ; .. ; xn |]" := (drec (cons x1 .. (cons xn nil) ..)) : data_scope.

Notation "{||}" := (dcoll nil) : data_scope. (* collections *)
Notation "{| x1 ; .. ; xn |}" := (dcoll (cons x1 .. (cons xn nil) ..)) : data_scope.

Require Import String ZArith.
Require Import NRAEnvRuntime.
Require Import cNRAEnv.
Require Import TrivialModel.

Section NRAEnvTest.
  Open Scope Z_scope.

  Local Open Scope string_scope.
  Local Open Scope nraenv_core_scope.
  Local Open Scope data_scope.

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

  Example db1
    := dcoll
         ([| ("A", dconst 1); ("B", dconst 3) |]
            :: [| ("A", dconst 1); ("B", dconst 5) |]
            :: [| ("A", dconst 2); ("B", dconst 7) |]
            :: [| ("A", dconst 4); ("B", dconst 5) |]
            :: nil).
  
  Example db2
    := dcoll
         ([| ("A", dconst 1); ("C", dconst 13) |]
            :: [| ("A", dconst 2); ("C", dconst 15) |]
            :: [| ("A", dconst 3); ("C", dconst 17) |]
            :: [| ("A", dconst 4); ("C", dconst 15) |]
            :: nil).

  Example natural_join :=
    NRAEnvNaturalJoin (NRAEnvConst db1) (NRAEnvConst db2).
  
  (* Eval vm_compute in
     (nraenv_eval_top nil natural_join nil). *)

End NRAEnvTest.

