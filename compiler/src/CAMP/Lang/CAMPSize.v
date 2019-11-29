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

Require Import Omega.
Require Import CommonRuntime.
Require Import CAMP.

Section CAMPSize.
  Context {fruntime:foreign_runtime}.

  Fixpoint camp_size (p:camp) : nat
    := match p with
         | pconst d' => 1
         | punop op p₁ => S (camp_size p₁)
         | pbinop op p₁ p₂ => S (camp_size p₁ + camp_size p₂)
         | pmap p₁ => S (camp_size p₁)
         | passert p₁ => S (camp_size p₁)
         | porElse p₁ p₂ => S (camp_size p₁ + camp_size p₂)
         | pit => 1
         | pletIt p₁ p₂ => S (camp_size p₁ + camp_size p₂)
         | pgetConstant _ => 1
         | penv => 1
         | pletEnv p₁ p₂ => S (camp_size p₁ + camp_size p₂)
         | pleft => 1
         | pright => 1
       end.

  Lemma camp_size_nzero (a:camp) : camp_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.

End CAMPSize.

