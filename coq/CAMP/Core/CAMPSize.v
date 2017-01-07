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

Section CAMPSize.
  Require Import Omega.
  Require Import BasicRuntime CAMP.

  Context {fruntime:foreign_runtime}.

  Fixpoint pat_size (p:pat) : nat
    := match p with
         | pconst d' => 1
         | punop op p₁ => S (pat_size p₁)
         | pbinop op p₁ p₂ => S (pat_size p₁ + pat_size p₂)
         | pmap p₁ => S (pat_size p₁)
(*       | pgroupBy p₁ => S (pat_size p₁) *)
         | passert p₁ => S (pat_size p₁)
         | porElse p₁ p₂ => S (pat_size p₁ + pat_size p₂)
         | pit => 1
         | pletIt p₁ p₂ => S (pat_size p₁ + pat_size p₂)
         | pgetconstant _ => 1
         | penv => 1
         | pletEnv p₁ p₂ => S (pat_size p₁ + pat_size p₂)
         | pleft => 1
         | pright => 1
       end.

  Lemma pat_size_nzero (a:pat) : pat_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.

End CAMPSize.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
