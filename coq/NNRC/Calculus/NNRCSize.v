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

Section size.
  Require Import Omega.
  Require Import BasicRuntime NNRC.

  Context {fruntime:foreign_runtime}.

  (* Java equivalent: NnrcOptimizer.rew_size.nrc_size *)
  Fixpoint nrc_size (n:nrc) : nat 
    := match n with
         | NRCVar v => 1
         | NRCConst d => 1
         | NRCBinop op n₁ n₂ => S (nrc_size n₁ + nrc_size n₂)
         | NRCUnop op n₁ => S (nrc_size n₁)
         | NRCLet v n₁ n₂ => S (nrc_size n₁ + nrc_size n₂)
         | NRCFor v n₁ n₂ => S (nrc_size n₁ + nrc_size n₂)
         | NRCIf n₁ n₂ n₃ => S (nrc_size n₁ + nrc_size n₂ + nrc_size n₃)
         | NRCEither nd vl nl vr nr => S (nrc_size nd + nrc_size nl + nrc_size nr)
       end.

  Lemma nrc_size_nzero (n:nrc) : nrc_size n <> 0.
  Proof.
    induction n; simpl; omega.
  Qed.

End size.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
