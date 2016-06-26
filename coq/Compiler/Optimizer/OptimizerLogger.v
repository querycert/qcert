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

Section OptimizerLogger.

  Require Import String List.

  Class optimizer_logger (Name:Set) (D:Set) 
    := mk_optimizer_logger {
           optimizer_logger_token_type:Set
           ; logStartPass (name:Name) (input:D) : optimizer_logger_token_type
           ; logStep (t:optimizer_logger_token_type) (name:Name) (input output:D) :
               optimizer_logger_token_type
           ; logEndPass (t:optimizer_logger_token_type) (output:D):
               optimizer_logger_token_type
         }.

  Definition optimizer_step
             {Name D} {logger:optimizer_logger Name D}
             (step:Name*(D->D)) (input:optimizer_logger_token_type*D)
    : optimizer_logger_token_type*D
    := let res := (snd step) (snd input) in
       let log := logStep (fst input) (fst step) (snd input) res in
       (log, res).

  Lemma optimizer_step_result
         {Name D} {logger:optimizer_logger Name D}
         (step:Name*(D->D)) (input:optimizer_logger_token_type*D) :
    snd (optimizer_step step input) = (snd step) (snd input).
  Proof.
    unfold optimizer_step.
    simpl; reflexivity.
  Qed.

  (* This it to try and ``trick'' the system so that 
     the evaluation is extracted and run for its effects
    *)
  Definition hide_use {A B} (x:A) (y:B) := y.
  Lemma hide_use_eq {A B} (x:A) (y:B) : hide_use x y = y.
  Proof.
    reflexivity.
  Qed.
  Opaque hide_use.
  
  Definition apply_steps {Name D} {logger:optimizer_logger Name D}
             (name:Name)
              (l:list (Name*(D->D))) (p:D)
    := let tok := logStartPass name p in
       let res := fold_right optimizer_step (tok,p) l in
       let tok := logEndPass (fst res) (snd res) in
       hide_use tok (snd res).

  Instance silent_optimizer_logger (Name:Set) (D:Set) : optimizer_logger Name D
    :=
    {
      optimizer_logger_token_type := bool
      ; logStartPass name input := true
      ; logStep t name input output := t
      ; logEndPass t output := t
    } .
       
End OptimizerLogger.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
