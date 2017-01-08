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

Section RAlgSugar.
  Require Import String List Compare_dec.
  Require Import EquivDec.
  
  Require Import Utils BasicRuntime.
  Require Import RAlg.

  (* Some macros used by extended algebras and patterns *)

  Context {fruntime:foreign_runtime}.

  Open Scope string_scope.

  Definition pat_bind := AUnop (ADot "PBIND") AID.
  Definition pat_const_env := AUnop (ADot "PCONST") AID.
  Definition pat_data := AUnop (ADot "PDATA") AID.
  Definition pat_data_op op := AUnop (ADot "PDATA") op.

  (* Match failure returns the empty sequence, success returns a singleton sequence *)
  Definition pat_fail := AConst (dcoll nil).
  Definition pat_match op := AUnop AColl op.
  Definition pat_triple s1 s2 s3 (aconst:alg) (abind:alg) (adata:alg) :=
    ABinop AConcat
           (AUnop (ARec s1) aconst)
           (ABinop AConcat
                   (AUnop (ARec s2) abind)
                   (AUnop (ARec s3) adata)).
  
  Definition pat_context (aconst:alg) (abind:alg) (adata:alg) :=
    pat_triple "PCONST" "PBIND" "PDATA"  aconst abind adata.
  
  Definition pat_withbinding :=
    pat_context pat_const_env pat_bind pat_bind.
  
  Definition pat_context_data dconst dbind dpid : data :=
    drec (("PBIND",dbind)
            ::("PCONST",dconst)
            ::("PDATA",dpid)
            :: nil).

  (* Variant used in context *)
  Definition make_fixed_pat_context_data (const:data) (env:data) : alg
    := ABinop AConcat
              (AUnop (ARec "PBIND"%string) (AConst env))
              (ABinop AConcat
                      (AUnop (ARec "PCONST"%string) (AConst const))
                      (AUnop (ARec "PDATA"%string) AID)).

  Definition pat_wrap op  :=
    pat_triple "PCONST" "PBIND" "PDATA" pat_const_env pat_bind op.
  
  Definition pat_wrap_a1 op :=
    pat_triple "PCONST" "PBIND" "a1" pat_const_env pat_bind op.

  Definition pat_wrap_bind_a1 op :=
    pat_triple "PCONST" "a1" "PDATA" pat_const_env  pat_bind op.

  Definition pat_wrap_with_bind op1 :=
    pat_context pat_const_env op1 AID.
  
  Definition pat_project_wrap :=
    pat_wrap_with_bind pat_fail.

  Lemma data_normalized_pat_context_data h constants env d:
    data_normalized h constants ->
    data_normalized h env ->
    data_normalized h d ->
    data_normalized h (pat_context_data constants env d).
  Proof.
    unfold pat_context_data.
    repeat (constructor; simpl; eauto).
  Qed.

  Lemma data_normalized_pat_context_data_inv h constants env d:
    data_normalized h (pat_context_data constants env d) ->
     data_normalized h constants /\
    data_normalized h env /\
    data_normalized h d.
  Proof.
    unfold pat_context_data.
    intros H.
    inversion H; clear H; subst.
    inversion H1; clear H1; subst.
    inversion H4; clear H4; subst.
    inversion H5; clear H5; subst.
    tauto.
  Qed.

End RAlgSugar.

Hint Resolve data_normalized_pat_context_data.  
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
