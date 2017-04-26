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

Section NRASugar.
  Require Import String List Compare_dec.
  Require Import EquivDec.
  
  Require Import Utils BasicRuntime.
  Require Import NRA.

  (* Some macros used by extended algebras and patterns *)

  Context {fruntime:foreign_runtime}.

  Open Scope string_scope.

  Definition nra_bind := AUnop (ADot "PBIND") AID.
  Definition nra_const_env := AUnop (ADot "PCONST") AID.
  Definition nra_data := AUnop (ADot "PDATA") AID.
  Definition nra_data_op op := AUnop (ADot "PDATA") op.

  (* Match failure returns the empty sequence, success returns a singleton sequence *)
  Definition nra_fail := AConst (dcoll nil).
  Definition nra_match op := AUnop AColl op.
  Definition nra_triple s1 s2 s3 (aconst:nra) (abind:nra) (adata:nra) :=
    ABinop AConcat
           (AUnop (ARec s1) aconst)
           (ABinop AConcat
                   (AUnop (ARec s2) abind)
                   (AUnop (ARec s3) adata)).
  
  Definition nra_context (aconst:nra) (abind:nra) (adata:nra) :=
    nra_triple "PCONST" "PBIND" "PDATA"  aconst abind adata.
  
  Definition nra_withbinding :=
    nra_context nra_const_env nra_bind nra_bind.
  
  Definition nra_context_data dconst dbind dpid : data :=
    drec (("PBIND",dbind)
            ::("PCONST",dconst)
            ::("PDATA",dpid)
            :: nil).

  (* Variant used in context *)
  Definition make_fixed_nra_context_data (const:data) (env:data) : nra
    := ABinop AConcat
              (AUnop (ARec "PBIND"%string) (AConst env))
              (ABinop AConcat
                      (AUnop (ARec "PCONST"%string) (AConst const))
                      (AUnop (ARec "PDATA"%string) AID)).

  Definition nra_wrap op  :=
    nra_triple "PCONST" "PBIND" "PDATA" nra_const_env nra_bind op.
  
  Definition nra_wrap_a1 op :=
    nra_triple "PCONST" "PBIND" "a1" nra_const_env nra_bind op.

  Definition nra_wrap_bind_a1 op :=
    nra_triple "PCONST" "a1" "PDATA" nra_const_env  nra_bind op.

  Definition nra_wrap_with_bind op1 :=
    nra_context nra_const_env op1 AID.
  
  Definition nra_project_wrap :=
    nra_wrap_with_bind nra_fail.

  Lemma data_normalized_nra_context_data h constants env d:
    data_normalized h constants ->
    data_normalized h env ->
    data_normalized h d ->
    data_normalized h (nra_context_data constants env d).
  Proof.
    unfold nra_context_data.
    repeat (constructor; simpl; eauto).
  Qed.

  Lemma data_normalized_nra_context_data_inv h constants env d:
    data_normalized h (nra_context_data constants env d) ->
     data_normalized h constants /\
    data_normalized h env /\
    data_normalized h d.
  Proof.
    unfold nra_context_data.
    intros H.
    inversion H; clear H; subst.
    inversion H1; clear H1; subst.
    inversion H4; clear H4; subst.
    inversion H5; clear H5; subst.
    tauto.
  Qed.

End NRASugar.

Hint Resolve data_normalized_nra_context_data.  
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
