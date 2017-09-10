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
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import EquivDec.
  Require Import CommonRuntime.
  Require Import NRA.

  (* Some macros used by extended algebras and patterns *)

  Context {fruntime:foreign_runtime}.

  Open Scope string_scope.

  Definition nra_bind := AUnop (OpDot "PBIND") AID.
  Definition nra_data := AUnop (OpDot "PDATA") AID.
  Definition nra_data_op op := AUnop (OpDot "PDATA") op.

  (* Match failure returns the empty sequence, success returns a singleton sequence *)
  Definition nra_fail := AConst (dcoll nil).
  Definition nra_match op := AUnop OpBag op.
  Definition nra_double s1 s2 (abind:nra) (adata:nra) :=
    ABinop OpRecConcat
           (AUnop (OpRec s1) abind)
           (AUnop (OpRec s2) adata).
  
  Definition nra_context (abind:nra) (adata:nra) :=
    nra_double "PBIND" "PDATA" abind adata.
  
  Definition nra_withbinding :=
    nra_context nra_bind nra_bind.
  
  Definition nra_context_data dbind dpid : data :=
    drec (("PBIND",dbind)
            ::("PDATA",dpid)
            :: nil).

  (* Variant used in context *)
  Definition make_fixed_nra_context_data (env:data) : nra
    := ABinop OpRecConcat
              (AUnop (OpRec "PBIND"%string) (AConst env))
              (AUnop (OpRec "PDATA"%string) AID).

  Definition nra_wrap op  :=
    nra_double "PBIND" "PDATA" nra_bind op.
  
  Definition nra_wrap_a1 op :=
    nra_double "PBIND" "a1" nra_bind op.

  Definition nra_wrap_bind_a1 op :=
    nra_double "a1" "PDATA" nra_bind op.

  Definition nra_wrap_with_bind op1 :=
    nra_context op1 AID.
  
  Definition nra_project_wrap :=
    nra_wrap_with_bind nra_fail.

  Lemma data_normalized_nra_context_data h env d:
    data_normalized h env ->
    data_normalized h d ->
    data_normalized h (nra_context_data env d).
  Proof.
    unfold nra_context_data.
    repeat (constructor; simpl; eauto).
  Qed.

  Lemma data_normalized_nra_context_data_inv h env d:
    data_normalized h (nra_context_data env d) ->
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
