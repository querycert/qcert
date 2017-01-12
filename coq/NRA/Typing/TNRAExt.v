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

Section TNRAExt.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.

  Require Import Utils BasicSystem.

  Require Import NRAExt.
  Require Import TNRA.

  Local Open Scope nraext_scope.
  
  (** Typing for NRA *)

  Context {m:basic_model}.
  Definition nraext_type Op A B := nra_type (nra_of_nraext Op) A B.
  
  Notation "Op ▷ A >=> B" := (nraext_type Op A B) (at level 70).

  (** Main typing soundness theorem for the Extended NRA *)

  Theorem typed_nraext_yields_typed_data {τin τout} (d:data) (op:nraext):
    (d ▹ τin) -> (op ▷ τin >=> τout) ->
    (exists x, (brand_relation_brands ⊢ op @ₓ d = Some x /\ (x ▹ τout))).
  Proof.
    unfold fun_of_nraext, nraext_type; intros.
    apply (@typed_nra_yields_typed_data m τin τout); assumption.
  Qed.

  (** Corrolaries of the main type soudness theorem *)

  Definition typed_nraext_total {τin τout} (op:nraext) (d:data):
    (d ▹ τin) -> (op ▷ τin >=> τout) ->             
    { x:data | x ▹ τout }.
  Proof.
    unfold fun_of_nraext, nraext_type; intros.
    apply (@typed_nra_total m τin τout (nra_of_nraext op) H0 d); assumption.
  Defined.

  Definition tnraext_eval {τin τout} (op:nraext) (d:data):
    (d ▹ τin) -> (op ▷ τin >=> τout) -> data.
  Proof.
    unfold fun_of_nraext, nraext_type; intros.
    apply (@tnra_eval m τin τout (nra_of_nraext op) H0 d); assumption.
  Defined.
End TNRAExt.

(* Typed algebraic plan *)

Notation "Op ▷ A >=> B" := (nraext_type Op A B) (at level 70) : nraext_scope.
Notation "Op @▷ d" := (tnraext_eval Op d) (at level 70) : nraext_scope.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
