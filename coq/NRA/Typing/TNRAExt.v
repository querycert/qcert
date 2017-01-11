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

  Local Open Scope algext_scope.
  
  (** Typing for NRA *)

  Context {m:basic_model}.
  Definition algext_type Op A B := alg_type (alg_of_algext Op) A B.
  
  Notation "Op ▷ A >=> B" := (algext_type Op A B) (at level 70).

  (** Main typing soundness theorem for the Extended NRA *)

  Theorem typed_algext_yields_typed_data {τin τout} (d:data) (op:algext):
    (d ▹ τin) -> (op ▷ τin >=> τout) ->
    (exists x, (brand_relation_brands ⊢ op @ₓ d = Some x /\ (x ▹ τout))).
  Proof.
    unfold fun_of_algext, algext_type; intros.
    apply (@typed_alg_yields_typed_data m τin τout); assumption.
  Qed.

  (** Corrolaries of the main type soudness theorem *)

  Definition typed_algext_total {τin τout} (op:algext) (d:data):
    (d ▹ τin) -> (op ▷ τin >=> τout) ->             
    { x:data | x ▹ τout }.
  Proof.
    unfold fun_of_algext, algext_type; intros.
    apply (@typed_alg_total m τin τout (alg_of_algext op) H0 d); assumption.
  Defined.

  Definition talgext_eval {τin τout} (op:algext) (d:data):
    (d ▹ τin) -> (op ▷ τin >=> τout) -> data.
  Proof.
    unfold fun_of_algext, algext_type; intros.
    apply (@talg_eval m τin τout (alg_of_algext op) H0 d); assumption.
  Defined.
End TNRAExt.

(* Typed algebraic plan *)

Notation "Op ▷ A >=> B" := (algext_type Op A B) (at level 70) : algext_scope.
Notation "Op @▷ d" := (talgext_eval Op d) (at level 70) : algext_scope.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
