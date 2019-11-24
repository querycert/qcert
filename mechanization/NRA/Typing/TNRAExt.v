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

Require Import String.
Require Import List.
Require Import Compare_dec.
Require Import CommonSystem.
Require Import NRAExt.
Require Import TNRA.

Section TNRAExt.
  Local Open Scope nraext_scope.
  
  (** Typing for NRA *)

  Context {m:basic_model}.

  Definition nraext_type Op C A B := nra_type C (nra_of_nraext Op) A B.

  Notation "Op ▷ A >=> B ⊣ C" := (nraext_type Op C A B) (at level 70) : nraext_scope.

  (** Main typing soundness theorem for the Extended NRA *)

  Theorem typed_nraext_yields_typed_data {τc} {τin τout} (d:data) c (op:nraext):
    (bindings_type c τc) ->
    (d ▹ τin) -> (op ▷ τin >=> τout ⊣ τc) ->
    (exists x, (brand_relation_brands ⊢ op @ₓ d ⊣ c = Some x /\ (x ▹ τout))).
  Proof.
    unfold nraext_eval, nraext_type; intros.
    apply (@typed_nra_yields_typed_data m τc τin τout); assumption.
  Qed.

  (** Corrolaries of the main type soudness theorem *)

  Definition typed_nraext_total {τc} {τin τout} (op:nraext) (d:data) c :
    (bindings_type c τc) ->
    (d ▹ τin) -> (op ▷ τin >=> τout ⊣ τc) ->             
    { x:data | x ▹ τout }.
  Proof.
    unfold nraext_eval, nraext_type; intros.
    apply (@typed_nra_total m τc τin τout (nra_of_nraext op) H1 c d); assumption.
  Defined.

  Definition tnraext_eval {τc} {τin τout} (op:nraext) (d:data) c :
    (bindings_type c τc) ->
    (d ▹ τin) -> (op ▷ τin >=> τout ⊣ τc) -> data.
  Proof.
    unfold nraext_eval, nraext_type; intros.
    apply (@tnra_eval m τc τin τout (nra_of_nraext op) H1 c d); assumption.
  Defined.
End TNRAExt.

(* Typed algebraic plan *)

Notation "Op ▷ A >=> B ⊣ C" := (nraext_type Op C A B) (at level 70) : nraext_scope.
Notation "Op @▷ d ⊣ c" := (tnraext_eval Op d c) (at level 70) : nraext_scope.

