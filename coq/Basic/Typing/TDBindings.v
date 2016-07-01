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

Section TDBindings.
  Require Import String.
  Require Import List.
  Require Import Sumbool.
  Require Import Arith.
  Require Import Bool.
  Require Import Morphisms.
  Require Import Basics.

  Require Import BrandRelation.
  Require Import Utils Types BasicRuntime.
  Require Import ForeignDataTyping.
  Require Import TDData.

  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Definition tdbindings := list (string*drtype).

  Definition dbindings_type (b:list (string*ddata)) (t:tdbindings)
    := Forall2 (fun xy1 xy2 =>
                      (fst xy1) = (fst xy2)
                  /\ ddata_type (snd xy1) (snd xy2)) b t.

  Hint Resolve ddata_dtype_normalized.
  Lemma dbindings_type_Forall_normalized c τc :
    dbindings_type c τc ->
    Forall
      (fun d : string * ddata => ddata_normalized brand_relation_brands (snd d))
      c.
  Proof.
    induction 1; trivial.
    intuition.
    constructor.
    - destruct x; destruct y; simpl in *; subst.
      apply (ddata_dtype_normalized _ _ H2).
    - auto.
  Qed.

End TDBindings.

Hint Resolve dbindings_type_Forall_normalized.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)

