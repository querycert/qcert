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

Section TDData.
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
  Require Import TData.

  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Inductive ddata_type : ddata -> drtype -> Prop :=
  | dtlocal d τ : data_type d τ -> ddata_type (Dlocal d) (Tlocal τ)
  | dtdistr dl τ : Forall (fun d => data_type d τ) dl -> ddata_type (Ddistr dl) (Tdistr τ).
  
  Lemma ddata_dtype_normalized d dτ :
    ddata_type d dτ -> ddata_normalized brand_relation_brands d.
  Proof.
    intros.
    destruct d; simpl in *.
    - inversion H. subst.
      constructor.
      apply (data_type_normalized d τ H1).
    - inversion H. subst.
      constructor.
      rewrite Forall_forall in *; intros.
      specialize (H1 x H0).
      apply (data_type_normalized x τ H1).
  Qed.
      
End TDData.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)

