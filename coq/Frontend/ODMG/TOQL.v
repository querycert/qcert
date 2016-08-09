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

Section TOQL.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Program.
  Require Import EquivDec Morphisms.

  Require Import Utils BasicSystem.

  Require Import OQL.
  
  (** Typing for CAMP *)

  Section typ.
  
    Context {m:basic_model}.
    Context (τconstants:tbindings).
    Hint Resolve bindings_type_has_type.

    Inductive oql_expr_type : tbindings -> oql_expr -> rtype -> Prop :=
    | OTConst {τ} tenv c :
        data_type (normalize_data brand_relation_brands c) τ ->
        oql_expr_type tenv (OConst c) τ
    | OTVar {τ} tenv v :
        edot tenv v = Some τ -> oql_expr_type tenv (OVar v) τ
    | OTTable {τ} tenv s :
      tdot τconstants s = Some τ ->
      oql_expr_type tenv (OTable s) τ
    .
  End typ.
    
  (** Main typing soundness theorem for OQL *)

  Theorem typed_oql_yields_typed_data {m:basic_model} {τc} {τenv τout} c (env:list (string*data)) (q:oql_expr):
    bindings_type c τc ->
    bindings_type env τenv ->
    (oql_expr_type τc τenv q τout) ->
    (exists x, (oql_interp brand_relation_brands c q env = Some x /\ (x ▹ τout))).
  Proof.
    intros.
    revert c env H H0.
    dependent induction H1; simpl; intros.
    - exists (normalize_data brand_relation_brands c).
      split; [reflexivity|assumption].
    - unfold bindings_type in H1.
      apply (Forall2_lookupr_some _ _ _ _ H1).
      assumption.
    - unfold bindings_type in H0.
      apply (Forall2_lookupr_some _ _ _ _ H0).
      assumption.
  Qed.
  
End TOQL.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
