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
    | OTBinop {τ₁ τ₂ τout} tenv b e₁ e₂ :
        oql_expr_type tenv e₁ τ₁ ->
        oql_expr_type tenv e₂ τ₂ ->
        binOp_type b τ₁ τ₂ τout ->
        oql_expr_type tenv (OBinop b e₁ e₂) τout
    | OTUnop {τ₁ τout} tenv u e₁ :
        oql_expr_type tenv e₁ τ₁ ->
        unaryOp_type u τ₁ τout ->
        oql_expr_type tenv (OUnop u e₁) τout.
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
    - elim (IHoql_expr_type1 _ _ H0 H1); intros.
      elim (IHoql_expr_type2 _ _ H0 H1); intros.
      elim H2; clear H2; intros.
      elim H3; clear H3; intros.
      rewrite H2; rewrite H3; simpl.
      destruct (typed_binop_yields_typed_data _ _ _ H4 H5 H) as [?[??]].
      rewrite H6.
      exists x1; auto.
    - elim (IHoql_expr_type _ _ H0 H2); intros.
      elim H3; clear H3; intros.
      rewrite H3; simpl.
      destruct (typed_unop_yields_typed_data _ _ H4 H) as [?[??]].
      rewrite H5.
      exists x0; auto.
  Qed.
  
End TOQL.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
