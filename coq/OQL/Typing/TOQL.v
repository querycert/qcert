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
Require Import Arith.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import OQL.
  
Section TOQL.
  (** Typing for CAMP *)

  Section typ.
  
    Context {m:basic_model}.
    Section constt.
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
          binary_op_type b τ₁ τ₂ τout ->
          oql_expr_type tenv (OBinop b e₁ e₂) τout
      | OTUnop {τ₁ τout} tenv u e₁ :
          oql_expr_type tenv e₁ τ₁ ->
          unary_op_type u τ₁ τout ->
          oql_expr_type tenv (OUnop u e₁) τout.

    End constt.
    
    Context (τconstants:tbindings).

    Inductive oql_query_program_type : tbindings -> tbindings -> oql_query_program -> rtype -> Prop :=
    | OTDefineQuery {tenv s e rest τ}  {tdefls τ₁} :
        oql_expr_type (rec_concat_sort τconstants tdefls) tenv e τ₁ ->
        oql_query_program_type (rec_concat_sort tdefls ((s,τ₁)::nil)) tenv rest τ ->
        oql_query_program_type tdefls tenv (ODefineQuery s e rest) τ
    | OTUndefineQuery {tenv s rest tdefls τ} :
        oql_query_program_type (rremove tdefls s) tenv rest τ ->
        oql_query_program_type tdefls tenv (OUndefineQuery s rest) τ
    |OTQuery {tdefls tenv e τ}:
     oql_expr_type (rec_concat_sort τconstants tdefls) tenv e τ ->
     oql_query_program_type tdefls tenv (OQuery e) τ.

    Definition oql_type (o:oql_query_program) (τ:rtype) : Prop
      := oql_query_program_type nil nil o τ.
    
    End typ.

  Theorem typed_oql_expr_yields_typed_data {m:basic_model} {τc} {τenv τout} c (env:list (string*data)) (q:oql_expr):
    bindings_type c τc ->
    bindings_type env τenv ->
    (oql_expr_type τc τenv q τout) ->
    (exists x, (oql_expr_interp brand_relation_brands c q env = Some x /\ (x ▹ τout))).
  Proof.
    intros.
    revert c env H H0.
    dependent induction H1; simpl; intros.
    - exists (normalize_data brand_relation_brands c).
      split; [reflexivity|assumption].
    - unfold bindings_type in H1.
      apply (Forall2_lookupr_some H1).
      assumption.
    - unfold bindings_type in H0.
      apply (Forall2_lookupr_some H0).
      assumption.
    - elim (IHoql_expr_type1 _ _ H0 H1); intros.
      elim (IHoql_expr_type2 _ _ H0 H1); intros.
      elim H2; clear H2; intros.
      elim H3; clear H3; intros.
      rewrite H2; rewrite H3; simpl.
      destruct (typed_binary_op_yields_typed_data _ _ _ H4 H5 H) as [?[??]].
      rewrite H6.
      exists x1; auto.
    - elim (IHoql_expr_type _ _ H0 H2); intros.
      elim H3; clear H3; intros.
      rewrite H3; simpl.
      destruct (typed_unary_op_yields_typed_data _ _ H4 H) as [?[??]].
      rewrite H5.
      exists x0; auto.
  Qed.

  Lemma typed_oql_query_program_yields_typed_data {m:basic_model} {τc τdefls} {τenv τout} c (defls env:list (string*data)) (q:oql_query_program):
    bindings_type c τc ->
    bindings_type defls τdefls ->
    bindings_type env τenv ->
    (oql_query_program_type τc τdefls τenv q τout) ->
    (exists x, (oql_query_program_interp brand_relation_brands c defls q env = Some x /\ (x ▹ τout))).
  Proof.
    intros.
    revert c defls env H H0 H1.
    dependent induction H2; simpl; intros.
    - assert (bt: bindings_type (rec_concat_sort c defls) (rec_concat_sort τc tdefls))
        by (apply bindings_type_rec_concat_sort; trivial).
      destruct (typed_oql_expr_yields_typed_data _ _ e bt H3 H)
        as [d [de dt]].
      rewrite de; simpl.
      destruct (IHoql_query_program_type _ (rec_concat_sort defls ((s,d)::nil)) env H0);
        eauto 2.
      apply bindings_type_rec_concat_sort; trivial.
      constructor; simpl; auto.
    - destruct (IHoql_query_program_type c (rremove defls s) env); eauto 2.
      apply rremove_well_typed.
      trivial.
    - eapply typed_oql_expr_yields_typed_data; eauto.
      apply bindings_type_rec_concat_sort; trivial.
  Qed.

    (** Main typing soundness theorem for OQL *)

  Theorem typed_oql_yields_typed_data {m:basic_model} {τc} {τout} c (q:oql_query_program):
    bindings_type c τc ->
    oql_type τc q τout ->
    (exists x, (oql_interp brand_relation_brands c q = Some x /\ (x ▹ τout))).
  Proof.
    intros.
    eapply typed_oql_query_program_yields_typed_data; eauto
    ; constructor.
  Qed.
  
End TOQL.

