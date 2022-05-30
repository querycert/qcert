(*
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
Require Import Permutation.
Require Import Morphisms.
Require Import Utils.
Require Import DataSystem.
Require Import OQL.
Require Import OQLSem.
  
Section TOQL.
  (** Typing for CAMP *)

  Section typ.
  
    Context {m:basic_model}.

    Section constt.
      Context (τconstants:tbindings).

      Local Hint Resolve bindings_type_has_type : qcert.

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
          oql_expr_type tenv (OUnop u e₁) τout
      | TOSFW_true_noorder {τout} tenv from_tenv select_e from_e :
          oql_from_expr_type tenv from_e from_tenv ->
          oql_select_expr_type from_tenv select_e τout -> 
          oql_expr_type tenv (OSFW select_e from_e OTrue ONoOrder) τout
      | TOSFW_where_noorder {τout} tenv from_tenv select_e from_e where_e :
          oql_from_expr_type tenv from_e from_tenv ->
          oql_where_expr_type from_tenv where_e -> 
          oql_select_expr_type from_tenv select_e τout -> 
          oql_expr_type tenv (OSFW select_e from_e (OWhere where_e) ONoOrder) τout
      | TOSFW_true_order {τout} tenv from_tenv select_e from_e sc order_e :
          oql_from_expr_type tenv from_e from_tenv ->
          oql_order_expr_type from_tenv order_e -> 
          oql_select_expr_type from_tenv select_e τout -> 
          oql_expr_type tenv (OSFW select_e from_e OTrue (OOrderBy order_e sc)) τout
      | TOSFW_where_order {τout} tenv from_tenv select_e from_e sc where_e order_e :
          oql_from_expr_type tenv from_e from_tenv ->
          oql_where_expr_type from_tenv where_e -> 
          oql_order_expr_type from_tenv order_e -> 
          oql_select_expr_type from_tenv select_e τout -> 
          oql_expr_type tenv (OSFW select_e from_e (OWhere where_e) (OOrderBy order_e sc)) τout
      with oql_from_expr_type : tbindings -> list oql_in_expr -> tbindings -> Prop :=
      | TOFromNil tenv :
          oql_from_expr_type tenv nil tenv
      | TOFromConsIn tenv tenv' tenv'' v e from_rest_e:
          oql_from_in_expr_type v e tenv tenv' ->
          oql_from_expr_type tenv' from_rest_e tenv'' ->
          oql_from_expr_type tenv (OIn v e :: from_rest_e) tenv''
      | TOFromConsInCast tenv tenv' tenv'' br v e from_rest_e:
          oql_from_in_cast_expr_type br v e tenv tenv' ->
          oql_from_expr_type tenv' from_rest_e tenv'' ->
          oql_from_expr_type tenv (OInCast v br e :: from_rest_e) tenv''
      with oql_from_in_expr_type : string -> oql_expr -> tbindings -> tbindings -> Prop :=
      | TOFromIn {τ} tenv tenv' v e:
          oql_expr_type tenv e (Coll τ) ->
          (* add (v,t) to the environment with the correct scoping (right override left) *)
          rec_concat_sort tenv ((v,τ)::nil) = tenv' ->
          oql_from_in_expr_type v e tenv tenv'
      with oql_from_in_cast_expr_type : list string -> string -> oql_expr -> tbindings -> tbindings -> Prop :=
      | TOFromInCast br bs tenv tenv' v e:
          oql_expr_type tenv e (Coll (Brand bs)) ->
          (* add (v,t) to the environment with the correct scoping (right override left) *)
          rec_concat_sort tenv ((v,(Brand br))::nil) = tenv' ->
          oql_from_in_cast_expr_type br v e tenv tenv'
      with oql_where_expr_type : tbindings -> oql_expr -> Prop :=
      | TOWhere tenv e :
          oql_expr_type tenv e Bool ->
          oql_where_expr_type tenv e
      with oql_order_expr_type : tbindings -> oql_expr -> Prop :=
      | TOOrder tenv {τ} e :
          oql_expr_type tenv e τ ->
          sortable_type τ ->
          oql_order_expr_type tenv e
      with oql_select_expr_type : tbindings -> oql_select_expr -> rtype -> Prop :=
      | TOSelect {τ} tenv e :
          oql_select_map_expr_type tenv e τ ->
          oql_select_expr_type tenv (OSelect e) (Coll τ)
      | TOSelectDistinct {τ} tenv e:
          oql_select_map_expr_type tenv e τ ->
          oql_select_expr_type tenv (OSelectDistinct e) (Coll τ)
      with oql_select_map_expr_type : tbindings -> oql_expr -> rtype -> Prop :=
      | TOSelectMap {τ} tenv e :
          oql_expr_type tenv e τ ->
          oql_select_map_expr_type tenv e τ.

      (** A couple of useful lemma on typed bindings *)
      Lemma oql_from_in_type_sorted τenv v e τenv' :
        is_list_sorted StringOrder.lt_dec (domain τenv) = true ->
        oql_from_in_expr_type v e τenv τenv' ->
        is_list_sorted StringOrder.lt_dec (domain τenv') = true.
      Proof.
        intros.
        inversion H0; subst.
        apply (drec_concat_sort_sorted (odt:=ODT_string)).
      Qed.

      Lemma oql_from_in_cast_type_sorted τenv br v e τenv' :
        is_list_sorted StringOrder.lt_dec (domain τenv) = true ->
        oql_from_in_cast_expr_type br v e τenv τenv' ->
        is_list_sorted StringOrder.lt_dec (domain τenv') = true.
      Proof.
        intros.
        inversion H0; subst.
        apply (drec_concat_sort_sorted (odt:=ODT_string)).
      Qed.

      Lemma oql_from_type_sorted τenv el τenv' :
        is_list_sorted StringOrder.lt_dec (domain τenv) = true ->
        oql_from_expr_type τenv el τenv' ->
        is_list_sorted StringOrder.lt_dec (domain τenv') = true.
      Proof.
        intros.
        revert τenv H0 H.
        induction el; intros.
        - inversion H0; subst; assumption.
        - inversion H0; subst; clear H0.
          + apply (IHel tenv'); try assumption.
            apply (oql_from_in_type_sorted τenv v e); assumption.
          + apply (IHel tenv'); try assumption.
            apply (oql_from_in_cast_type_sorted τenv br v e); assumption.
      Qed.

    End constt.

    Context (τconstants:tbindings).

    Inductive oql_query_program_type : tbindings -> oql_query_program -> rtype -> Prop :=
    | OTDefineQuery {s e rest τ}  {tdefls τ₁} :
        oql_expr_type (rec_concat_sort τconstants tdefls) nil e τ₁ ->
        oql_query_program_type (rec_concat_sort tdefls ((s,τ₁)::nil)) rest τ ->
        oql_query_program_type tdefls (ODefineQuery s e rest) τ
    | OTUndefineQuery {s rest tdefls τ} :
        oql_query_program_type (rremove tdefls s) rest τ ->
        oql_query_program_type tdefls (OUndefineQuery s rest) τ
    | OTQuery {tdefls e τ}:
        oql_expr_type (rec_concat_sort τconstants tdefls) nil e τ ->
        oql_query_program_type tdefls (OQuery e) τ.

    Definition oql_type (o:oql_query_program) (τ:rtype) : Prop
      := oql_query_program_type nil o τ.
    
  End typ.

  Lemma Forall_binding_types_concat {m:basic_model} v τ a tenv dl:
    bindings_type a tenv ->
    Forall (fun d : data => d ▹ τ) dl ->
    Forall (fun env : list (string * data) =>
              bindings_type env (rec_concat_sort tenv ((v, τ) :: nil)))
           (env_map_concat_single a (map (fun x0 : data => (v, x0) :: nil) dl)).
  Proof.
    intros.
    induction dl; intros.
    - constructor.
    - inversion H0; intros; subst; clear H0.
      specialize (IHdl H4).
      constructor; [|assumption]; clear H4.
      unfold bindings_type, rec_concat_sort in *.
      apply rec_sort_Forall2.
      rewrite domain_app.
      rewrite domain_app.
      assert (domain a = domain tenv).
      apply sorted_forall_same_domain.
      assumption.
      rewrite H0.
      f_equal.
      apply Forall2_app.
      assumption.
      constructor.
      simpl.
      split; [reflexivity|assumption].
      constructor.
  Qed.
  
  Lemma oql_from_in_expr_sound {m:basic_model} {τc} {tenv tenv'} c v e l1 :
    oql_from_in_expr_type τc v e tenv tenv' ->
    Forall (fun env => bindings_type env tenv) l1 ->
    (forall (τenv : tbindings) (τout : rtype) (env : list (string * data)),
       bindings_type env τenv ->
       oql_expr_type τc τenv e τout ->
       exists x : data, oql_expr_sem brand_relation_brands c e env x /\ x ▹ τout) ->
    (exists l2,
        oql_from_in_sem brand_relation_brands c v e l1 l2 /\
        (Forall (fun env => bindings_type env tenv') l2))
  .
  Proof.
    intros.
    induction l1.
    - exists nil; split; constructor.
    - inversion H; subst.
      inversion H0; intros; subst; clear H0.
      elim (H1 tenv (Coll τ) a H5 H2); intros; subst; clear H1 H2.
      elim H0; intros; clear H0.
      inversion H2; subst.
      elim (IHl1 H6); intros; subst; clear IHl1 H6.
      elim H3; intros; subst; clear H3.
      exists (env_map_concat_single a (map (fun x => ((v,x)::nil)) dl) ++ x).
      split.
      + econstructor; [assumption|apply H1|reflexivity].
      + apply Forall_app; try assumption.
        assert (r = τ) by (apply rtype_fequal; assumption).
        subst.
        apply Forall_binding_types_concat; assumption.
  Qed.

  Lemma oql_filter_cast_sound {m:basic_model} bs br (dl:list data):
    Forall (fun d : data => d ▹ Brand bs) dl ->
    exists dl',
      (filter_cast_sem brand_relation_brands br dl dl'
       /\ Forall (fun d : data => d ▹ Brand br) dl').
  Proof.
    intros.
    induction dl; intros; simpl in *.
    - exists nil; split; constructor.
    - inversion H; intros; subst; clear H.
      elim (IHdl H3); intros; clear IHdl.
      elim H; intros; subst; clear H.
      inversion H2; intros; subst.
      specialize (sub_brands_dec brand_relation_brands b br); intros.
      elim H7; intros.
      + exists ((dbrand b d) :: x).
        split; [econstructor; assumption| ].
        constructor; try assumption.
        constructor; try assumption.
      + exists x.
        split; [econstructor; assumption| ].
        assumption.
  Qed.

  Lemma oql_from_in_cast_expr_sound {m:basic_model} {τc} {tenv tenv'} c br v e l1 :
    oql_from_in_cast_expr_type τc br v e tenv tenv' ->
    Forall (fun env => bindings_type env tenv) l1 ->
    (forall (τenv : tbindings) (τout : rtype) (env : list (string * data)),
       bindings_type env τenv ->
       oql_expr_type τc τenv e τout ->
       exists x : data, oql_expr_sem brand_relation_brands c e env x /\ x ▹ τout) ->
    (exists l2,
        oql_from_in_cast_sem brand_relation_brands c v br e l1 l2 /\
        (Forall (fun env => bindings_type env tenv') l2))
  .
  Proof.
    intros.
    induction l1.
    - exists nil; split; constructor.
    - inversion H; subst; clear H.
      inversion H0; intros; subst; clear H0.
      elim (H1 tenv (Coll (Brand bs)) a H4 H2); intros; subst; clear H1 H2.
      elim H; intros; clear H.
      inversion H1; subst.
      elim (IHl1 H5); intros; subst; clear IHl1 H5.
      elim H2; intros; subst; clear H2.
      assert (r = Brand bs) by (apply rtype_fequal; assumption).
      subst; clear H.
      elim (oql_filter_cast_sound bs br dl); intros; try assumption.
      elim H; intros; clear H.
      exists (env_map_concat_single a (map (fun x => ((v,x)::nil)) x0) ++ x).
      split.
      + econstructor; [assumption|apply H0|apply H2|reflexivity].
      + apply Forall_app; try assumption.
        apply Forall_binding_types_concat;
          assumption.
  Qed.

  Lemma oql_from_expr_type_sound {m:basic_model} {τc} {τenv} {lenv} {from_tenv} c el:
    bindings_type c τc ->
    Forall (fun env => bindings_type env τenv) lenv ->
    Forall
      (fun ab : oql_in_expr =>
         forall (τenv : tbindings) (τout : rtype) (env : list (string * data)),
           bindings_type env τenv ->
           oql_expr_type τc τenv (oin_expr ab) τout ->
           (exists x : data, oql_expr_sem brand_relation_brands c (oin_expr ab) env x /\ x ▹ τout)) el ->
    oql_from_expr_type τc τenv el from_tenv ->
    (exists tenv',
        oql_from_sem brand_relation_brands c el lenv tenv' /\
        (Forall (fun env => bindings_type env from_tenv) tenv')).
  Proof.
    intros Hc.
    revert τenv from_tenv lenv.
    induction el; intros.
    - inversion H1; subst.
      exists lenv.
      split; [constructor|assumption].
    - destruct a.
      + inversion H1; intros; subst; clear H1.
        inversion H0; intros; subst; clear H0.
        elim (@oql_from_in_expr_sound m τc τenv tenv' c s o lenv H7 H H3);
          intros; clear H H3.
        elim H0; intros; clear H0.
        elim (IHel tenv' from_tenv x H1 H4 H8); intros.
        elim H0; intros; clear H0.
        exists x0.
        split; [|assumption].
        econstructor.
        apply H.
        apply H2.
      + inversion H1; intros; subst; clear H1.
        inversion H0; intros; subst; clear H0.
        elim (@oql_from_in_cast_expr_sound m τc τenv tenv' c l s o lenv H8 H H3);
          intros; clear H H3.
        elim H0; intros; clear H0.
        elim (IHel tenv' from_tenv x H1 H4 H9); intros.
        elim H0; intros; clear H0.
        exists x0.
        split; [|assumption].
        econstructor.
        apply H.
        apply H2.
  Qed.

  Lemma oql_select_map_expr_type_sound {m:basic_model} {τc} {from_tenv} {x} {τout} c e :
    bindings_type c τc ->
    Forall (fun env : list (string * data) => bindings_type env from_tenv) x ->
    (forall (τenv : tbindings) (τout : rtype) (env : list (string * data)),
        bindings_type env τenv ->
        oql_expr_type τc τenv e τout ->
        exists x : data, oql_expr_sem brand_relation_brands c e env x /\ x ▹ τout)
    ->
    oql_select_map_expr_type τc from_tenv e τout ->
    (exists dl,
        oql_select_map_sem brand_relation_brands c e x dl /\ Forall (fun d => d ▹ τout) dl).
  Proof.
    induction x; simpl in *; intros.
    - exists nil; split; constructor; constructor.
    - inversion H0; simpl in *; intros; subst; clear H0.
      elim (IHx H H6 H1 H2); intros; subst; clear IHx; try assumption.
      elim H0; intros; subst; clear H0.
      inversion H2; subst; intros.
      elim (H1 from_tenv τout a H5 H0); intros.
      elim H7; intros; clear H7.
      exists (x1 :: x0).
      split; constructor; assumption.
  Qed.

  Lemma oql_where_expr_type_sound {m:basic_model} {τc} {from_tenv} {x} c e :
    bindings_type c τc ->
    Forall (fun env : list (string * data) => bindings_type env from_tenv) x ->
    (forall (τenv : tbindings) (τout : rtype) (env : list (string * data)),
         bindings_type env τenv ->
         oql_expr_type τc τenv e τout ->
         exists x : data, oql_expr_sem brand_relation_brands c e env x /\ x ▹ τout) ->
    oql_where_expr_type τc from_tenv e ->
    (exists tenv',
        oql_where_sem brand_relation_brands c e x tenv' /\
        (Forall (fun env => bindings_type env from_tenv) tenv')).
  Proof.
    intros.
    induction x; intros; simpl in *.
    - exists nil; split; constructor.
    - inversion H0; intros; subst; clear H0.
      elim (IHx H6); intros; clear IHx.
      elim H0; intros; clear H0.
      inversion H2; intros; subst; clear H2.
      elim (H1 from_tenv Bool a H5 H0);
        intros; subst; clear H1.
      elim H2; intros; clear H2.
      inversion H7; intros; subst.
      destruct b; intros; simpl in *.
      (* Condition is true *)
      + exists (a :: x0).
        split; constructor; assumption.
      (* Condition is false *)
      + exists x0.
        split; [constructor; assumption|assumption].
  Qed.

  Lemma oql_order_expr_type_sound {m:basic_model} {τc} {from_tenv} {x} c sc e :
    bindings_type c τc ->
    Forall (fun env : list (string * data) => bindings_type env from_tenv) x ->
    (forall (τenv : tbindings) (τout : rtype) (env : list (string * data)),
         bindings_type env τenv ->
         oql_expr_type τc τenv e τout ->
         exists x : data, oql_expr_sem brand_relation_brands c e env x /\ x ▹ τout) ->
    oql_order_expr_type τc from_tenv e ->
    (exists tenv',
        oql_order_sem brand_relation_brands c e sc x tenv' /\
        (Forall (fun env => bindings_type env from_tenv) tenv')).
  Proof.
    intros.
    inversion H2; subst.
    inversion H4; subst; clear H4.
    
    admit.
  Admitted.

  Lemma oql_select_expr_type_sound {m:basic_model} {τc} {from_tenv} {x} {τout} c e :
    bindings_type c τc ->
    Forall (fun env : list (string * data) => bindings_type env from_tenv) x ->
    (forall (τenv : tbindings) (τout : rtype) (env : list (string * data)),
        bindings_type env τenv ->
        oql_expr_type τc τenv (oselect_expr e) τout ->
        exists x : data, oql_expr_sem brand_relation_brands c (oselect_expr e) env x /\ x ▹ τout)
    ->
    oql_select_expr_type τc from_tenv e τout ->
    (exists dl,
        oql_select_sem brand_relation_brands c e x (dcoll dl) /\ dcoll dl ▹ τout).
  Proof.
    intros.
    inversion H2; subst; intros.
    - elim (@oql_select_map_expr_type_sound m τc from_tenv x τ c e0 H H0 H1 H3);
        intros; subst.
      elim H4; intros; subst; clear H4.
      exists x0.
      split; constructor; assumption.
    - elim (@oql_select_map_expr_type_sound m τc from_tenv x τ c e0 H H0 H1 H3);
        intros; subst.
      elim H4; intros; subst; clear H4.
      exists (bdistinct x0).
      split; econstructor.
      + apply H5.
      + reflexivity.
      + apply bdistinct_Forall; assumption.
  Qed.

  Theorem typed_oql_expr_sound {m:basic_model} {τc} {τenv τout} c (env:list (string*data)) (q:oql_expr):
    bindings_type c τc ->
    bindings_type env τenv ->
    (oql_expr_type τc τenv q τout) ->
    (exists x, (oql_expr_sem brand_relation_brands c q env x /\ (x ▹ τout))).
  Proof.
    intro Hc.
    revert τenv τout env.
    induction q; simpl; intros.
    - inversion H0; intros; subst; clear H0.
      exists (normalize_data brand_relation_brands d).
      split; [constructor; reflexivity|assumption].
    - inversion H0; intros; subst; clear H0.
      unfold bindings_type in *; unfold edot in *.
      elim (Forall2_lookupr_some H H3); intros.
      elim H0; intros; subst.
      exists x.
      split; [constructor; unfold edot| ]; assumption.
    - inversion H0; intros; subst; clear H0.
      unfold bindings_type in *; unfold edot in *.
      elim (Forall2_lookupr_some Hc H3); intros.
      elim H0; intros; subst.
      exists x.
      split; [constructor; unfold edot| ]; assumption.
    - inversion H0; intros; subst; clear H0.
      elim (IHq1 τenv τ₁ env H H5); intros; subst; clear H5.
      elim (IHq2 τenv τ₂ env H H7); intros; subst; clear H7.
      elim H0; intros; subst; clear H0.
      elim H1; intros; subst; clear H1.
      destruct (typed_binary_op_yields_typed_data _ _ _ H3 H4 H8) as [?[??]].
      exists x1; split; [|assumption];
        econstructor;[apply H2|apply H0|assumption].
    - inversion H0; intros; subst; clear H0.
      elim (IHq τenv τ₁ env H H4); intros; subst; clear H4.
      elim H0; intros; subst; clear H0.
      destruct (typed_unary_op_yields_typed_data _ _ H2 H6) as [?[??]].
      exists x0; split; [|assumption];
        econstructor; [apply H1|assumption].
    - inversion H1; intros; subst; clear H1.
      assert (Forall (fun env0 : list (string * data) => bindings_type env0 τenv) (env :: nil))
        by (constructor; [assumption|constructor]).
      elim (@oql_from_expr_type_sound _ τc τenv (env::nil) from_tenv c el Hc H1 H H5);
        intros.
      elim H2; intros; subst; clear H2.
      elim (@oql_select_expr_type_sound _ τc from_tenv x τout c e1 Hc H4 IHq H7);
        intros; subst.
      elim H2; intros; subst; clear H2.
      exists (dcoll x0).
      split; [|assumption].
      econstructor;[apply H3|assumption].
    - inversion H1; intros; subst; clear H1.
      assert (Forall (fun env0 : list (string * data) => bindings_type env0 τenv) (env :: nil))
        by (constructor; [assumption|constructor]).
      elim (@oql_from_expr_type_sound _ τc τenv (env::nil) from_tenv c el Hc H1 H H6);
        intros.
      elim H2; intros; subst; clear H2.
      elim (@oql_where_expr_type_sound _ τc from_tenv x c q Hc H4 IHq0 H8);
        intros; subst; clear H8.
      elim H2; intros; subst; clear H2.
      elim (@oql_select_expr_type_sound _ τc from_tenv x0 τout c e1 Hc H7 IHq H9);
        intros; subst.
      elim H2; intros; subst; clear H2.
      exists (dcoll x1).
      split; [|assumption].
      econstructor; [apply H3|apply H5|assumption].
    - inversion H1; intros; subst; clear H1.
      assert (Forall (fun env0 : list (string * data) => bindings_type env0 τenv) (env :: nil))
        by (constructor; [assumption|constructor]).
      elim (@oql_from_expr_type_sound _ τc τenv (env::nil) from_tenv c el Hc H1 H H8);
        intros.
      elim H2; intros; subst; clear H2.
      elim (@oql_order_expr_type_sound _ τc from_tenv x c sc q Hc H4 IHq0 H9);
        intros; subst; clear H8.
      elim H2; intros; subst; clear H2.
      elim (@oql_select_expr_type_sound _ τc from_tenv x0 τout c e1 Hc H6 IHq H10);
        intros; subst.
      elim H2; intros; subst; clear H2.
      exists (dcoll x1).
      split; [|assumption].
      econstructor; [apply H3|apply H5|assumption].
    - inversion H1; intros; subst; clear H1.
      assert (Forall (fun env0 : list (string * data) => bindings_type env0 τenv) (env :: nil))
        by (constructor; [assumption|constructor]).
      elim (@oql_from_expr_type_sound _ τc τenv (env::nil) from_tenv c el Hc H1 H H9);
        intros.
      elim H2; intros; subst; clear H2.
      elim (@oql_where_expr_type_sound _ τc from_tenv x c q1 Hc H4 IHq2 H10);
        intros; subst; clear H10.
      elim H2; intros; subst; clear H2.
      elim (@oql_order_expr_type_sound _ τc from_tenv x0 c sc q2 Hc H6 IHq3 H11);
        intros; subst; clear H11.
      elim H2; intros; subst; clear H2.
      elim (@oql_select_expr_type_sound _ τc from_tenv x1 τout c e1 Hc H8 IHq1 H12);
        intros; subst.
      elim H2; intros; subst; clear H2.
      exists (dcoll x2).
      split; [|assumption].
      econstructor; [apply H3|apply H5|apply H7|assumption].
  Qed.

 Theorem typed_oql_expr_yields_typed_data {m:basic_model} {τc} {τenv τout} c (env:list (string*data)) (q:oql_expr):
    bindings_type c τc ->
    bindings_type env τenv ->
    (oql_expr_type τc τenv q τout) ->
    (exists x, (oql_expr_interp brand_relation_brands c q env = Some x /\ (x ▹ τout))).
  Proof.
    intros.
    elim (@typed_oql_expr_sound _ τc τenv τout c env q H H0 H1); intros; subst.
    elim H2; intros; clear H2; subst.
    exists x; split; [|assumption].
    rewrite oql_expr_interp_correct_and_complete; assumption.
  Qed.

  Lemma typed_oql_query_program_yields_typed_data {m:basic_model} {τc τdefls} {τout} c (defls env:list (string*data)) (q:oql_query_program):
    bindings_type c τc ->
    bindings_type defls τdefls ->
    (oql_query_program_type τc τdefls q τout) ->
    (exists x, (oql_query_program_interp brand_relation_brands c defls q = Some x /\ (x ▹ τout))).
  Proof.
    intros.
    revert c defls env H H0.
    dependent induction H1; simpl; intros.
    - assert (bt: bindings_type (rec_concat_sort c defls) (rec_concat_sort τc tdefls))
        by (apply bindings_type_rec_concat_sort; trivial).
      assert (bindings_type nil nil) by constructor.
      destruct (typed_oql_expr_yields_typed_data _ nil e bt H3 H)
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
      constructor.
  Qed.

  Lemma typed_oql_query_program_sound {m:basic_model} {τc τdefls} {τout} c (defls env:list (string*data)) (q:oql_query_program):
    bindings_type c τc ->
    bindings_type defls τdefls ->
    (oql_query_program_type τc τdefls q τout) ->
    (exists x, (oql_query_program_sem brand_relation_brands c defls q x /\ (x ▹ τout))).
  Proof.
    intros.
    elim (typed_oql_query_program_yields_typed_data c defls env q H H0 H1); intros.
    elim H2; intros; clear H2.
    exists x; split; [|assumption].
    apply oql_query_program_interp_correct_and_complete; assumption.
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
  
  Theorem typed_oql_sound {m:basic_model} {τc} {τout} c (q:oql_query_program):
    bindings_type c τc ->
    oql_type τc q τout ->
    (exists x, (oql_sem brand_relation_brands c q x /\ (x ▹ τout))).
  Proof.
    intros.
    elim (typed_oql_yields_typed_data c q H H0); intros.
    elim H1; intros; clear H1.
    exists x; split; [|assumption].
    apply oql_interp_correct_and_complete; assumption.
  Qed.

End TOQL.
