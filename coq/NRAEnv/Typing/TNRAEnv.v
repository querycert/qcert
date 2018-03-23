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

Section TNRAEnv.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import Program.
  Require Import Utils.
  Require Import CommonSystem.
  Require Import cNRAEnvSystem.
  Require Import NRAEnv.
  Require Import NRAEnvEq.

  Local Open Scope nraenv_scope.
  
  (** Typing for NRA *)
  Section typ.
    Context {m:basic_model}.
    Context (τconstants:list (string*rtype)).
    Definition nraenv_type (q:nraenv) : rtype -> rtype -> rtype -> Prop :=
      @nraenv_core_type m τconstants (nraenv_to_nraenv_core q).

  End typ.

  Notation "Op ▷ₓ A >=> B ⊣ C ; E" := (nraenv_type C Op E A B) (at level 70).

  Section groupby.

    Context {m:basic_model}.
    Context (τconstants:list (string*rtype)).

    (* An explicit typing rule for groupby *)
    Lemma type_NNRCGroupBy {k τl pf} τcenv τenv τin g sl e :
      sublist sl (domain τl) ->
      e ▷ₓ τin >=> (Coll (Rec k τl pf)) ⊣ τcenv ; τenv ->
                                                  (NRAEnvGroupBy g sl e) ▷ₓ τin >=>  (GroupBy_type g sl k τl pf) ⊣ τcenv ; τenv.
    Proof.
      unfold GroupBy_type, nraenv_type.
      simpl; intros subl typ.
      unfold macro_cNRAEnvGroupBy.
      repeat (econstructor; try eassumption; trivial).
      Unshelve.
      - simpl; reflexivity.
      - apply (is_list_sorted_sublist pf).
        apply sublist_domain.
        apply sublist_rproject.
      - simpl; trivial.
      - simpl; trivial.
      - simpl; trivial.
    Qed.

    (* And an explicit typing rule inversion principle for groupby *)
    (* note that additional constraint, since otherwise the grouped elements will
          be ignored, which allows more freedom in the typing
     *)
    Lemma type_NNRCGroupBy_inv {τl k pf} τcenv τenv τin g sl e:
      ((NRAEnvGroupBy g sl e) ▷ₓ τin >=>  (GroupBy_type g sl k τl pf) ⊣ τcenv ; τenv) ->
      sublist sl (domain τl) /\ e ▷ₓ τin >=> (Coll (Rec k τl pf)) ⊣ τcenv ; τenv.
    Proof.
      unfold GroupBy_type, nraenv_type; simpl.
      unfold macro_cNRAEnvGroupBy, macro_cNRAEnvProject; intros typ.
      nraenv_core_inverter; subst.
      destruct x; destruct x0; simpl in *; subst.
      assert (inn1:assoc_lookupr ODT_eqdec (rec_concat_sort τ₁ [(s, s1)]) s =
                   assoc_lookupr ODT_eqdec (rec_concat_sort (rproject τl sl) [(s, Coll (Rec k τl pf))]) s)
        by congruence.
      unfold rec_concat_sort in inn1.
      repeat rewrite assoc_lookupr_drec_sort in inn1; simpl in inn1.
      repeat rewrite @assoc_lookupr_app in inn1; simpl in inn1.
      destruct (string_eqdec s s); try congruence.
      invcs inn1.
      unfold tdot, edot, rec_concat_sort in *.
      repeat rewrite assoc_lookupr_drec_sort in *.
      simpl in *.
      invcs H9; invcs H10; invcs H0.
      invcs H13.
      rtype_equalizer; subst.
      split; trivial.
      erewrite Rec_pr_irrel; try eassumption.
    Qed.

  End groupby.
  (** Type lemmas for individual algebraic expressions *)

  Section prop.
    Context {m:basic_model}.

    (** Main typing soundness theorem for the NRA *)

    Lemma typed_nraenv_yields_typed_nraenv_core {τc τenv τin τout} (op:nraenv):
      (op ▷ₓ τin >=> τout ⊣ τc;τenv) -> nraenv_core_type τc (nraenv_to_nraenv_core op) τenv τin τout.
    Proof.
      unfold nraenv_type; intro; assumption.
    Qed.

    Lemma typed_nraenv_core_yields_typed_nraenv {τc τenv τin τout} (op:nraenv):
      nraenv_core_type τc (nraenv_to_nraenv_core op) τenv τin τout -> (op ▷ₓ τin >=> τout ⊣ τc;τenv).
    Proof.
      revert τin τout τenv.
      induction op; intros;
        (* Takes care of all core operators *)
        unfold nraenv_type; assumption;
          try (solve[inversion H; clear H; subst; repeat econstructor; eauto]).
    Qed.
    
    Theorem typed_nraenv_core_iff_typed_nraenv {τc τenv τin τout} (op:nraenv):
      (op ▷ₓ τin >=> τout ⊣ τc;τenv) <-> nraenv_core_type τc (nraenv_to_nraenv_core op) τenv τin τout.
    Proof.
      split.
      apply typed_nraenv_yields_typed_nraenv_core.
      apply typed_nraenv_core_yields_typed_nraenv.
    Qed.
    
    Theorem typed_nraenv_yields_typed_data {τc τenv τin τout} c (env:data) (d:data) (op:nraenv):
      bindings_type c τc ->
      (env ▹ τenv) -> (d ▹ τin) -> (op ▷ₓ τin >=> τout ⊣ τc;τenv) ->
      (exists x, (nraenv_eval brand_relation_brands c op env d = Some x /\ (x ▹ τout))).
    Proof.
      intros.
      unfold nraenv_eval.
      apply (@typed_nraenv_core_yields_typed_data m τc τenv τin τout); try assumption.
    Qed.

    (** Corrolaries of the main type soudness theorem *)

    Definition typed_nraenv_total {τc τenv τin τout} (op:nraenv) (HOpT: op ▷ₓ τin >=> τout ⊣ τc;τenv) c (env:data) (d:data):
      bindings_type c τc ->
      (env ▹ τenv) ->
      (d ▹ τin) ->
      { x:data | x ▹ τout }.
    Proof.
      intros Hc Henv.
      intros HdT.
      generalize (typed_nraenv_yields_typed_data c env d op Hc Henv HdT HOpT).
      intros.
      destruct (nraenv_eval brand_relation_brands c op env d).
      assert (data_type d0 τout).
      - inversion H. inversion H0. inversion H1. trivial.
      - exists d0. trivial.
      - cut False. intuition. inversion H.
        destruct H0. inversion H0.
    Defined.

    Definition tnraenv_eval {τc τenv τin τout} (op:nraenv) (HOpT: op ▷ₓ τin >=> τout ⊣ τc;τenv) c (env:data) (d:data):
      bindings_type c τc ->
      (env ▹ τenv) -> (d ▹ τin) -> data.
    Proof.
      intros Hc Henv.
      intros HdT.
      destruct (typed_nraenv_total op HOpT c env d Hc Henv HdT).
      exact x.
    Defined.
  End prop.

End TNRAEnv.

(* Typed algebraic plan *)

Notation "Op ▷ₓ A >=> B ⊣ C ; E" := (nraenv_type C Op E A B) (at level 70).
Notation "Op @▷ₓ d ⊣ C ; e" := (tnraenv_eval C Op e d) (at level 70).

(* Used to prove type portion of typed directed rewrites *)

Hint Unfold nraenv_type.
Hint Constructors unary_op_type.
Hint Constructors binary_op_type.

(* inverts, then tries and solve *)
Ltac nraenv_inferer :=
  unfold nraenv_type in *;
  unfold nraenv_eval; simpl in *;
  try nraenv_core_inverter; subst; try eauto.

(* simplifies when a goal evaluates an expression over well-typed data *)
Ltac nraenv_input_well_typed :=
  repeat progress
         match goal with
         | [HO:?op ▷ₓ ?τin >=> ?τout ⊣  ?τc ; ?τenv,
                                              HI:?x ▹ ?τin,
                                              HE:?env ▹ ?τenv,
                                              HC:bindings_type ?c ?τc
                                              |- context [(nraenv_eval ?h ?c ?op ?env ?x)]] =>
           let xout := fresh "dout" in
           let xtype := fresh "τout" in
           let xeval := fresh "eout" in
           destruct (typed_nraenv_yields_typed_data _ _ _ op HC HE HI HO)
             as [xout [xeval xtype]]; rewrite xeval in *; simpl
         end; input_well_typed.

