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

Section TAlgEnvExt.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import Program.

  Require Import Utils BasicSystem.

  Require Import RAlgEnvExt RAlgEnvExtEq.

  Local Open Scope algenvx_scope.
  
  (** Typing for NRA *)
  Section typ.
    Context {m:basic_model}.
    Context (τconstants:list (string*rtype)).

  Inductive algenvx_type : algenvx -> rtype -> rtype -> rtype -> Prop :=
  | ANXTID {τenv τ} :
      algenvx_type ANXID τenv τ τ
  | ANXTConst {τenv τin τout} c :
      data_type (normalize_data brand_relation_brands c) τout -> algenvx_type (ANXConst c) τenv τin τout
  | ANXTBinop {τenv τin τ₁ τ₂ τout} b op1 op2 :
      binOp_type b τ₁ τ₂ τout ->
      algenvx_type op1 τenv τin τ₁ ->
      algenvx_type op2 τenv τin τ₂ ->
      algenvx_type (ANXBinop b op1 op2) τenv τin τout
  | ANXTUnop {τenv τin τ τout} u op :
      unaryOp_type u τ τout ->
      algenvx_type op τenv τin τ ->
      algenvx_type (ANXUnop u op) τenv τin τout
  | ANXTMap {τenv τin τ₁ τ₂} op1 op2 :
      algenvx_type op1 τenv τ₁ τ₂ ->
      algenvx_type op2 τenv τin (Coll τ₁) ->
      algenvx_type (ANXMap op1 op2) τenv τin (Coll τ₂)
  | ANXTMapConcat {τenv τin τ₁ τ₂ τ₃} op1 op2 pf1 pf2 pf3 :
      algenvx_type op1 τenv (Rec Closed τ₁ pf1) (Coll (Rec Closed τ₂ pf2)) ->
      algenvx_type op2 τenv τin (Coll (Rec Closed τ₁ pf1)) ->
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      algenvx_type (ANXMapConcat op1 op2) τenv τin (Coll (Rec Closed τ₃ pf3))
  | ANXTProduct {τenv τin τ₁ τ₂ τ₃} op1 op2 pf1 pf2 pf3 :
      algenvx_type op1 τenv τin (Coll (Rec Closed τ₁ pf1)) ->
      algenvx_type op2 τenv τin (Coll (Rec Closed τ₂ pf2)) ->
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      algenvx_type (ANXProduct op1 op2) τenv τin (Coll (Rec Closed τ₃ pf3))
  | ANXTSelect {τenv τin τ} op1 op2 :
      algenvx_type op1 τenv τ Bool ->
      algenvx_type op2 τenv τin (Coll τ) ->
      algenvx_type (ANXSelect op1 op2) τenv τin (Coll τ)
  | ANXTDefault {τenv τin τ} op1 op2 :
      algenvx_type op1 τenv τin (Coll τ) ->
      algenvx_type op2 τenv τin (Coll τ) ->
      algenvx_type (ANXDefault op1 op2) τenv τin (Coll τ)
  | ANXTEither {τenv τl τr τout} opl opr :
      algenvx_type opl τenv τl τout ->
      algenvx_type opr τenv τr τout ->
      algenvx_type (ANXEither opl opr) τenv (Either τl τr) τout
  | ANXTEitherConcat {τin τenv rll pfl rlr pfr rlo pfo lo ro} op1 op2 pflo pfro :
      algenvx_type op1 τenv τin (Either (Rec Closed rll pfl) (Rec Closed rlr pfr)) ->
      algenvx_type op2 τenv τin (Rec Closed rlo pfo) ->
      rec_concat_sort rll rlo = lo ->
      rec_concat_sort rlr rlo = ro ->
      algenvx_type (ANXEitherConcat op1 op2) τenv  τin (Either (Rec Closed lo pflo) (Rec Closed ro pfro))                  
  | ANXTApp {τenv τin τ1 τ2} op2 op1 :
      algenvx_type op1 τenv τin τ1 ->
      algenvx_type op2 τenv τ1 τ2 ->
      algenvx_type (ANXApp op2 op1) τenv τin τ2
  | ANXTGetConstant {τenv τin τout} s :
      tdot τconstants s = Some τout ->
      algenvx_type (ANXGetConstant s) τenv τin τout
  | ANXTEnv {τenv τin} :
      algenvx_type ANXEnv τenv τin τenv
  | ANXTAppEnv {τenv τenv' τin τ2} op2 op1 :
      algenvx_type op1 τenv τin τenv' ->
      algenvx_type op2 τenv' τin τ2 ->
      algenvx_type (ANXAppEnv op2 op1) τenv τin τ2
  | ANXTMapEnv {τenv τin τ₂} op1 :
      algenvx_type op1 τenv τin τ₂ ->
      algenvx_type (ANXMapEnv op1) (Coll τenv) τin (Coll τ₂)
  | ANXTFlatMap {τenv τin τ₁ τ₂} op1 op2 :
      algenvx_type op1 τenv τ₁ (Coll τ₂) ->
      algenvx_type op2 τenv τin (Coll τ₁) ->
      algenvx_type (ANXFlatMap op1 op2) τenv τin (Coll τ₂)
  | ANXTJoin {τenv τin τ₀ τ₁ τ₂ τ₃} op0 op1 op2 pf1 pf2 pf3 :
      algenvx_type op0 τenv τ₀ Bool ->
      algenvx_type op1 τenv τin (Coll (Rec Closed τ₁ pf1)) ->
      algenvx_type op2 τenv τin (Coll (Rec Closed τ₂ pf2)) ->
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      τ₀ = (Rec Closed τ₃ pf3) ->
      algenvx_type (ANXJoin op0 op1 op2) τenv τin (Coll τ₀)
  | ANXTProject {τenv τin τ} op k sl pf1 pf2 :
      sublist sl (domain τ) ->
      algenvx_type op τenv τin (Coll (Rec k τ pf1)) ->
      algenvx_type (ANXProject sl op) τenv τin (Coll (Rec Closed (rproject τ sl) pf2)).
  End typ.

  Require Import RAlgEnv TAlgEnv.
  
  Notation "Op ▷ A >=> B ⊣ c ; E" := (algenvx_type c Op E A B) (at level 70).

  (** Type lemmas for individual algebraic expressions *)

  Context {m:basic_model}.
  
  (** Main typing soundness theorem for the NRA *)

  Lemma typed_algenvx_yields_typed_algenv {τc τenv τin τout} (op:algenvx):
    (op ▷ τin >=> τout ⊣ τc;τenv) -> algenv_type τc (algenv_of_algenvx op) τenv τin τout.
  Proof.
    revert τin τout τenv.
    induction op; intros;
    (* Takes care of all operators *)
    try (solve[inversion H; clear H; subst; repeat econstructor; eauto]).
  Qed.

  Lemma typed_algenv_yields_typed_algenvx {τc τenv τin τout} (op:algenvx):
    algenv_type τc (algenv_of_algenvx op) τenv τin τout -> (op ▷ τin >=> τout ⊣ τc;τenv).
  Proof.
    revert τin τout τenv.
    induction op; intros;
    (* Takes care of all core operators *)
    try (solve[inversion H; clear H; subst; repeat econstructor; eauto]).
    (* FlatMap *)
    - inversion H; clear H; subst.
      inversion H6; subst; clear H6.
      inversion H2; subst; clear H2.
      inverter; econstructor; eauto.
    (* Join *)
    - inversion H; subst; clear H.
      inversion H6; subst; clear H6.
      econstructor; eauto.
      rtype_equalizer.
      assert (exists pf, τ = Rec Closed (rec_concat_sort τ₁ τ₂) pf).
      apply Rec₀_eq_proj1_Rec. auto.
      elim H; clear H; intros. subst.
      apply rtype_fequal. simpl. reflexivity.
    (* Project *)
    - inversion H; subst; clear H.
      inversion H2; subst; clear H2.
      inversion H7; subst; clear H7.
      inversion H1; subst; clear H1.
      econstructor; eauto.
      
      Grab Existential Variables.
      eauto.
  Qed.
    
  Theorem typed_algenv_iff_typed_algenvx {τc τenv τin τout} (op:algenvx):
    (op ▷ τin >=> τout ⊣ τc;τenv) <-> algenv_type τc (algenv_of_algenvx op) τenv τin τout.
  Proof.
    split.
    apply typed_algenvx_yields_typed_algenv.
    apply typed_algenv_yields_typed_algenvx.
  Qed.
    
  Theorem typed_algenvx_yields_typed_data {τc τenv τin τout} c (env:data) (d:data) (op:algenvx):
    bindings_type c τc ->
    (env ▹ τenv) -> (d ▹ τin) -> (op ▷ τin >=> τout ⊣ τc;τenv) ->
    (exists x, (fun_of_algenvx brand_relation_brands c op env d = Some x /\ (x ▹ τout))).
  Proof.
    intros.
    unfold fun_of_algenvx.
    apply (@typed_algenv_yields_typed_data m τc τenv τin τout); try assumption.
    apply typed_algenvx_yields_typed_algenv. assumption.
  Qed.

  (* Evaluation into single value for typed algebra *)

  (** Corrolaries of the main type soudness theorem *)

  Definition typed_algenvx_total {τc τenv τin τout} (op:algenvx) (HOpT: op ▷ τin >=> τout ⊣ τc;τenv) c (env:data) (d:data):
    bindings_type c τc ->
    (env ▹ τenv) ->
    (d ▹ τin) ->
    { x:data | x ▹ τout }.
  Proof.
    intros Hc Henv.
    intros HdT.
    generalize (typed_algenvx_yields_typed_data c env d op Hc Henv HdT HOpT).
    intros.
    destruct (fun_of_algenvx brand_relation_brands c op env d).
    assert (data_type d0 τout).
    - inversion H. inversion H0. inversion H1. trivial.
    - exists d0. trivial.
    - cut False. intuition. inversion H.
      destruct H0. inversion H0.
  Defined.

  Definition talgenvx_eval {τc τenv τin τout} (op:algenvx) (HOpT: op ▷ τin >=> τout ⊣ τc;τenv) c (env:data) (d:data):
    bindings_type c τc ->
    (env ▹ τenv) -> (d ▹ τin) -> data.
  Proof.
    intros Hc Henv.
    intros HdT.
    destruct (typed_algenvx_total op HOpT c env d Hc Henv HdT).
    exact x.
  Defined.

End TAlgEnvExt.

(* Typed algebraic plan *)

Notation "Op ▷ A >=> B ⊣ c ; E" := (algenvx_type c Op E A B) (at level 70).
Notation "Op @▷ d ⊣ c ; e" := (talgenvx_eval c Op e d) (at level 70).

(* Used to prove type portion of typed directed rewrites *)
  
Hint Constructors algenvx_type.
Hint Constructors unaryOp_type.
Hint Constructors binOp_type.

Ltac inverterx := 
  match goal with
    | [H:Coll _ = Coll _ |- _] => inversion H; clear H
    | [H: `?τ₁ = Coll₀ (`?τ₂) |- _] => rewrite (Coll_right_inv τ₁ τ₂) in H; subst
    | [H:  Coll₀ (`?τ₂) = `?τ₁ |- _] => symmetry in H
    (* Note: do not generalize too hastily on unaryOp/binOp constructors *)
    | [H:ANXID ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXEnv ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXMap _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXMapConcat _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXMapEnv _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXDefault _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXApp _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXAppEnv _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXEither _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXEitherConcat _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXProduct _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXSelect _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXUnop _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXBinop _ _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXConst _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXProject _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXFlatMap _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:ANXJoin _ _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H: (_,_)  = (_,_) |- _ ] => inversion H; clear H
    | [H: map (fun x2 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x2, ` (snd x2))) ?x0 = [] |- _] => apply (map_rtype_nil x0) in H; simpl in H; subst
    | [H: (map
             (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                (fst x, proj1_sig (snd x))) _)
          = 
          (map
             (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                (fst x, proj1_sig (snd x))) _) |- _ ] =>
      apply map_rtype_fequal in H; trivial
    | [H:Rec _ _ _ = Rec _ _ _ |- _ ] => generalize (Rec_inv H); clear H; intro H; try subst
    | [H: context [(_::nil) = map 
                                (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                   (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
                                                                                         
    | [H: context [map 
                     (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                        (fst x, proj1_sig (snd x))) _ = (_::nil) ] |- _] => apply map_eq_cons in H;
        destruct H as [? [? [? [??]]]]
    | [H: Coll₀ _ = Coll₀ _ |- _ ] => inversion H; clear H
    | [H: Rec₀ _ _ = Rec₀ _ _ |- _ ] => inversion H; clear H
    | [H: _ ▷ _ >=> snd ?x ⊣  _ ;_ |- _] => destruct x; simpl in *; subst
    | [H:unaryOp_type AColl _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type AFlatten _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ARec _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ADot _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ARecProject _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type (ARecRemove _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type ALeft _ _ |- _ ] => inversion H; clear H; subst
    | [H:unaryOp_type ARight _ _ |- _ ] => inversion H; clear H; subst
    | [H:binOp_type AConcat _ _ _ |- _ ] => inversion H; clear H
    | [H:binOp_type AAnd _ _ _ |- _ ] => inversion H; clear H
    | [H:binOp_type AMergeConcat _ _ _ |- _ ] => inversion H; clear H
  end; try rtype_equalizer; try assumption; try subst; simpl in *; try inverter.

(* inverts, then tries and solve *)
Ltac inferer := try inverter; subst; try eauto.
  
(* simplifies when a goal evaluates an expression over well-typed data *)
Ltac input_well_typed :=
  repeat progress
         match goal with
           | [HO:?op ▷ ?τin >=> ?τout ⊣  ?τc ; ?τenv,
              HI:?x ▹ ?τin,
              HE:?env ▹ ?τenv,
              HC:bindings_type ?c ?τc 
              |- context [(fun_of_algenv ?h ?c ?op ?env ?x)]] =>
             let xout := fresh "dout" in
             let xtype := fresh "τout" in
             let xeval := fresh "eout" in
             destruct (typed_algenv_yields_typed_data _ _ _ op HC HE HI HO)
               as [xout [xeval xtype]]; rewrite xeval in *; simpl
         end.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
