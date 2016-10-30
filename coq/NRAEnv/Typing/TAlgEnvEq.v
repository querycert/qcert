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

Section TAlgEnvEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Require Import List.
  Require Import String.

  Require Import Utils BasicSystem.
  Require Import RAlgEnv RAlgEnvEq.
  Require Import TAlgEnv.

  Local Open Scope algenv_scope.
  
  (* Equivalence relation between *typed* algebraic plans.  Two
     well-typed plans are equivalent iff they return the same value
     for every well-typed input.  *)

  Definition typed_algenv {m:basic_model} τc τenv τin τout := {op:algenv|op ▷ τin >=> τout ⊣ τc;τenv}.

  Definition talgenv_eq {m:basic_model} {τc τenv τin τout} (op1 op2:typed_algenv τc τenv τin τout) : Prop :=
    forall (x:data) c (env: data)
           (dt_x:x ▹ τin)
           (dt_c:bindings_type c τc)
           (dt_env:env ▹ τenv),
        brand_relation_brands ⊢ₑ (proj1_sig op1) @ₑ x ⊣ c;env
        = brand_relation_brands ⊢ₑ (proj1_sig op2) @ₑ x ⊣ c;env.

  Global Instance talgenv_equiv {m:basic_model} {τc} {τenv τin τout:rtype} : Equivalence (@talgenv_eq m τc τenv τin τout).
  Proof.
    constructor.
    - unfold Reflexive, talgenv_eq; intros.
      reflexivity.
    - unfold Symmetric, talgenv_eq; intros.
      rewrite (H x0 c env dt_x dt_c dt_env); reflexivity.
    - unfold Transitive, talgenv_eq; intros.
      intros; rewrite (H x0 c env dt_x dt_c dt_env); rewrite (H0 x0 c env dt_x dt_c dt_env); reflexivity.
  Qed.

  Notation "t1 ⇝ₑ t2 ⊣ τc ; tenv" := (typed_algenv τc tenv t1 t2) (at level 80).
  Notation "X ≡τₑ Y" := (talgenv_eq X Y) (at level 80).               (* ≡ = \equiv *)

  Hint Resolve data_type_normalized.
  Hint Resolve bindings_type_Forall_normalized.

  Lemma algenv_eq_impl_talgenv_eq {m:basic_model} {τc τenv τin τout} (op1 op2: τin ⇝ₑ τout ⊣ τc;τenv) :
    `op1 ≡ₑ `op2 -> op1 ≡τₑ op2.
  Proof.
    unfold talgenv_eq, algenv_eq; intros.
    eapply H; eauto.
  Qed.

  Lemma algenv_eq_pf_irrel {m:basic_model} {op} {τin τout τc τenv} (pf1 pf2: op ▷ τin >=> τout ⊣ τc;τenv) :
    talgenv_eq (exist _ op pf1) (exist _ op pf2).
  Proof.
    red; intros; simpl.
    reflexivity.
  Qed.

  (* A different kind of equivalence for rewrites *)
  Context {m:basic_model}.

  Definition talgenv_rewrites_to (op1 op2:algenv) : Prop :=
    forall τc (τenv τin τout:rtype),
      op1 ▷ τin >=> τout ⊣ τc;τenv ->
                              (op2 ▷ τin >=> τout ⊣ τc;τenv)
                              /\ (forall (x:data) c
                                         env
                                         (dt_x:x ▹ τin)
                                         (dt_c:bindings_type c τc)
                                         (dt_env:env ▹ τenv),
                                    brand_relation_brands ⊢ₑ op1 @ₑ x ⊣ c;env
                                 = brand_relation_brands ⊢ₑ op2 @ₑ x ⊣ c;env).
  
  Notation "op1 ⇒ op2" := (@talgenv_rewrites_to op1 op2) (at level 80).
  
  Lemma rewrites_typed_with_untyped (op1 op2:algenv) :
    op1 ≡ₑ op2 ->
    (forall {τc} {τenv τin τout:rtype}, op1 ▷ τin >=> τout ⊣ τc;τenv -> op2 ▷ τin >=> τout ⊣ τc;τenv)
    -> op1 ⇒ op2.
  Proof.
    intros.
    unfold talgenv_rewrites_to; simpl; intros.
    split; eauto.
  Qed.

  (* Rewrite implies type-based equivalence! *)
  Lemma talg_rewrites_eq_is_typed_eq {τc} {τenv τin τout:rtype} (op1 op2:typed_algenv τc τenv τin τout):
    (`op1 ⇒ `op2) -> @talgenv_eq m τc τenv τin τout op1 op2.
  Proof.
    unfold talgenv_rewrites_to, talgenv_eq; intros.
    dependent induction op1.
    dependent induction op2; simpl in *.
    elim (H τc τenv τin τout); clear H; intros.
    apply (H0 x1 c env dt_x dt_c dt_env).
    assumption.
  Qed.
  
  (****************
   * Proper stuff *
   ****************)

  Require Import ROpsEq RAlgEnvEq.
  
  Global Instance  talgenv_rewrites_to_pre : PreOrder talgenv_rewrites_to.
  Proof.
    constructor; red; intros.
    - unfold talgenv_rewrites_to; intros.
      split; try assumption; intros.
      reflexivity.
    - unfold talgenv_rewrites_to in *; intros.
      specialize (H τc τenv τin τout H1).
      elim H; clear H; intros.
      specialize (H0 τc τenv τin τout H).
      elim H0; clear H0; intros.
      split; try assumption; intros.
      rewrite (H2 x0 c env); try assumption.
      rewrite (H3 x0 c env); try assumption.
      reflexivity.
  Qed.

  (* ANID *)

  Global Instance anid_tproper:
    Proper talgenv_rewrites_to ANID.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    split; [assumption|reflexivity].
  Qed.

  (* ANConst *)

  Global Instance anconst_tproper:
    Proper (eq ==> talgenv_rewrites_to) ANConst.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    rewrite <- H; clear H.
    split; [assumption|reflexivity].
  Qed.

  (* ANBinop *)

  Global Instance anbinop_tproper:
    Proper (eq ==> talgenv_rewrites_to
               ==> talgenv_rewrites_to
               ==> talgenv_rewrites_to) ANBinop.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    rewrite H in *; clear H.
    algenv_inferer.
    specialize (H0 τc τenv τin τ₁ H9); elim H0; clear H0 H9; intros.
    specialize (H1 τc τenv τin τ₂ H10); elim H1; clear H1 H10; intros.
    econstructor; eauto; intros.
    rewrite (H0 x2 c env dt_x dt_c dt_env); rewrite (H2 x2 c env dt_x dt_c dt_env); reflexivity.
  Qed.
  
  (* ANUnop *)

  Global Instance anunop_tproper :
    Proper (eq ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANUnop.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin τ H8); elim H0; clear H0 H8; intros.
    econstructor; eauto.
    intros.
    rewrite (H0 x c env dt_x dt_c dt_env); reflexivity.
  Qed.

  (* ANMap *)

  Global Instance anmap_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANMap.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin (Coll τ₁) H8); elim H0; clear H0 H8; intros.
    specialize (H τc τenv τ₁ τ₂ H4); elim H; clear H H4; intros.
    econstructor; eauto; intros.
    rewrite (H1 x1 c env dt_x dt_c dt_env).
    input_well_typed.
    dtype_inverter.
    inversion τout.
    rtype_equalizer. subst. clear eout τout.
    induction dout; try reflexivity; simpl in *.
    f_equal.
    inversion H5; clear H5; subst.
    rewrite (H2 a c env H6 dt_c dt_env).
    input_well_typed.
    unfold lift in *.
    specialize (IHdout H7).
    destruct (rmap (fun_of_algenv brand_relation_brands c x env) dout); destruct (rmap (fun_of_algenv brand_relation_brands c y env) dout); congruence.
  Qed.

  (* ANMapConcat *)
  
  Global Instance anmapconcat_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANMapConcat.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin (Coll (Rec Closed τ₁ pf1)) H5); elim H0; clear H0 H5; intros.
    specialize (H τc τenv (Rec Closed τ₁ pf1) (Coll (Rec Closed τ₂ pf2)) H4); elim H; clear H H4; intros.
    econstructor; eauto; intros.
    rewrite (H1 x1 c env dt_x dt_c dt_env).
    input_well_typed.
    dtype_inverter.
    inversion τout.
    rtype_equalizer. subst. clear eout τout.
    induction dout; try reflexivity; simpl in *.
    f_equal.
    inversion H5; clear H5; subst.
    dtype_inverter. subst.
    assert (data_type a (Rec Closed τ₁ pf1)).
    - assert (Rec Closed τ₁ pf1 = Rec Closed τ₁ x2) by (apply rtype_fequal; reflexivity).
      rewrite H3 in *; clear H3; assumption.
    - unfold rmap_concat in *; simpl in *.
      unfold oomap_concat in *; simpl in *.
      rewrite (H2 a c env H3 dt_c dt_env).
      input_well_typed.
      dtype_inverter.
      specialize (IHdout H8).
      destruct ((oflat_map
                   (fun a0 : data =>
                      match brand_relation_brands ⊢ₑ x @ₑ a0 ⊣ c;env with
                        | Some (dcoll y1) => omap_concat a0 y1
                        | _ => None
                      end) dout));
        destruct ((oflat_map
                     (fun a0 : data =>
                        match brand_relation_brands ⊢ₑ y @ₑ a0 ⊣ c;env with
                          | Some (dcoll y1) => omap_concat a0 y1
                          | _ => None
                        end) dout));
        try congruence; destruct (omap_concat (drec a) dout0); try congruence;
        inversion IHdout; reflexivity.
  Qed.

  (* ANProduct *)
  
  Global Instance anproduct_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANProduct.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin (Coll (Rec Closed τ₂ pf2)) H5); elim H0; clear H0 H5; intros.
    specialize (H τc τenv τin (Coll (Rec Closed τ₁ pf1)) H4); elim H; clear H H4; intros.
    econstructor; eauto; intros.
    rewrite (H1 x1 c env dt_x dt_c dt_env).
    rewrite (H2 x1 c env dt_x dt_c dt_env).
    reflexivity.
  Qed.
  
  (* ANSelect *)
  
  Global Instance anselect_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANSelect.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin (Coll τ) H8); elim H0; clear H0 H8; intros.
    specialize (H τc τenv τ Bool H4); elim H; clear H H4; intros.
    econstructor; eauto; intros.
    rewrite (H1 x1 c env dt_x dt_c dt_env).
    input_well_typed.
    dtype_inverter.
    apply f_equal.
    apply lift_filter_eq; auto; simpl; intros.
    dtype_enrich.
    rewrite (H2 a c env H4 dt_c dt_env).
    reflexivity.
  Qed.

  (* ANDefault *)

  Global Instance andefault_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANDefault.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin (Coll τ) H8); elim H0; clear H0 H8; intros.
    specialize (H τc τenv τin (Coll τ) H4); elim H; clear H H4; intros.
    econstructor; eauto; intros.
    rewrite (H2 x1 c env dt_x dt_c dt_env).
    rewrite (H1 x1 c env dt_x dt_c dt_env).
    reflexivity.
  Qed.

  (* ANEither *)
  Global Instance aneither_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANEither.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    inversion H1; subst.
    specialize (H0  _ _ _ _ H8); elim H0; clear H0 H8; intros.
    specialize (H _ _ _ _ H4); elim H; intros.
    econstructor; eauto; intros. simpl.
    inversion dt_x; rtype_equalizer.
    - subst; eauto.
    - subst; eauto.
  Qed.

    (* ANEitherConcat *)
  Global Instance aneitherconcat_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANEitherConcat.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    inversion H1; clear H1; subst.
    specialize (H0 _ _ _ _ H5); elim H0; clear H0 H5; intros.
    specialize (H _ _ _ _ H4); elim H; clear H H4; intros.
    econstructor; eauto; intros. simpl.
    rewrite H1, H2; trivial.
  Qed.
  
  (* ANApp *)

  Global Instance anapp_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANApp.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin τ1 H4); elim H0; clear H0 H4; intros.
    specialize (H τc τenv τ1 τout H8); elim H; clear H H8; intros.
    econstructor; eauto; intros.
    rewrite (H1 x1 c env dt_x dt_c dt_env).
    input_well_typed.
    rewrite (H2 dout c env τout0 dt_c dt_env).
    auto.
  Qed.

  (* ANEnv *)

  Global Instance anenv_tproper:
    Proper talgenv_rewrites_to ANEnv.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    split; [assumption|reflexivity].
  Qed.

  (* ANAppEnv *)

  Global Instance anappenv_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to ==> talgenv_rewrites_to) ANAppEnv.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H0 τc τenv τin τenv' H4); elim H0; clear H0 H4; intros.
    specialize (H τc τenv' τin τout H8); elim H; clear H H8; intros.
    econstructor; eauto; intros.
    rewrite (H1 x1 c env dt_x dt_c dt_env).
    input_well_typed.                           
    rewrite (H2 x1 c dout dt_x dt_c τout0).
    auto.
  Qed.

  (* ANMapEnv *)

  Global Instance anmapenv_tproper :
    Proper (talgenv_rewrites_to ==> talgenv_rewrites_to) ANMapEnv.
  Proof.
    unfold Proper, respectful, talgenv_rewrites_to; intros.
    algenv_inferer.
    specialize (H τc τenv0 τin τ₂ H2); elim H; clear H H2; intros.
    econstructor; eauto; intros.
    dtype_inverter.
    f_equal.
    apply rmap_ext; intros.
    rewrite (H0 x0 c x1 dt_x dt_c).
    reflexivity.
    inversion dt_env.
    rtype_equalizer. subst.
    rewrite Forall_forall in *; auto.
  Qed.

End TAlgEnvEq.

Notation "op1 ⇒ op2" := (talgenv_rewrites_to op1 op2) (at level 80) : algenv_scope.
Notation "h ⊧ t1 ⇝ t2 ⊣ c ; tenv" := (@typed_algenv h c tenv t1 t2) (at level 80) : algenv_scope.
Notation "X ≡τ Y" := (talgenv_eq X Y) (at level 80) : algenv_scope.               (* ≡ = \equiv *)
Notation "X ≡τ' Y" := (talgenv_eq (exist _ _ X) (exist _ _ Y)) (at level 80) : algenv_scope.               (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
