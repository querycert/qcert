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

Section RAlgEnvEq.
  Require Import String List Compare_dec.
  
  Require Import Utils BasicRuntime.
  Require Import NRARuntime.
  Require Import RAlgEnv RAlgEnvIgnore.

  Local Open Scope string.
  Local Open Scope algenv_scope.

  Context {fruntime:foreign_runtime}.

  (* Equivalence for environment-enabled algebra *)
  
  Definition algenv_eq (op1 op2:algenv) : Prop :=
    forall
      (h:list(string*string))
      (c:list (string*data))
      (dn_c:Forall (fun d => data_normalized h (snd d)) c)
      (env:data)
      (dn_env:data_normalized h env)
      (x:data)
      (dn_x:data_normalized h x),
      h ⊢ₑ op1 @ₑ x ⊣ c;env = h ⊢ₑ op2 @ₑ x ⊣ c;env.

  Definition alg_eqenv (op1 op2:algenv) : Prop :=
    forall
      (h:list(string*string))
      (c:list (string*data))
      (dn_c:Forall (fun d => data_normalized h (snd d)) c)
      (env:data)
      (dn_env:data_normalized h env)
      (x:data)
      (dn_x:data_normalized h x),
      h ⊢ (alg_of_algenv op1) @ₐ (pat_context_data (drec (rec_sort c)) env x) = h ⊢ (alg_of_algenv op2) @ₐ (pat_context_data (drec (rec_sort c)) env x).

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  
  Global Instance algenv_equiv : Equivalence algenv_eq.
  Proof.
    constructor.
    - unfold Reflexive, algenv_eq.
      intros; reflexivity.
    - unfold Symmetric, algenv_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; reflexivity.
    - unfold Transitive, algenv_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; rewrite (H0 h c dn_c env dn_env x0) by trivial; reflexivity.
  Qed.

  Global Instance alg_eqenv_equiv : Equivalence alg_eqenv.
  Proof.
    constructor.
    - unfold Reflexive, alg_eqenv.
      intros; reflexivity.
    - unfold Symmetric, alg_eqenv.
      intros; rewrite (H h c dn_c env dn_env x0) by trivial; reflexivity.
    - unfold Transitive, alg_eqenv.
      intros; rewrite (H h c dn_c env dn_env x0) by trivial; rewrite (H0 h c dn_c env dn_env x0) by trivial; reflexivity.
  Qed.

  Hint Resolve dnrec_sort.
    
  Lemma alg_eqenv_same (op1 op2:algenv) :
    algenv_eq op1 op2 <-> alg_eqenv op1 op2.
  Proof.
    split; unfold algenv_eq, alg_eqenv; intros.
    - repeat rewrite <- unfold_env_alg by trivial.
      rewrite H; trivial.
      apply Forall_sorted.
      trivial.
    - repeat rewrite unfold_env_alg_sort by trivial.
      rewrite H; trivial.
  Qed.
    
  (* all the extended algebraic constructors are proper wrt. equivalence *)

  (* ANID *)
  Global Instance anid_proper : Proper algenv_eq ANID.
  Proof.
    unfold Proper, respectful, algenv_eq.
    reflexivity.
  Qed.

  Global Instance anideq_proper : Proper alg_eqenv ANID.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anid_proper.
  Qed.

  (* ANConst *)
  Global Instance anconst_proper : Proper (eq ==> algenv_eq) ANConst.
  Proof.
    unfold Proper, respectful, algenv_eq; intros.
    rewrite H; reflexivity.
  Qed.

  Global Instance anconsteq_proper : Proper (eq ==> alg_eqenv) ANConst.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anconst_proper; assumption.
  Qed.

  (* ANBinOp *)
    
  Global Instance anbinop_proper : Proper (binop_eq ==> algenv_eq ==> algenv_eq ==> algenv_eq) ANBinop.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    generalize abinop_proper.
    unfold Proper, respectful, algenv_eq, alg_eq; intros; simpl.
    specialize (H2 x y H).
    rewrite H0 by trivial; rewrite H1 by trivial.
    rewrite unfold_env_alg_sort by trivial; simpl.
    rewrite unfold_env_alg_sort by trivial; simpl.
    specialize (H2 (alg_of_algenv y0) (alg_of_algenv y0)).
    assert ((forall (h0 : list (string * string)) (x3 : data),
               data_normalized h0 x3 ->
               h0 ⊢ alg_of_algenv y0 @ₐ x3 = h0 ⊢ alg_of_algenv y0 @ₐ x3)).
    intros; reflexivity.
    specialize (H2 H3).
    specialize (H2 (alg_of_algenv y1) (alg_of_algenv y1)).
    assert ((forall (h0 : list (string * string)) (x3 : data),
               data_normalized h0 x3 ->
               h0 ⊢ alg_of_algenv y1 @ₐ x3 = h0 ⊢ alg_of_algenv y1 @ₐ x3)).
    intros; reflexivity.
    specialize (H2 H4).
    apply (H2 h).
    eauto.
  Qed.

  Global Instance anbinopeq_proper : Proper (binop_eq ==> alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANBinop.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anbinop_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

  (* ANUnop *)
  Global Instance anunop_proper : Proper (unaryop_eq ==> algenv_eq ==> algenv_eq) ANUnop.
  Proof.
    unfold Proper, respectful, algenv_eq; simpl; intros.
    rewrite H0 by trivial.
    rewrite unfold_env_alg_sort by trivial; simpl.
    generalize (aunop_proper).
    unfold Proper, respectful, algenv_eq, alg_eq; simpl; intros.
    specialize (H1 x y H).
    specialize (H1 (alg_of_algenv y0) (alg_of_algenv y0)).
    assert ((forall (h0 : list (string * string)) (x3 : data),
                   data_normalized h0 x3 ->
               h0 ⊢ alg_of_algenv y0 @ₐ x3 = h0 ⊢ alg_of_algenv y0 @ₐ x3)).
    intros; reflexivity.
    specialize (H1 H2).
    apply (H1 h).
    eauto.
  Qed.

  Hint Resolve data_normalized_dcoll_in.

  Global Instance anunopeq_proper : Proper (unaryop_eq ==> alg_eqenv ==> alg_eqenv) ANUnop.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anunop_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

  (* ANMap *)
  Global Instance anmap_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANMap.
  Proof.
    unfold Proper, respectful, algenv_eq; simpl; intros.
    rewrite H0 by trivial.
    rewrite unfold_env_alg_sort by trivial; simpl.
    case_eq (fun_of_alg h (alg_of_algenv y0) (pat_context_data (drec (rec_sort c)) env x1)); simpl; trivial.
    destruct d; try reflexivity; simpl; intros.
    f_equal. apply rmap_ext; intros.
    apply H; eauto.
  Qed.

  Global Instance anmapeq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANMap.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anmap_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

  (* ANMapConcat *)
  Global Instance anmapconcat_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANMapConcat.
  Proof.
    unfold Proper, respectful, algenv_eq; simpl; intros.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl; intros.
    f_equal.
    apply rmap_concat_ext; intros.
    apply H; eauto.
    
  Qed.

  Global Instance anmapconcateq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANMapConcat.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anmapconcat_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.
  
  (* ANProduct *)
  Global Instance anproduct_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANProduct.
  Proof.
    unfold Proper, respectful, algenv_eq; simpl; intros.
    rewrite H by trivial; rewrite H0 by trivial.
    rewrite unfold_env_alg_sort by trivial; simpl.
    rewrite unfold_env_alg_sort by trivial; simpl.
    generalize aproduct_proper.
    unfold Proper, respectful, alg_eq; simpl; intros.
    specialize (H1 (alg_of_algenv y) (alg_of_algenv y)).
    assert ((forall (h0 : list (string * string)) (x3 : data),
               data_normalized h0 x3 ->
               h0 ⊢ alg_of_algenv y @ₐ x3 = h0 ⊢ alg_of_algenv y @ₐ x3))
      by (intros; reflexivity).
    assert ((forall (h0 : list (string * string)) (x3 : data),
               data_normalized h0 x3 ->
               h0 ⊢ alg_of_algenv y0 @ₐ x3 = h0 ⊢ alg_of_algenv y0 @ₐ x3))
      by (intros; reflexivity).
    specialize (H1 H2 (alg_of_algenv y0) (alg_of_algenv y0) H3).
    apply (H1 h).
    eauto.      
  Qed.

  Global Instance anmapproducteq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANProduct.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anproduct_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.
  
  (* ANSelect *)
  Global Instance anselect_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANSelect.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); intros; trivial.
    destruct d; try reflexivity; simpl.
    f_equal.
    apply lift_filter_ext; intros.
    rewrite H; eauto.
  Qed.

  Global Instance anselecteq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANSelect.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anselect_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

  (* ANDefault *)
  Global Instance andefault_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANDefault.
  Proof.
    unfold Proper, respectful, algenv_eq; simpl; intros.
    rewrite H by trivial; rewrite H0 by trivial.
    rewrite unfold_env_alg_sort by trivial; simpl.
    rewrite unfold_env_alg_sort by trivial; simpl.
    generalize adefault_proper.
    unfold Proper, respectful, algenv_eq, alg_eq; simpl; intros.
    specialize (H1 (alg_of_algenv y) (alg_of_algenv y)).
    assert ((forall (h0 : list (string * string)) (x3 : data),
               data_normalized h0 x3 ->
               h0 ⊢ alg_of_algenv y @ₐ x3 = h0 ⊢ alg_of_algenv y @ₐ x3)).
    intros; reflexivity.
    specialize (H1 H2).
    specialize (H1 (alg_of_algenv y0) (alg_of_algenv y0)).
    assert ((forall (h0 : list (string * string)) (x3 : data),
               data_normalized h0 x3 ->
               h0 ⊢ alg_of_algenv y0 @ₐ x3 = h0 ⊢ alg_of_algenv y0 @ₐ x3)).
    intros; reflexivity.
    specialize (H1 H3).
    apply (H1 h); eauto.
  Qed.

  Global Instance andefaulteq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANDefault.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply andefault_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

    (* ANEither *)
  Global Instance aneither_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANEither.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    destruct x1; trivial; inversion dn_x; subst; eauto.
  Qed.

    Global Instance aneithereq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANEither.
  Proof.
    unfold Proper, respectful, alg_eqenv; intros; simpl.
    destruct x1; simpl; trivial; inversion dn_x; subst.
    + apply H; trivial.
    + apply H0; trivial.
  Qed.

      (* ANEitherConcat *)
  Global Instance aneitherconcat_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANEitherConcat.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    rewrite H,H0 by trivial. repeat match_destr.
  Qed.

    Global Instance aneitherconcateq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANEitherConcat.
  Proof.
    unfold Proper, respectful, alg_eqenv; intros; simpl.
    rewrite H,H0 by trivial. repeat match_destr.
  Qed.

  (* ANApp *)
  Global Instance anapp_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANApp.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); intros; trivial; simpl.
    eauto.
  Qed.

  Global Instance anappeq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANApp.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anapp_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

  (* ANGetConstant *)
  Global Instance angetconstant_proper s : Proper (algenv_eq) (ANGetConstant s).
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    reflexivity.
  Qed.

  Global Instance angetconstanteq_proper s : Proper (alg_eqenv) (ANGetConstant s).
  Proof.
    unfold Proper, respectful; intros.
    reflexivity.
  Qed.
  
  (* ANEnv *)
  Global Instance anenv_proper : Proper (algenv_eq) ANEnv.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    reflexivity.
  Qed.

  Global Instance anenveq_proper : Proper (alg_eqenv) ANEnv.
  Proof.
    unfold Proper, respectful; intros.
    reflexivity.
  Qed.

  (* ANAppEnv *)
  Global Instance anappenv_proper : Proper (algenv_eq ==> algenv_eq ==> algenv_eq) ANAppEnv.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); intros; simpl; trivial.
    apply H; eauto.
  Qed.

  Global Instance anappenveq_proper : Proper (alg_eqenv ==> alg_eqenv ==> alg_eqenv) ANAppEnv.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anappenv_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

  (* ANMapEnv *)
  Global Instance anmapenv_proper : Proper (algenv_eq ==> algenv_eq) ANMapEnv.
  Proof.
    unfold Proper, respectful, algenv_eq; intros; simpl.
    destruct env; try reflexivity; simpl.
    f_equal.
    apply rmap_ext; intros.
    eauto.
  Qed.

  Global Instance anmapenveq_proper : Proper (alg_eqenv ==> alg_eqenv) ANMapEnv.
  Proof.
    unfold Proper, respectful; intros.
    rewrite <- alg_eqenv_same; apply anmapenv_proper;
    try assumption; rewrite alg_eqenv_same; assumption.
  Qed.

  Lemma algenv_of_alg_proper : Proper (alg_eq ==> algenv_eq) algenv_of_alg.
  Proof.
    unfold Proper, respectful, alg_eq, algenv_eq.
    intros.
    repeat rewrite <- fun_of_algenv_of_alg.
    auto.
  Qed.
  
  Notation "X ≡ₑ Y" := (algenv_eq X Y) (at level 90).

  
  
  Lemma algenv_of_alg_proper_inv x y :
    (algenv_of_alg x ≡ₑ algenv_of_alg y)%algenv ->
    (x ≡ₐ y)%alg.
  Proof.
    unfold alg_eq, algenv_eq.
    intros.
    assert (eq1:forall (h : list (string * string))
                       (c:list (string *data)),
                  Forall (fun d : string * data => data_normalized h (snd d)) c ->
                  forall (env:data),
                  data_normalized h env ->
                  forall (x0 : data),
                  data_normalized h x0 ->
                  (h ⊢ (alg_of_algenv (algenv_of_alg x)) @ₐ (pat_context_data (drec (rec_sort c)) env x0))%alg =
                  (h ⊢ (alg_of_algenv (algenv_of_alg y)) @ₐ (pat_context_data (drec (rec_sort c)) env x0))%alg ).
    { intros. repeat rewrite <- unfold_env_alg_sort; trivial. auto. }
    assert (eq2:forall (h : list (string * string))
                       (x0 : data),
                  data_normalized h x0 ->
                  h ⊢ deenv_alg (algenv_of_alg x) @ₐ x0 =
                  h ⊢ deenv_alg (algenv_of_alg y) @ₐ x0).
    { intros. specialize (eq1 h0 nil (Forall_nil _) dunit (dnunit _) x1 H1 ).
      do 2 rewrite is_nra_deenv in eq1 by
          apply algenv_of_alg_is_nra; trivial.
    }
    specialize (eq2 h x0).
    repeat rewrite deenv_alg_algenv_of_alg in eq2.
    auto.
  Qed.

  Lemma alg_of_algenv_proper_inv x y :
    (alg_of_algenv x ≡ₐ alg_of_algenv y)%alg ->
    (x ≡ₑ y)%algenv.
  Proof.
    unfold Proper, respectful; intros.
    (* apply algenv_of_alg_proper in H. *)
    unfold alg_eq, algenv_eq in *.
    intros.
    specialize (H h (pat_context_data (drec (rec_sort c)) env x0)).
    repeat rewrite <- unfold_env_alg_sort in H by trivial.
    auto.
  Qed.

  Definition algenv_always_ensures (P:data->Prop) (q:algenv) :=
    forall
      (h:list(string*string))
      (c:list (string*data))
      (dn_c:Forall (fun d => data_normalized h (snd d)) c)
      (env:data)
      (dn_env:data_normalized h env)
      (x:data)
      (dn_x:data_normalized h x)
      (d:data),
      h ⊢ₑ q @ₑ x ⊣ c;env = Some d -> P d.

End RAlgEnvEq.

Notation "X ≡ₑ Y" := (algenv_eq X Y) (at level 90) : algenv_scope.                             (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
