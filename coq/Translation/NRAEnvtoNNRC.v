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

Section NRAEnvtoNNRC.

  (* begin hide *)
  Require Import String.
  Require Import List.
  Require Import EquivDec.
  Require Import Compare_dec.

  Require Import Utils BasicRuntime.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime.

  (* end hide *)

  Context {fruntime:foreign_runtime}.

  (** Translation from NRAEnv to Named Nested Relational Calculus Extended *)
  Fixpoint nraenv_to_nnrc_ext (op:nraenv) (varid varenv:var) : nnrc :=
    match op with
    (* [[ ID ]]_vid,venv == vid *)
    | NRAEnvID => NNRCVar varid
    (* [[ Const ]]_vid,venv == Const *)
    | NRAEnvConst rd => NNRCConst rd
    (* [[ op1 ⊕ op2 ]]_vid,venv == [[ op1 ]]_vid,venv ⊕ [[ op2 ]]_vid,venv *)
    | NRAEnvBinop bop op1 op2 =>
      NNRCBinop bop (nraenv_to_nnrc_ext op1 varid varenv) (nraenv_to_nnrc_ext op2 varid varenv)
    (* [[ UOP op1 ]]_vid,venv = UOP [[ op1 ]]_vid,venv *)
    | NRAEnvUnop uop op1 =>
      NNRCUnop uop (nraenv_to_nnrc_ext op1 varid varenv)
    (* [[ χ⟨ op1 ⟩( op2 ) ]]_vid,venv = { [[ op1 ]]_t,venv | t ∈ [[ op2 ]]_vid,venv } *)
    | NRAEnvMap op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tmap$" (varid::varenv::nil) in
      NNRCFor t nrc2 (nraenv_to_nnrc_ext op1 t varenv)
    (* [[ ⋈ᵈ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op1 ]]_t1,venv } | t1 ∈ [[ op2 ]]_vid,venv } *)
    | NRAEnvMapConcat op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let (t1,t2) := fresh_var2 "tmc$" "tmc$" (varid::varenv::nil) in
      NNRCUnop AFlatten
              (NNRCFor t1 nrc2
                      (NNRCFor t2 (nraenv_to_nnrc_ext op1 t1 varenv)
                              ((NNRCBinop AConcat) (NNRCVar t1) (NNRCVar t2))))
    (* [[ op1 × op2 ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op2 ]]_vid,venv } | t1 ∈ [[ op1 ]]_vid,venv } *)
    | NRAEnvProduct op1 op2 =>
      let nrc1 := (nraenv_to_nnrc_ext op1 varid varenv) in
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let (t1,t2) := fresh_var2 "tprod$" "tprod$" (varid::varenv::nil) in
      NNRCUnop AFlatten
              (NNRCFor t1 nrc1
                      (NNRCFor t2 nrc2
                              ((NNRCBinop AConcat) (NNRCVar t1) (NNRCVar t2))))
    (* [[ σ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ if [[ op1 ]]_t1,venv then { t1 } else {} | t1 ∈ [[ op2 ]]_vid,venv } *)
    | NRAEnvSelect op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tsel$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 t varenv) in
      NNRCUnop AFlatten
              (NNRCFor t nrc2
                      (NNRCIf nrc1 (NNRCUnop AColl (NNRCVar t)) (NNRCConst (dcoll nil))))
    (* [[ op1 ∥ op2 ]]_vid,venv == let t := [[ op1 ]]_vid,venv in
                                       if (t = {})
                                       then [[ op2 ]]_vid,venv
                                       else t *)
    | NRAEnvDefault op1 op2 =>
      let nrc1 := (nraenv_to_nnrc_ext op1 varid varenv) in
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tdef$" (varid::varenv::nil) in
      (NNRCLet t nrc1
              (NNRCIf (NNRCBinop AEq
                               (NNRCVar t)
                               (NNRCUnop AFlatten (NNRCConst (dcoll nil))))
                     nrc2 (NNRCVar t)))
    (* [[ op1 ◯ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                     in [[ op1 ]]_t,venv *)
    | NRAEnvEither opl opr =>
      let (t1,t2) := fresh_var2 "teitherL$" "teitherR$" (varid::varenv::nil) in
      let nrcl := (nraenv_to_nnrc_ext opl t1 varenv) in
      let nrcr := (nraenv_to_nnrc_ext opr t2 varenv) in
      NNRCEither (NNRCVar varid) t1 nrcl t2 nrcr
    | NRAEnvEitherConcat op1 op2 =>
      let nrc1 := (nraenv_to_nnrc_ext op1 varid varenv) in
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tec$" (varid::varenv::nil) in 
      NNRCLet t nrc2
             (NNRCEither nrc1 varid (NNRCUnop ALeft (NNRCBinop AConcat (NNRCVar varid) (NNRCVar t)))
                        varid (NNRCUnop ARight (NNRCBinop AConcat (NNRCVar varid) (NNRCVar t))))
    | NRAEnvApp op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tapp$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 t varenv) in
      (NNRCLet t nrc2 nrc1)
    (* [[ CENV v ]]_vid,venv = v *)
    | NRAEnvGetConstant s => NNRCVar (append CONST_PREFIX s)
    (* [[ ENV ]]_vid,venv = venv *)
    | NRAEnvEnv => NNRCVar varenv
    (* [[ op1 ◯ₑ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                      in [[ op1 ]]_vid,t *)
    | NRAEnvAppEnv op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tappe$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 varid t) in
      (NNRCLet t nrc2 nrc1)
    (* [[ χᵉ⟨ op1 ⟩ ]]_vid,venv = { [[ op1 ]]_vid,t1 | t1 ∈ venv } *)
    | NRAEnvMapEnv op1 =>
      let t1 := fresh_var "tmape$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 varid t1) in
      (NNRCFor t1 (NNRCVar varenv) nrc1)
    (* [[ χᵉ⟨ op1 ⟩ ]]_vid,venv = ♯flatten({ [[ op1 ]]_vid,t1 | t1 ∈ venv }) *)
    | NRAEnvFlatMap op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tmap$" (varid::varenv::nil) in
      NNRCUnop AFlatten (NNRCFor t nrc2 (nraenv_to_nnrc_ext op1 t varenv))
    | NRAEnvJoin op1 op2 op3 =>
      let nrc2 :=
          let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
          let nrc3 := (nraenv_to_nnrc_ext op3 varid varenv) in
          let (t2,t3) := fresh_var2 "tprod$" "tprod$" (varid::varenv::nil) in
          NNRCUnop AFlatten
                       (NNRCFor t2 nrc2
                                    (NNRCFor t3 nrc3
                                                 ((NNRCBinop AConcat) (NNRCVar t2) (NNRCVar t3))))
      in
      let t := fresh_var "tsel$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 t varenv) in
      NNRCUnop AFlatten
              (NNRCFor t nrc2
                      (NNRCIf nrc1 (NNRCUnop AColl (NNRCVar t)) (NNRCConst (dcoll nil))))
    | NRAEnvProject sl op1 =>
      let t := fresh_var "tmap$" (varid::varenv::nil) in
      NNRCFor t (nraenv_to_nnrc_ext op1 varid varenv) (NNRCUnop (ARecProject sl) (NNRCVar t))
    | NRAEnvGroupBy g sl op1 =>
      NNRCGroupBy g sl (nraenv_to_nnrc_ext op1 varid varenv)
    | NRAEnvUnnest a b op1 =>
      let nrc1 := (nraenv_to_nnrc_ext op1 varid varenv) in (* op1 *)
      let (t1,t2) := fresh_var2 "tmc$" "tmc$" (varid::varenv::nil) in (* new vars for op3 *)
      let nrc2 := (* op2 = (ANMap ((ANUnop (ARec b)) ANID) ((ANUnop (ADot a)) ANID)) *)
          let t := fresh_var "tmap$" (varid::varenv::nil) in
          NNRCFor t (NNRCUnop (ADot a) (NNRCVar t1)) (NNRCUnop (ARec b) (NNRCVar t))
      in
      let nrc3 := (* op3 = (ANMapConcat op2 op1) *)
          NNRCUnop AFlatten
                   (NNRCFor t1 nrc1
                            (NNRCFor t2 nrc2
                                     ((NNRCBinop AConcat) (NNRCVar t1) (NNRCVar t2))))
      in
      let nrc4 := (* op4 = (ANMap ((ANUnop (ARecRemove a)) ANID) op3) *)
          let t := fresh_var "tmap$" (varid::varenv::nil) in
          NNRCFor t nrc3 (NNRCUnop (ARecRemove a) (NNRCVar t))
      in
      nrc4
    end.

  Open Scope nraenv_scope.

  (* This is clearly not true *)
  Section negResult.
    Require Import cNRAEnvtocNNRC.
    Example nraenv_to_nnrc_codepaths_different vid venv:
      exists op,
        ~ (nnrc_ext_to_nnrc (nraenv_to_nnrc_ext op vid venv)
           = cnraenv_to_nnrc (cnraenv_of_nraenv op) vid venv).
    Proof.
      exists (NRAEnvGroupBy "a"%string nil%string NRAEnvID).
      simpl; inversion 1.
    Qed.
  End negResult.

  Lemma nnrc_core_eval_binop_eq h env b op1 op2 op1' op2' :
    nnrc_core_eval h env op1 = nnrc_core_eval h env op1' ->
    nnrc_core_eval h env op2 = nnrc_core_eval h env op2' ->
    nnrc_core_eval h env (NNRCBinop b op1 op2) =
    nnrc_core_eval h env (NNRCBinop b op1' op2').
  Proof.
    intros eqq1 eqq2.
    simpl.
    rewrite eqq1, eqq2; trivial.
  Qed.

  Lemma nnrc_core_eval_unop_eq h env u op1 op1' :
    nnrc_core_eval h env op1 = nnrc_core_eval h env op1' ->
    nnrc_core_eval h env (NNRCUnop u op1) =
    nnrc_core_eval h env (NNRCUnop u op1').
  Proof.
    intros eqq.
    simpl.
    rewrite eqq; trivial.
  Qed.

  Lemma nnrc_core_eval_for_eq h env x op1 op2 op1' op2' :
      nnrc_core_eval h env op1 = nnrc_core_eval h env op1' ->
      (forall l,
          nnrc_core_eval h env op1 = Some (dcoll l) ->
          forall d,
            In d l ->
            nnrc_core_eval h  ((x,d)::env) op2 = nnrc_core_eval h  ((x,d)::env) op2') ->
      nnrc_core_eval h env (NNRCFor x op1 op2) =
      nnrc_core_eval h env (NNRCFor x op1' op2').
  Proof.
    intros eqq1 eqq2.
    simpl.
    rewrite <- eqq1; trivial.
    match_destr.
    match_destr.
    f_equal.
    apply rmap_ext; intros.
    eauto.
  Qed.

  Lemma nnrc_core_eval_if_eq h env bop bop' op1 op2 op1' op2' :
    nnrc_core_eval h env bop = nnrc_core_eval h env bop' ->
    nnrc_core_eval h env op1 = nnrc_core_eval h env op1' ->
    nnrc_core_eval h env op2 = nnrc_core_eval h env op2' ->
    nnrc_core_eval h env (NNRCIf bop op1 op2) =
    nnrc_core_eval h env (NNRCIf bop' op1' op2').
  Proof.
    intros eqq1 eqq2 eqq3.
    simpl.
    rewrite eqq1.
    apply olift_ext; intros.
    match_destr.
    match_destr.
  Qed.
  
  Lemma nnrc_core_eval_let_eq h env x op1 op2 op1' op2' :
      nnrc_core_eval h env op1 = nnrc_core_eval h env op1' ->
      (forall d,
          nnrc_core_eval h env op1 = Some d ->
            nnrc_core_eval h  ((x,d)::env) op2 = nnrc_core_eval h  ((x,d)::env) op2') ->
      nnrc_core_eval h env (NNRCLet x op1 op2) =
      nnrc_core_eval h env (NNRCLet x op1' op2').
  Proof.
    intros eqq1 eqq2.
    simpl.
    rewrite <- eqq1; trivial.
    match_destr.
    auto.
  Qed.

  Lemma nnrc_core_eval_either_eq h env x y eop eop' op1 op2 op1' op2' :
      nnrc_core_eval h env eop = nnrc_core_eval h env eop' ->
      (forall d,
          nnrc_core_eval h env eop = Some (dleft d) ->
            nnrc_core_eval h  ((x,d)::env) op1 = nnrc_core_eval h  ((x,d)::env) op1') ->
      (forall d,
          nnrc_core_eval h env eop = Some (dright d) ->
            nnrc_core_eval h  ((y,d)::env) op2 = nnrc_core_eval h  ((y,d)::env) op2') ->
      nnrc_core_eval h env (NNRCEither eop x op1 y op2) =
      nnrc_core_eval h env (NNRCEither eop' x op1' y op2').
  Proof.
    intros eqq1 eqq2 eqq3.
    simpl.
    rewrite <- eqq1; trivial.
    match_destr.
    match_destr; auto.
  Qed.

  Theorem nraenv_to_nnrc_codepaths_equivalent h env op vid venv:
    nnrc_core_eval h env (nnrc_ext_to_nnrc (nraenv_to_nnrc_ext op vid venv))
    = nnrc_core_eval h env (cnraenv_to_nnrc (cnraenv_of_nraenv op) vid venv).
  Proof.
    Hint Resolve nnrc_core_eval_unop_eq nnrc_core_eval_binop_eq.
    Hint Resolve nnrc_core_eval_for_eq nnrc_core_eval_if_eq.
    Hint Resolve nnrc_core_eval_let_eq nnrc_core_eval_either_eq.
    revert vid venv env; induction op; intros
    ; simpl cnraenv_of_nraenv
    ; simpl cnraenv_to_nnrc
    ; simpl nnrc_ext_to_nnrc
    ; simpl nraenv_to_nnrc_ext
    ; eauto 4.
    - apply nnrc_core_eval_unop_eq; auto.
    - apply nnrc_core_eval_group_by_eq; auto.
    - apply unnest_from_nraenv_and_nraenv_core_eq; auto.
  Qed.
  
  Theorem nraenv_sem_correct (h:list (string*string)) (op:nraenv) (env:bindings) (vid venv:var) dcenv (did denv:data) :
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    vid <> venv ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants dcenv) x
        = lookup equiv_dec (filterConstants env) x) ->
    lookup equiv_dec env vid = Some did ->
    lookup equiv_dec env venv = Some denv ->
    @nnrc_ext_eval _ h env (nraenv_to_nnrc_ext op vid venv) = nraenv_eval h dcenv op denv did.
  Proof.
    intros.
    unfold nnrc_ext_eval.
    unfold nraenv_eval.
    rewrite nraenv_to_nnrc_codepaths_equivalent.
    apply nraenv_sem_correct; assumption.
  Qed.

  Lemma nraenv_to_nnrc_ext_no_free_vars (op: nraenv):
    forall (vid venv: var),
    forall v,
      In v (nnrc_free_vars (nraenv_to_nnrc_ext op vid venv)) ->
      (prefix CONST_PREFIX v = true
      (* It is also true that: *)
      (* /\ In v (mkConstants (nraenv_constants op)) *)
      (* but stating this requires defining nraenv_constants *)
      )
      \/ v = vid \/ v = venv.
  Proof.
    nraenv_cases (induction op) Case.
    - Case "NRAEnvID"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "NRAEnvConst"%string.
      contradiction.
    - Case "NRAEnvBinop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "NRAEnvUnop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "NRAEnvMap"%string.
      intros vid venv v Hv.
      simpl in Hv.
      rewrite in_app_iff in Hv.
      destruct Hv.
      + auto.
      + apply remove_inv in H.
        destruct (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv v); intuition.
    - Case "NRAEnvMapConcat"%string.
      intros vid venv v.
      Opaque fresh_var2.
      simpl.
      case_eq (fresh_var2 "tmc$" "tmc$" (vid :: venv :: nil)); intros.
      simpl in *.
      rewrite in_app_iff in H0.
      elim H0; intros; clear H0.
      + apply IHop2; assumption.
      + destruct (string_eqdec s0 s0); try congruence.
        destruct (string_eqdec s0 s); try congruence; subst; clear e.
        * generalize (fresh_var2_distinct "tmc$" "tmc$" (vid :: venv :: nil)).
          rewrite H; simpl.
          congruence.
        * apply remove_inv in H1.
          elim H1; clear H1; intros.
          rewrite In_app_iff in H0; simpl in H0.
          elim H0; clear H0; intros; [congruence | ]. 
          clear IHop2.
          specialize (IHop1 s venv v H0).
          intuition.
    - Case "NRAEnvProduct"%string.
      intros vid venv v H.
      simpl in *.
      case_eq (fresh_var2 "tprod$" "tprod$" (vid :: venv :: nil)); intros.
      rewrite H0 in H. simpl in H.
      rewrite in_app_iff in H.
      destruct (string_eqdec s0 s0); try congruence.
      destruct (string_eqdec s0 s); try congruence; subst; clear e.
      + generalize (fresh_var2_distinct "tprod$" "tprod$" (vid :: venv :: nil)).
        rewrite H0; simpl.
        congruence.
      + elim H; clear H; intros.
        apply IHop1; assumption.
        apply remove_inv in H.
        elim H; clear H; intros.
      rewrite In_app_iff in H; simpl in H.
      elim H; clear H; intros. subst; congruence.
      apply IHop2; assumption.
    - Case "NRAEnvSelect"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv.
      + apply IHop2.
        assumption.
      + specialize (IHop1 ((fresh_var "tsel$" (vid :: venv :: nil))) venv v).
        clear IHop2.
        revert H IHop1.
        generalize (nnrc_free_vars
                      (nraenv_to_nnrc_ext op1 (fresh_var "tsel$" (vid :: venv :: nil)) venv)).
        intros.
        apply remove_inv in H.
        elim H; clear H; intros.
        rewrite In_app_iff in H; simpl in H.
        intuition.
    - Case "NRAEnvDefault"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv.
      + apply IHop1.
        assumption.
      + match_destr_in H; [ | congruence].
        apply remove_inv in H.
        elim H; clear H; intros.
        rewrite In_app_iff in H; simpl in H.
        elim H; clear H; intros.
        subst; congruence.
        apply IHop2; assumption.
    - Case "NRAEnvEither"%string.
      intros vid venv v.
      simpl.
      match_case; intros ? ? eqq.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      destruct H.
      + apply remove_inv in H.
        elim H; clear H; intros.
        clear IHop2; specialize (IHop1 _ venv v H).
        intuition.
      + revert H.
        intros.
        apply remove_inv in H.
        elim H; clear H; intros.
        clear IHop1; specialize (IHop2 _ venv v H).
        intuition.
    - Case "NRAEnvEitherConcat"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      repeat rewrite in_app_iff in H.
      destruct H.
      destruct H as [?|[?|?]].
      + auto.
      + match_destr_in H; [| congruence ].
        match_destr_in H; simpl in *; intuition.
      + match_destr_in H; [| congruence ].
        match_destr_in H; simpl in *; intuition.
    - Case "NRAEnvApp"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 _ venv v H).
      intuition.
    - Case "NRAEnvGetConstant"%string.
      intros vid venv v.
      simpl.
      intros [?|?]; [|intuition].
      subst.
      left.
      simpl.
      rewrite prefix_nil.
      reflexivity.
    - Case "NRAEnvEnv"%string.
      simpl.
      intros vid venv v.
      simpl.
      intros Hv.
      intuition.
    - Case "NRAEnvAppEnv"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 vid _ v H).
      intuition.
    - Case "NRAEnvMapEnv"%string.
      intros vid venv v.
      simpl.
      intros.
      elim H; clear H; intros; [ intuition | ].
      apply remove_inv in H.
      destruct H.
      specialize (IHop vid ((fresh_var "tmape$" (vid :: venv :: nil))) v H).
      intuition.
    - Case "NRAEnvFlatMap"%string.
      intros vid venv v Hv.
      simpl in Hv.
      rewrite in_app_iff in Hv.
      destruct Hv.
      + auto.
      + apply remove_inv in H.
        destruct (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv v); intuition.
    - Case "NRAEnvJoin"%string.
      intros vid venv v Hv.
      simpl in Hv.
      rewrite in_app_iff in Hv.
      destruct Hv.
      + case_eq (fresh_var2 "tprod$" "tprod$" (vid :: venv :: nil)); intros.
        rewrite H0 in H. simpl in H.
        rewrite in_app_iff in H.
        destruct (string_eqdec s0 s0); try congruence.
        destruct H.
        * auto.
        * destruct (string_eqdec s0 s); try congruence; subst; clear e.
          apply remove_inv in H.
          elim H; clear H; intros.
          rewrite in_app_iff in H.
          elim H; clear H; intros.
          auto.
          auto.
          apply remove_inv in H.
          elim H; clear H; intros.
          rewrite in_app_iff in H.
          elim H; clear H; intros.
          auto.
          simpl in H.
          elim H; clear H; intros; auto.
      + specialize (IHop1 ((fresh_var "tsel$" (vid :: venv :: nil))) venv v).
        clear IHop2.
        revert H IHop1.
        generalize (nnrc_free_vars
                      (nraenv_to_nnrc_ext op1 (fresh_var "tsel$" (vid :: venv :: nil)) venv)).
        intros.
        apply remove_inv in H.
        elim H; clear H; intros.
        rewrite In_app_iff in H; simpl in H.
        intuition.
    - Case "NRAEnvProject"%string.
      intros vid venv v Hv.
      Opaque fresh_var.
      simpl in Hv.
      rewrite in_app_iff in Hv.
      destruct Hv.
      + auto.
      + intros;
        simpl in *; repeat rewrite in_app_iff in *;
        destruct (IHop (fresh_var "tmap$" (vid :: venv :: nil)) venv v); intuition;
        destruct (string_eqdec (fresh_var "tmap$" (vid :: venv :: nil))
                               (fresh_var "tmap$" (vid :: venv :: nil))); try congruence;
        simpl in *; contradiction.
    - Case "NRAEnvGroupBy"%string.
      intros vid venv v Hv.
      Opaque fresh_var.
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "NRAEnvUnnest"%string.
      intros vid venv v Hv.
      Opaque fresh_var2.
      simpl.
      case_eq (fresh_var2 "tmc$" "tmc$" (vid :: venv :: nil)); intros.
      simpl in *.
      rewrite H in Hv.
      simpl in Hv.
      repeat rewrite in_app_iff in *.
      destruct (string_eqdec s2 s2); try congruence.
      elim Hv; intros; clear Hv.
      + elim H0; clear H0; intros.
        apply IHop; assumption.
        destruct (string_eqdec (fresh_var "tmap$" (vid :: venv :: nil))
                               (fresh_var "tmap$" (vid :: venv :: nil))); try congruence.
        destruct (string_eqdec s1 s1); try congruence.
        simpl in H0.
        destruct (string_eqdec s2 s1); simpl in *.
        contradiction.
        destruct (string_eqdec s1 s1); try congruence.
        contradiction.
      + destruct (string_eqdec (fresh_var "tmap$" (vid :: venv :: nil))
                               (fresh_var "tmap$" (vid :: venv :: nil))); try congruence.
        simpl in H0.
        contradiction.
  Qed.

  Section Top.
    Definition nraenv_to_nnrc_ext_top (q:nraenv) (init_vid init_venv:var) : nnrc :=
      NNRCLet init_venv (NNRCConst (drec nil))
             (NNRCLet init_vid (NNRCConst dunit)
                     (nraenv_to_nnrc_ext q init_vid init_venv)).
  End Top.
  
  (** Lemma and proof of linear size translation *)

  Section size.

    Require Import Omega.

    Theorem nraenvToNNNRC_size op vid venv : 
      nnrc_size (nraenv_to_nnrc_ext op vid venv) <= 14 * nraenv_size op.
    Proof.
      Transparent fresh_var2.
      revert vid venv.
      induction op; simpl in *; intros; trivial.
      - omega.
      - omega.
      - specialize (IHop1 vid venv); specialize (IHop2 vid venv); omega.
      - specialize (IHop vid venv); omega.
      - specialize (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv);
          specialize (IHop2 vid venv); omega.
      - repeat match_destr.
        specialize (IHop1 (fresh_var "tmc$" (vid :: venv :: nil)) venv); specialize (IHop2 vid venv); omega.
      - specialize (IHop1 vid venv); specialize (IHop2 vid venv); omega.
      - specialize (IHop1 (fresh_var "tsel$" (vid :: venv :: nil)) venv); specialize (IHop2 vid venv); omega.
      - specialize (IHop1 vid venv); specialize (IHop2 vid venv); omega.
      - specialize (IHop1 (fresh_var "teitherL$" (vid :: venv :: nil)) venv); specialize (IHop2 (fresh_var "teitherR$" (fresh_var "teitherL$" (vid :: venv :: nil) :: vid :: venv :: nil)) venv); omega.
      - specialize (IHop2 vid venv); specialize (IHop1 vid venv); omega.
      - specialize (IHop1 (fresh_var "tapp$" (vid :: venv :: nil)) venv); specialize (IHop2 vid venv); omega.
      - omega.
      - omega.
      - specialize (IHop1 vid (fresh_var "tappe$" (vid :: venv :: nil))); specialize (IHop2 vid venv); omega.
      - specialize (IHop vid (fresh_var "tmape$" (vid :: venv :: nil))); omega.
      - specialize (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv);
          specialize (IHop2 vid venv); omega.
      - specialize (IHop1 (fresh_var "tsel$" (vid :: venv :: nil)) venv);
          specialize (IHop2 vid venv); specialize (IHop3 vid venv); try omega.
      - specialize (IHop vid venv); omega.
      - specialize (IHop vid venv); omega.
      - specialize (IHop vid venv); omega.
    Qed.

  End size.

End NRAEnvtoNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
