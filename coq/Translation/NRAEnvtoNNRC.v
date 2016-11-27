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

  (** Translation from NRA+Env to Named Nested Relational Calculus *)
  (* Java equivalent: NraToNnrc.algenv_to_nnrc *)
  Fixpoint algenv_to_nnrc (op:algenv) (varid varenv:var) : nrc :=
    match op with
      (* [[ ID ]]_vid,venv == vid *)
      | ANID => NRCVar varid
      (* [[ Const ]]_vid,venv == Const *)
      | ANConst rd => NRCConst rd
      (* [[ op1 ⊕ op2 ]]_vid,venv == [[ op1 ]]_vid,venv ⊕ [[ op2 ]]_vid,venv *)
      | ANBinop bop op1 op2 =>
        NRCBinop bop (algenv_to_nnrc op1 varid varenv) (algenv_to_nnrc op2 varid varenv)
      (* [[ UOP op1 ]]_vid,venv = UOP [[ op1 ]]_vid,venv *)
      | ANUnop uop op1 =>
        NRCUnop uop (algenv_to_nnrc op1 varid varenv)
      (* [[ χ⟨ op1 ⟩( op2 ) ]]_vid,venv = { [[ op1 ]]_t,venv | t ∈ [[ op2 ]]_vid,venv } *)
      | ANMap op1 op2 =>
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let t := fresh_var "tmap$" (varid::varenv::nil) in
        NRCFor t nrc2 (algenv_to_nnrc op1 t varenv)
      (* [[ ⋈ᵈ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op1 ]]_t1,venv } | t1 ∈ [[ op2 ]]_vid,venv } *)
      | ANMapConcat op1 op2 =>
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let (t1,t2) := fresh_var2 "tmc$" "tmc$" (varid::varenv::nil) in
        NRCUnop AFlatten
                (NRCFor t1 nrc2
                        (NRCFor t2 (algenv_to_nnrc op1 t1 varenv)
                                ((NRCBinop AConcat) (NRCVar t1) (NRCVar t2))))
      (* [[ op1 × op2 ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op2 ]]_vid,venv } | t1 ∈ [[ op1 ]]_vid,venv } *)
      | ANProduct op1 op2 =>
        let nrc1 := (algenv_to_nnrc op1 varid varenv) in
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let (t1,t2) := fresh_var2 "tprod$" "tprod$" (varid::varenv::nil) in
        NRCUnop AFlatten
                (NRCFor t1 nrc1
                        (NRCFor t2 nrc2
                                ((NRCBinop AConcat) (NRCVar t1) (NRCVar t2))))
      (* [[ σ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ if [[ op1 ]]_t1,venv then { t1 } else {} | t1 ∈ [[ op2 ]]_vid,venv } *)
      | ANSelect op1 op2 =>
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let t := fresh_var "tsel$" (varid::varenv::nil) in
        let nrc1 := (algenv_to_nnrc op1 t varenv) in
        NRCUnop AFlatten
                (NRCFor t nrc2
                        (NRCIf nrc1 (NRCUnop AColl (NRCVar t)) (NRCConst (dcoll nil))))
      (* [[ op1 ∥ op2 ]]_vid,venv == let t := [[ op1 ]]_vid,venv in
                                       if (t = {})
                                       then [[ op2 ]]_vid,venv
                                       else t *)
      | ANDefault op1 op2 =>
        let nrc1 := (algenv_to_nnrc op1 varid varenv) in
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let t := fresh_var "tdef$" (varid::varenv::nil) in
        (NRCLet t nrc1
                (NRCIf (NRCBinop AEq
                                 (NRCVar t)
                                 (NRCUnop AFlatten (NRCConst (dcoll nil))))
                       nrc2 (NRCVar t)))
      (* [[ op1 ◯ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                     in [[ op1 ]]_t,venv *)
      | ANEither opl opr =>
        let (t1,t2) := fresh_var2 "teitherL$" "teitherR$" (varid::varenv::nil) in
        let nrcl := (algenv_to_nnrc opl t1 varenv) in
        let nrcr := (algenv_to_nnrc opr t2 varenv) in
        NRCEither (NRCVar varid) t1 nrcl t2 nrcr
      | ANEitherConcat op1 op2 =>
        let nrc1 := (algenv_to_nnrc op1 varid varenv) in
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let t := fresh_var "tec$" (varid::varenv::nil) in 
        NRCLet t nrc2
        (NRCEither nrc1 varid (NRCUnop ALeft (NRCBinop AConcat (NRCVar varid) (NRCVar t)))
                  varid (NRCUnop ARight (NRCBinop AConcat (NRCVar varid) (NRCVar t))))
      | ANApp op1 op2 =>
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let t := fresh_var "tapp$" (varid::varenv::nil) in
        let nrc1 := (algenv_to_nnrc op1 t varenv) in
        (NRCLet t nrc2 nrc1)
      (* [[ CENV v ]]_vid,venv = v *)
      | ANGetConstant s => NRCVar (append CONST_PREFIX s)
      (* [[ ENV ]]_vid,venv = venv *)
      | ANEnv => NRCVar varenv
      (* [[ op1 ◯ₑ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                      in [[ op1 ]]_vid,t *)
      | ANAppEnv op1 op2 =>
        let nrc2 := (algenv_to_nnrc op2 varid varenv) in
        let t := fresh_var "tappe$" (varid::varenv::nil) in
        let nrc1 := (algenv_to_nnrc op1 varid t) in
        (NRCLet t nrc2 nrc1)
      (* [[ χᵉ⟨ op1 ⟩ ]]_vid,venv = { [[ op1 ]]_vid,t1 | t1 ∈ venv } *)
      | ANMapEnv op1 =>
        let t1 := fresh_var "tmape$" (varid::varenv::nil) in
        let nrc1 := (algenv_to_nnrc op1 varid t1) in
        (NRCFor t1 (NRCVar varenv) nrc1)
    end.

  (** Auxiliary lemmas used in the proof of correctness for the translation *)

  Lemma map_sem_correct (h:list (string*string)) (op:algenv) dcenv (denv:data) (l:list data) (env:bindings) (vid venv:var):
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    vid <> venv ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants dcenv) x
        = lookup equiv_dec (filterConstants env) x) ->
    lookup equiv_dec env venv = Some denv ->
    (forall cenv (did denv : data) (env : bindings) (vid venv : var),
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    vid <> venv ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants cenv) x
        = lookup equiv_dec (filterConstants env) x) ->
      lookup equiv_dec env vid = Some did ->
       lookup equiv_dec env venv = Some denv ->
       nrc_eval h env (algenv_to_nnrc op vid venv) = (fun_of_algenv h cenv op denv did)) ->
    rmap
      (fun x : data =>
         nrc_eval h ((vid, x) :: env) (algenv_to_nnrc op vid venv)) l
    =
    rmap (fun_of_algenv h dcenv op denv) l.
  Proof.
    intros Hdiff1 Hdiff2 Hcenv Henv.
    intros; induction l.
    - reflexivity.
    - simpl in *.
      rewrite (H0 dcenv a denv ((vid, a) :: env) vid venv);
        simpl; trivial; try solve [match_destr; congruence].
  Qed.

  (** Theorem 5.2: proof of correctness for the translation *)

  Local Open Scope algenv_scope.

  Opaque append.
  Theorem nraenv_sem_correct (h:list (string*string)) (op:algenv) (env:bindings) (vid venv:var) dcenv (did denv:data) :
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    vid <> venv ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants dcenv) x
        = lookup equiv_dec (filterConstants env) x) ->
    lookup equiv_dec env vid = Some did ->
    lookup equiv_dec env venv = Some denv ->
    nrc_eval h env (algenv_to_nnrc op vid venv) = h ⊢ₑ op @ₑ did ⊣ dcenv;denv.
  Proof.
    Opaque fresh_var.
    Hint Resolve fresh_var_fresh1 fresh_var_fresh2 fresh_var_fresh3 fresh_var2_distinct.
    revert dcenv did denv env vid venv.
    algenv_cases (induction op) Case; intros; simpl.
    - Case "ANID"%string.
      assumption.
    - Case "ANConst"%string.
      reflexivity.
    - Case "ANBinop"%string.
      rewrite (IHop1 dcenv did denv env vid venv H H0 H1); trivial.
      rewrite (IHop2 dcenv did denv env vid venv H H0 H1); trivial.
    - Case "ANUnop"%string.
      rewrite (IHop dcenv did denv env vid venv H H0 H1); trivial.
    - Case "ANMap"%string.
      rewrite (IHop2 dcenv did denv env vid venv H H0 H1); trivial; clear IHop2.
      destruct (h ⊢ₑ op2 @ₑ did ⊣ dcenv;denv); try reflexivity; simpl.
      destruct d; try reflexivity.
      rewrite (map_sem_correct h op1 dcenv denv l); trivial.
      prove_fresh_nin.
    - Case "ANMapConcat"%string.
      rewrite (IHop2 dcenv did denv env vid venv H H0 H1); trivial.
      repeat (dest_eqdec; try congruence).
      prove_fresh_nin.
      simpl.
      destruct (h ⊢ₑ op2 @ₑ did ⊣ dcenv;denv); try reflexivity; clear op2 IHop2; simpl;
        destruct d; try reflexivity;
        autorewrite with alg in *;
        apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold rmap_concat in *; simpl.
      unfold oomap_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop1 dcenv a denv ) at 1; clear IHop1; try assumption; simpl; auto 3.
      + destruct (h ⊢ₑ op1 @ₑ a ⊣ dcenv;denv); try reflexivity; simpl.
        destruct d; try reflexivity.
        unfold omap_concat, orecconcat, rec_concat_sort.
        simpl.
        generalize (rmap
                      (fun d1 : data =>
                         match a with
                           | drec r1 =>
                             match d1 with
                               | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                               | _ => None
                             end
                           | _ => None
                         end) l0); intros.
        destruct o; try reflexivity.
        rewrite rflatten_through_match.
        reflexivity.
      +match_destr; unfold Equivalence.equiv in *.
       prove_fresh_nin.
      + match_destr; unfold Equivalence.equiv in *.
        elim (fresh_var_fresh2 _ _ _ _ e1).
    - Case "ANProduct"%string.
      rewrite (IHop1 dcenv did denv env vid venv H H0 H1).
      dest_eqdec; [elim (fresh_var_fresh1 _ _ _ e) | ].
      dest_eqdec; [ | congruence ].
      dest_eqdec; [ | congruence ].
      destruct (h ⊢ₑ op1 @ₑ did ⊣ dcenv;denv); try reflexivity; clear op1 IHop1; simpl.
      destruct d; try reflexivity.
      autorewrite with alg in *.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold rmap_concat in *; simpl.
      unfold oomap_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop2 dcenv did denv _ vid venv) at 1; clear IHop2; trivial; try congruence.
      + destruct (h ⊢ₑ op2 @ₑ did ⊣ dcenv;denv); try reflexivity; simpl;
        destruct d; try reflexivity;
        unfold omap_concat, orecconcat, rec_concat_sort;
        simpl.
        generalize (rmap
                      (fun d1 : data =>
                         match a with
                           | drec r1 =>
                             match d1 with
                               | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                               | _ => None
                             end
                           | _ => None
                         end) l0); intros.
        simpl.
        destruct o; try reflexivity.
        rewrite rflatten_through_match; simpl.
        reflexivity.
      + simpl; match_destr; unfold Equivalence.equiv in *.
        elim (fresh_var_fresh1 _ _ _ e1).
      +  simpl; match_destr; unfold Equivalence.equiv in *.
        elim (fresh_var_fresh2 _ _ _ _ e1).
      + trivial.
      + trivial.
      + trivial.
    - Case "ANSelect"%string.
      rewrite (IHop2 dcenv did denv env vid venv H H0 H1); trivial.
      destruct (h ⊢ₑ op2 @ₑ did ⊣ dcenv;denv); try reflexivity; clear IHop2 op2; simpl.
      destruct d; try reflexivity.
      autorewrite with alg.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      dest_eqdec; [ | congruence ].
      rewrite <- IHl; clear IHl.
      simpl.
      rewrite (IHop1 dcenv a denv ((_,a) :: env) _ venv) at 1; trivial.
      + destruct (h ⊢ₑ op1 @ₑ a ⊣ dcenv;denv); try reflexivity; simpl.
        destruct d; simpl in *; try congruence.
        destruct b.
        * rewrite lift_cons_dcoll.
          reflexivity.
        * rewrite match_lift_id.
          rewrite lift_empty_dcoll.
          reflexivity.
      + prove_fresh_nin.
      + simpl; match_destr.
        congruence.
      + simpl; match_destr.
        elim (fresh_var_fresh2 _ _ _ _ e0).
    - Case "ANDefault"%string.
      simpl. rewrite (IHop1 dcenv did denv env vid venv H H0 H1); trivial.
      case_eq (h ⊢ₑ op1 @ₑ did ⊣ dcenv;denv); intros; try reflexivity; simpl.
      dest_eqdec; [| congruence ].
      simpl.
      destruct (data_eq_dec d (dcoll nil)); subst; simpl.
      + rewrite (IHop2 dcenv did denv ((_, dcoll nil) :: env)); simpl; trivial.
        * match_destr.
          elim (fresh_var_fresh1 _ _ _ e0).
        * match_destr.
          elim (fresh_var_fresh2 _ _ _ _ e0).
      + destruct d; trivial.
        destruct l; congruence.
    - Case "ANEither"%string.
      rewrite H3. match_destr.
      + apply IHop1; trivial; simpl.
        * prove_fresh_nin.
        * match_destr; congruence.
        * match_destr.
          elim (fresh_var_fresh2 _ _ _ _ e).
      + apply IHop2; trivial; simpl.
        * prove_fresh_nin. 
        * match_destr; congruence.
        * match_destr.
          elim (fresh_var_fresh3 _ _ _ _ _ e).
    - Case "ANEitherConcat"%string.
      rewrite H3.
      rewrite <- (IHop2 _ _ _ _ _ _ H H0 H1 H2 H3 H4).
      match_destr; [| repeat (match_destr; trivial)].
      rewrite <- (IHop1 dcenv did denv ((fresh_var "tec$" (vid :: venv :: nil), d) :: env) vid venv); simpl; trivial.
      + unfold var in *.
        destruct (nrc_eval h (_ :: env)); trivial.
        dest_eqdec; [| congruence].
        dest_eqdec; [elim (fresh_var_fresh1 _ _ _ (symmetry e0)) | ].
        dest_eqdec; [| congruence].
        simpl.
        match_destr; simpl; match_destr; match_destr.
      + match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
      + match_destr.
        elim (fresh_var_fresh2 _ _ _ _ e).
    - Case "ANApp"%string.
      rewrite (IHop2 dcenv did denv env vid venv H H0 H1 H2 H3 H4).
      case (h ⊢ₑ op2 @ₑ did ⊣ dcenv;denv); intros; try reflexivity; simpl.
      rewrite (IHop1 dcenv d denv); trivial.
      + prove_fresh_nin.
      + simpl; match_destr.
        congruence.
      + simpl; match_destr.
        elim (fresh_var_fresh2 _ _ _ _ e).
    - Case "ANGetConstant"%string.
      generalize (filterConstants_lookup_pre env s); simpl; intros eqq1.
      rewrite <- eqq1.
      rewrite <- H2.
      rewrite mkConstants_assoc_lookupr.
      reflexivity.
    - Case "ANEnv"%string.
      assumption.
    - Case "ANAppEnv"%string.
      rewrite (IHop2 dcenv did denv env vid venv H H0 H1); trivial.
      case (h ⊢ₑ op2 @ₑ did ⊣ dcenv;denv); intros; trivial.
      rewrite (IHop1 dcenv did d); simpl; try reflexivity; trivial; simpl.
      + match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
      + match_destr.
        congruence.
    - Case "ANMapEnv"%string.
      intros.
      rewrite H4.
      destruct denv; try reflexivity; simpl.
      f_equal.
      apply rmap_ext; intros.
      specialize (IHop dcenv did x ((fresh_var "tmape$" (vid :: venv :: nil), x) :: env) vid (fresh_var "tmape$" (vid :: venv :: nil))).
      rewrite <- IHop; trivial; simpl.
      + match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
      + match_destr.
        congruence.
  Qed.

  Transparent append.

  Lemma algenv_to_nnrc_no_free_vars (op: algenv):
    forall (vid venv: var),
    forall v,
      In v (nrc_free_vars (algenv_to_nnrc op vid venv)) ->
      (prefix CONST_PREFIX v = true
      (* It is also true that: *)
      (* /\ In v (mkConstants (nraenv_constants op)) *)
      (* but stating this requires defining nraenv_constants *)
      )
      \/ v = vid \/ v = venv.
  Proof.
    algenv_cases (induction op) Case.
    - Case "ANID"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "ANConst"%string.
      contradiction.
    - Case "ANBinop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "ANUnop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "ANMap"%string.
      intros vid venv v Hv.
      simpl in Hv.
      rewrite in_app_iff in Hv.
      destruct Hv.
      + auto.
      + apply remove_inv in H.
        destruct (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv v); intuition.
    - Case "ANMapConcat"%string.
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
    - Case "ANProduct"%string.
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
    - Case "ANSelect"%string.
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
        generalize (nrc_free_vars
                      (algenv_to_nnrc op1 (fresh_var "tsel$" (vid :: venv :: nil)) venv)).
        intros.
        apply remove_inv in H.
        elim H; clear H; intros.
        rewrite In_app_iff in H; simpl in H.
        intuition.
    - Case "ANDefault"%string.
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
    - Case "ANEither"%string.
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
    - Case "ANEitherConcat"%string.
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
    - Case "ANApp"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 _ venv v H).
      intuition.
    - Case "ANGetConstant"%string.
      intros vid venv v.
      simpl.
      intros [?|?]; [|intuition].
      subst.
      left.
      simpl.
      rewrite prefix_nil.
      reflexivity.
    - Case "ANEnv"%string.
      intros vid venv v.
      simpl.
      intros Hv.
      intuition.
    - Case "ANAppEnv"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 vid _ v H).
      intuition.
    - Case "ANMapEnv"%string.
      intros vid venv v.
      simpl.
      intros.
      elim H; clear H; intros; [ intuition | ].
      apply remove_inv in H.
      destruct H.
      specialize (IHop vid ((fresh_var "tmape$" (vid :: venv :: nil))) v H).
      intuition.
  Qed.

  Section Top.
    Definition algenv_to_nnrc_top (q:algenv) (init_vid init_venv:var) : nrc :=
      NRCLet init_venv (NRCConst (drec nil))
             (NRCLet init_vid (NRCConst dunit)
                     (algenv_to_nnrc q init_vid init_venv)).
  End Top.
  
  (** Lemma and proof of linear size translation *)

  Section size.

  Require Import Omega.

  Theorem algenvToNNRC_size op vid venv : 
    nrc_size (algenv_to_nnrc op vid venv) <= 10 * algenv_size op.
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
  Qed.

  End size.

End NRAEnvtoNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
