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
Require Import EquivDec.
Require Import Omega.
Require Import Compare_dec.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNRAEnvRuntime.
Require Import cNNRCRuntime.
Require Import NNRC.
Require Import NNRCSize.

Section cNRAEnvtocNNRC.
  Context {fruntime:foreign_runtime}.

  (** Translation from NRA+Env to Named Nested Relational Calculus *)
  (* Java equivalent: NraToNnrc.cnraenv_to_nnrc *)
  Fixpoint nraenv_core_to_nnrc_core (op:nraenv_core) (varid varenv:var) : nnrc :=
    match op with
      (* [[ CENV v ]]_vid,venv = v *)
      | cNRAEnvGetConstant s => NNRCGetConstant s
      (* [[ ID ]]_vid,venv == vid *)
      | cNRAEnvID => NNRCVar varid
      (* [[ Const ]]_vid,venv == Const *)
      | cNRAEnvConst rd => NNRCConst rd
      (* [[ op1 ⊕ op2 ]]_vid,venv == [[ op1 ]]_vid,venv ⊕ [[ op2 ]]_vid,venv *)
      | cNRAEnvBinop bop op1 op2 =>
        NNRCBinop bop (nraenv_core_to_nnrc_core op1 varid varenv) (nraenv_core_to_nnrc_core op2 varid varenv)
      (* [[ UOP op1 ]]_vid,venv = UOP [[ op1 ]]_vid,venv *)
      | cNRAEnvUnop uop op1 =>
        NNRCUnop uop (nraenv_core_to_nnrc_core op1 varid varenv)
      (* [[ χ⟨ op1 ⟩( op2 ) ]]_vid,venv = { [[ op1 ]]_t,venv | t ∈ [[ op2 ]]_vid,venv } *)
      | cNRAEnvMap op1 op2 =>
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let t := fresh_var "tmap$" (varid::varenv::nil) in
        NNRCFor t nnrc2 (nraenv_core_to_nnrc_core op1 t varenv)
      (* [[ ⋈ᵈ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op1 ]]_t1,venv } | t1 ∈ [[ op2 ]]_vid,venv } *)
      | cNRAEnvMapProduct op1 op2 =>
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let (t1,t2) := fresh_var2 "tmc$" "tmc$" (varid::varenv::nil) in
        NNRCUnop OpFlatten
                (NNRCFor t1 nnrc2
                        (NNRCFor t2 (nraenv_core_to_nnrc_core op1 t1 varenv)
                                ((NNRCBinop OpRecConcat) (NNRCVar t1) (NNRCVar t2))))
      (* [[ op1 × op2 ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op2 ]]_vid,venv } | t1 ∈ [[ op1 ]]_vid,venv } *)
      | cNRAEnvProduct op1 op2 =>
        let nnrc1 := (nraenv_core_to_nnrc_core op1 varid varenv) in
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let (t1,t2) := fresh_var2 "tprod$" "tprod$" (varid::varenv::nil) in
        NNRCUnop OpFlatten
                (NNRCFor t1 nnrc1
                        (NNRCFor t2 nnrc2
                                ((NNRCBinop OpRecConcat) (NNRCVar t1) (NNRCVar t2))))
      (* [[ σ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ if [[ op1 ]]_t1,venv then { t1 } else {} | t1 ∈ [[ op2 ]]_vid,venv } *)
      | cNRAEnvSelect op1 op2 =>
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let t := fresh_var "tsel$" (varid::varenv::nil) in
        let nnrc1 := (nraenv_core_to_nnrc_core op1 t varenv) in
        NNRCUnop OpFlatten
                (NNRCFor t nnrc2
                        (NNRCIf nnrc1 (NNRCUnop OpBag (NNRCVar t)) (NNRCConst (dcoll nil))))
      (* [[ op1 ∥ op2 ]]_vid,venv == let t := [[ op1 ]]_vid,venv in
                                       if (t = {})
                                       then [[ op2 ]]_vid,venv
                                       else t *)
      | cNRAEnvDefault op1 op2 =>
        let nnrc1 := (nraenv_core_to_nnrc_core op1 varid varenv) in
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let t := fresh_var "tdef$" (varid::varenv::nil) in
        (NNRCLet t nnrc1
                (NNRCIf (NNRCBinop OpEqual
                                 (NNRCVar t)
                                 (NNRCUnop OpFlatten (NNRCConst (dcoll nil))))
                       nnrc2 (NNRCVar t)))
      (* [[ op1 ◯ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                     in [[ op1 ]]_t,venv *)
      | cNRAEnvEither opl opr =>
        let (t1,t2) := fresh_var2 "teitherL$" "teitherR$" (varid::varenv::nil) in
        let nnrcl := (nraenv_core_to_nnrc_core opl t1 varenv) in
        let nnrcr := (nraenv_core_to_nnrc_core opr t2 varenv) in
        NNRCEither (NNRCVar varid) t1 nnrcl t2 nnrcr
      | cNRAEnvEitherConcat op1 op2 =>
        let nnrc1 := (nraenv_core_to_nnrc_core op1 varid varenv) in
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let t := fresh_var "tec$" (varid::varenv::nil) in 
        NNRCLet t nnrc2
                (NNRCEither nnrc1
                            varid (NNRCUnop OpLeft
                                            (NNRCBinop OpRecConcat (NNRCVar varid) (NNRCVar t)))
                            varid (NNRCUnop OpRight
                                            (NNRCBinop OpRecConcat (NNRCVar varid) (NNRCVar t))))
      | cNRAEnvApp op1 op2 =>
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let t := fresh_var "tapp$" (varid::varenv::nil) in
        let nnrc1 := (nraenv_core_to_nnrc_core op1 t varenv) in
        (NNRCLet t nnrc2 nnrc1)
      (* [[ ENV ]]_vid,venv = venv *)
      | cNRAEnvEnv => NNRCVar varenv
      (* [[ op1 ◯ₑ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                      in [[ op1 ]]_vid,t *)
      | cNRAEnvAppEnv op1 op2 =>
        let nnrc2 := (nraenv_core_to_nnrc_core op2 varid varenv) in
        let t := fresh_var "tappe$" (varid::varenv::nil) in
        let nnrc1 := (nraenv_core_to_nnrc_core op1 varid t) in
        (NNRCLet t nnrc2 nnrc1)
      (* [[ χᵉ⟨ op1 ⟩ ]]_vid,venv = { [[ op1 ]]_vid,t1 | t1 ∈ venv } *)
      | cNRAEnvMapEnv op1 =>
        let t1 := fresh_var "tmape$" (varid::varenv::nil) in
        let nnrc1 := (nraenv_core_to_nnrc_core op1 varid t1) in
        (NNRCFor t1 (NNRCVar varenv) nnrc1)
    end.

  (** Auxiliary lemmas used in the proof of correctness for the translation *)

  Lemma map_sem_correct (h:list (string*string)) (op:nraenv_core) cenv (denv:data) (l:list data) (env:bindings) (vid venv:var):
    vid <> venv ->
    lookup equiv_dec env venv = Some denv ->
    (forall (did denv : data) (env : bindings) (vid venv : var),
        vid <> venv ->
        lookup equiv_dec env vid = Some did ->
        lookup equiv_dec env venv = Some denv ->
        nnrc_core_eval h cenv env (nraenv_core_to_nnrc_core op vid venv) = (nraenv_core_eval h cenv op denv did)) ->
    lift_map
      (fun x : data =>
         nnrc_core_eval h cenv ((vid, x) :: env) (nraenv_core_to_nnrc_core op vid venv)) l
    =
    lift_map (nraenv_core_eval h cenv op denv) l.
  Proof.
    intros Hdiff1 Henv.
    intros; induction l.
    - reflexivity.
    - simpl in *.
      rewrite (H a denv ((vid, a) :: env) vid venv);
        simpl; trivial; try solve [match_destr; congruence].
  Qed.

  (** Theorem 5.2: proof of correctness for the translation *)

  Local Open Scope nraenv_core_scope.

  Opaque append.
  Theorem nraenv_core_sem_correct (h:list (string*string)) (cenv:bindings) (op:nraenv_core) (env:bindings) (vid venv:var) (did denv:data) :
    vid <> venv ->
    lookup equiv_dec env vid = Some did ->
    lookup equiv_dec env venv = Some denv ->
    nnrc_core_eval h cenv env (nraenv_core_to_nnrc_core op vid venv) = h ⊢ₑ op @ₑ did ⊣ cenv;denv.
  Proof.
    Opaque fresh_var.
    Hint Resolve fresh_var_fresh1 fresh_var_fresh2 fresh_var_fresh3 fresh_var2_distinct.
    revert did denv env vid venv.
    nraenv_core_cases (induction op) Case; intros; simpl.
    - Case "cNRAEnvGetConstant"%string.
      reflexivity.
    - Case "cNRAEnvID"%string.
      assumption.
    - Case "cNRAEnvConst"%string.
      reflexivity.
    - Case "cNRAEnvBinop"%string.
      rewrite (IHop1 did denv env vid venv H); trivial.
      rewrite (IHop2 did denv env vid venv H); trivial.
    - Case "cNRAEnvUnop"%string.
      rewrite (IHop did denv env vid venv H); trivial.
    - Case "cNRAEnvMap"%string.
      rewrite (IHop2 did denv env vid venv H); trivial; clear IHop2.
      destruct (h ⊢ₑ op2 @ₑ did ⊣ cenv;denv); try reflexivity; simpl.
      destruct d; try reflexivity.
      rewrite (map_sem_correct h op1 cenv denv l); trivial.
      prove_fresh_nin.
    - Case "cNRAEnvMapProduct"%string.
      rewrite (IHop2 did denv env vid venv H); trivial.
      repeat (dest_eqdec; try congruence).
      prove_fresh_nin.
      simpl.
      destruct (h ⊢ₑ op2 @ₑ did ⊣ cenv;denv); try reflexivity; clear op2 IHop2; simpl;
        destruct d; try reflexivity;
        autorewrite with alg in *;
        apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold omap_product in *; simpl.
      unfold oncoll_map_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop1 a denv) at 1; clear IHop1; try assumption; simpl; auto 3.
      + destruct (h ⊢ₑ op1 @ₑ a ⊣ cenv;denv); try reflexivity; simpl.
        destruct d; try reflexivity.
        unfold omap_concat, orecconcat, rec_concat_sort.
        simpl.
        generalize (lift_map
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
        rewrite oflatten_through_match.
        reflexivity.
      +match_destr; unfold Equivalence.equiv in *.
       prove_fresh_nin.
      + match_destr; unfold Equivalence.equiv in *.
        elim (fresh_var_fresh2 _ _ _ _ e1).
    - Case "cNRAEnvProduct"%string.
      rewrite (IHop1 did denv env vid venv H).
      dest_eqdec; [elim (fresh_var_fresh1 _ _ _ e) | ].
      dest_eqdec; [ | congruence ].
      dest_eqdec; [ | congruence ].
      destruct (h ⊢ₑ op1 @ₑ did ⊣ cenv;denv); try reflexivity; clear op1 IHop1; simpl.
      destruct d; try reflexivity.
      autorewrite with alg in *.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold omap_product in *; simpl.
      unfold oncoll_map_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop2 did denv _ vid venv) at 1; clear IHop2; trivial; try congruence.
      + destruct (h ⊢ₑ op2 @ₑ did ⊣ cenv;denv); try reflexivity; simpl;
        destruct d; try reflexivity;
        unfold omap_concat, orecconcat, rec_concat_sort;
        simpl.
        generalize (lift_map
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
        rewrite oflatten_through_match; simpl.
        reflexivity.
      + simpl; match_destr; unfold Equivalence.equiv in *.
        elim (fresh_var_fresh1 _ _ _ e1).
      +  simpl; match_destr; unfold Equivalence.equiv in *.
        elim (fresh_var_fresh2 _ _ _ _ e1).
      + trivial.
      + trivial.
    - Case "cNRAEnvSelect"%string.
      rewrite (IHop2 did denv env vid venv H); trivial.
      destruct (h ⊢ₑ op2 @ₑ did ⊣ cenv;denv); try reflexivity; clear IHop2 op2; simpl.
      destruct d; try reflexivity.
      autorewrite with alg.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      dest_eqdec; [ | congruence ].
      rewrite <- IHl; clear IHl.
      simpl.
      rewrite (IHop1 a denv ((_,a) :: env) _ venv) at 1; trivial.
      + destruct (h ⊢ₑ op1 @ₑ a ⊣ cenv;denv); try reflexivity; simpl.
        destruct d; simpl in *; try congruence.
        destruct b.
        * rewrite oflatten_lift_cons_dcoll.
          reflexivity.
        * rewrite match_lift_id.
          rewrite oflatten_lift_empty_dcoll.
          reflexivity.
      + prove_fresh_nin.
      + simpl; match_destr.
        congruence.
      + simpl; match_destr.
        elim (fresh_var_fresh2 _ _ _ _ e0).
    - Case "cNRAEnvDefault"%string.
      simpl. rewrite (IHop1 did denv env vid venv H); trivial.
      case_eq (h ⊢ₑ op1 @ₑ did ⊣ cenv;denv); intros; try reflexivity; simpl.
      dest_eqdec; [| congruence ].
      simpl.
      destruct (data_eq_dec d (dcoll nil)); subst; simpl.
      + rewrite (IHop2 did denv ((_, dcoll nil) :: env)); simpl; trivial.
        * match_destr.
          elim (fresh_var_fresh1 _ _ _ e0).
        * match_destr.
          elim (fresh_var_fresh2 _ _ _ _ e0).
      + destruct d; trivial.
        destruct l; congruence.
    - Case "cNRAEnvEither"%string.
      rewrite H0. match_destr.
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
    - Case "cNRAEnvEitherConcat"%string.
      rewrite H0.
      rewrite <- (IHop2 _ _ _ _ _ H H0 H1).
      match_destr; [| repeat (match_destr; trivial)].
      rewrite <- (IHop1 did denv ((fresh_var "tec$" (vid :: venv :: nil), d) :: env) vid venv); simpl; trivial.
      + unfold var in *.
        destruct (nnrc_core_eval h cenv (_ :: env)); trivial.
        dest_eqdec; [| congruence].
        dest_eqdec; [elim (fresh_var_fresh1 _ _ _ (symmetry e0)) | ].
        dest_eqdec; [| congruence].
        simpl.
        match_destr; simpl; match_destr; match_destr.
      + match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
      + match_destr.
        elim (fresh_var_fresh2 _ _ _ _ e).
    - Case "cNRAEnvApp"%string.
      rewrite (IHop2 did denv env vid venv H H0 H1).
      case (h ⊢ₑ op2 @ₑ did ⊣ cenv;denv); intros; try reflexivity; simpl.
      rewrite (IHop1 d denv); trivial.
      + prove_fresh_nin.
      + simpl; match_destr.
        congruence.
      + simpl; match_destr.
        elim (fresh_var_fresh2 _ _ _ _ e).
    - Case "cNRAEnvEnv"%string.
      assumption.
    - Case "cNRAEnvAppEnv"%string.
      rewrite (IHop2 did denv env vid venv H); trivial.
      case (h ⊢ₑ op2 @ₑ did ⊣ cenv;denv); intros; trivial.
      rewrite (IHop1 did d); simpl; try reflexivity; trivial; simpl.
      + match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
      + match_destr.
        congruence.
    - Case "cNRAEnvMapEnv"%string.
      intros.
      rewrite H1.
      destruct denv; try reflexivity; simpl.
      f_equal.
      apply lift_map_ext; intros.
      specialize (IHop did x ((fresh_var "tmape$" (vid :: venv :: nil), x) :: env) vid (fresh_var "tmape$" (vid :: venv :: nil))).
      rewrite <- IHop; trivial; simpl.
      + match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
      + match_destr.
        congruence.
  Qed.

  Transparent append.

  Lemma nraenv_core_to_nnrc_core_no_free_vars (op: nraenv_core):
    forall (vid venv: var),
    forall v,
      In v (nnrc_free_vars (nraenv_core_to_nnrc_core op vid venv)) ->
      v = vid \/ v = venv.
  Proof.
    nraenv_core_cases (induction op) Case.
    - Case "cNRAEnvGetConstant"%string.
      intros vid venv v.
      simpl.
      intros; contradiction.
    - Case "cNRAEnvID"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "cNRAEnvConst"%string.
      contradiction.
    - Case "cNRAEnvBinop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "cNRAEnvUnop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "cNRAEnvMap"%string.
      intros vid venv v Hv.
      simpl in Hv.
      rewrite in_app_iff in Hv.
      destruct Hv.
      + auto.
      + apply remove_inv in H.
        destruct (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv v); intuition.
    - Case "cNRAEnvMapProduct"%string.
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
    - Case "cNRAEnvProduct"%string.
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
    - Case "cNRAEnvSelect"%string.
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
                      (nraenv_core_to_nnrc_core op1 (fresh_var "tsel$" (vid :: venv :: nil)) venv)).
        intros.
        apply remove_inv in H.
        elim H; clear H; intros.
        rewrite In_app_iff in H; simpl in H.
        intuition.
    - Case "cNRAEnvDefault"%string.
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
    - Case "cNRAEnvEither"%string.
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
    - Case "cNRAEnvEitherConcat"%string.
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
    - Case "cNRAEnvApp"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 _ venv v H).
      intuition.
    - Case "cNRAEnvEnv"%string.
      intros vid venv v.
      simpl.
      intros Hv.
      intuition.
    - Case "cNRAEnvAppEnv"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 vid _ v H).
      intuition.
    - Case "cNRAEnvMapEnv"%string.
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
    Context (h:brand_relation_t).

    (* Canned initial variable for the current value *)
    Definition init_vid := "id"%string.
    Definition init_venv := "env"%string.
    
    (** One more top-level part of the translation *)
    Definition nraenv_core_to_nnrc_base_top (q:nraenv_core) : nnrc :=
      NNRCLet init_venv (NNRCConst (drec nil))
              (NNRCLet init_vid (NNRCConst dunit)
                       (nraenv_core_to_nnrc_core q init_vid init_venv)).

    (** Show that translation does not 'bleed out' beyond core NNRC *)
    Lemma nraenv_core_to_nnrc_core_is_core (vid venv:var) (q:nraenv_core) :
      nnrcIsCore (nraenv_core_to_nnrc_core q vid venv).
    Proof.
      revert vid venv.
      nraenv_core_cases (induction q) Case; intros; simpl; auto.
      - Case "cNRAEnvMapProduct"%string.
        destruct (fresh_var2 "tmc$" "tmc$" (vid :: venv :: nil));simpl.
        auto.
      - Case "cNRAEnvProduct"%string.
        destruct (fresh_var2 "tprod$" "tprod$" (vid :: venv :: nil)); simpl.
        auto.
      - Case "cNRAEnvEither"%string.
        destruct (fresh_var2 "teitherL$" "teitherR$" (vid :: venv :: nil)); simpl.
        auto.
    Qed.

    Hint Resolve nraenv_core_to_nnrc_core_is_core.

    Lemma nraenv_core_to_nnrc_base_top_is_core (q:nraenv_core) :
      nnrcIsCore (nraenv_core_to_nnrc_base_top q).
    Proof.
      simpl.
      auto.
    Qed.

    Hint Resolve nraenv_core_to_nnrc_base_top_is_core.

    Program Definition nraenv_core_to_nnrc_core_top (q:nraenv_core) : nnrc_core :=
      exist _ (nraenv_core_to_nnrc_base_top q) _.
    
    Theorem nraenv_core_to_nnrc_core_top_correct (q:nraenv_core) (env:bindings) :
      nnrc_core_eval_top h (nraenv_core_to_nnrc_core_top q) env = nraenv_core_eval_top h q env.
    Proof.
      intros.
      unfold nnrc_core_eval_top.
      unfold nraenv_core_eval_top.
      unfold nraenv_core_to_nnrc_core_top.
      unfold lift_nnrc_core.
      simpl.
      rewrite (nraenv_core_sem_correct h (rec_sort env) q
                                       ((init_vid,dunit)::(init_venv,drec nil)::nil)
                                       init_vid
                                       init_venv
                                       dunit
                                       (drec nil)); try reflexivity.
      unfold not; intros.
      unfold init_vid, init_venv in *.
      congruence.
    Qed.

  End Top.

  (** Lemma and proof of linear size translation *)

  Section size.

    Theorem nraenv_coreToNNRC_size op vid venv : 
      nnrc_size (nraenv_core_to_nnrc_core op vid venv) <= 10 * nraenv_core_size op.
    Proof.
      Transparent fresh_var2.
      revert vid venv.
      induction op; simpl in *; intros; trivial.
      - omega.
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
      - specialize (IHop1 vid (fresh_var "tappe$" (vid :: venv :: nil))); specialize (IHop2 vid venv); omega.
      - specialize (IHop vid (fresh_var "tmape$" (vid :: venv :: nil))); omega.
    Qed.

  End size.

End cNRAEnvtocNNRC.

