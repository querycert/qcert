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

Section NRAtocNNRC.

  (* begin hide *)
  Require Import String.
  Require Import List.
  Require Import EquivDec.
  Require Import Compare_dec.
  Require Import Program.

  Require Import Utils BasicRuntime.
  Require Import NRARuntime.
  Require Import NNRCRuntime.

  (* end hide *)

  Context {fruntime:foreign_runtime}.

  (** Translation from NRA to Named Nested Relational Calculus *)

  Fixpoint nra_to_nnrc (op:nra) (var:var) : nnrc :=
    match op with
    (* [[ ID ]]_var = var *)
    | AID => NNRCVar var
    (* [[ Const ]]_var = Const *)
    | AConst rd => NNRCConst rd
    (* [[ op1 ⊕ op2 ]]_var == [[ op1 ]]
_var ⊕ [[ op2 ]]_var *)
    | ABinop bop op1 op2 =>
      NNRCBinop bop (nra_to_nnrc op1 var) (nra_to_nnrc op2 var)
    (* [[ UOP op1 ]]_var = UOP [[ op1 ]]_var *)
    | AUnop uop op1 =>
      NNRCUnop uop (nra_to_nnrc op1 var)
    (* [[ χ⟨ op1 ⟩( op2 ) ]]_var = { [[ op1 ]]_t | t ∈ [[ op2 ]]_var } *)
    | AMap op1 op2 =>
      let nnrc2 := (nra_to_nnrc op2 var) in
      let t := fresh_var "tmap$" (var::nil) in
      NNRCFor t nnrc2 (nra_to_nnrc op1 t)
    (* [[ ⋈ᵈ⟨ op1 ⟩(op2) ]]_var
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op1 ]]_t1 } | t1 ∈ [[ op2 ]]_var } *)
    | AMapConcat op1 op2 =>
      let nnrc2 := (nra_to_nnrc op2 var) in
      let (t1,t2) := fresh_var2 "tmc$" "tmc$" (var::nil) in
      NNRCUnop AFlatten
               (NNRCFor t1 nnrc2
                        (NNRCFor t2 (nra_to_nnrc op1 t1)
                                 ((NNRCBinop AConcat) (NNRCVar t1) (NNRCVar t2))))
    (* [[ op1 × op2 ]]_var
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op2 ]]_var } | t1 ∈ [[ op1 ]]_var } *)
    | AProduct op1 op2 =>
      let nnrc1 := (nra_to_nnrc op1 var) in
      let nnrc2 := (nra_to_nnrc op2 var) in
      let (t1,t2) := fresh_var2 "tprod$" "tprod$" (var::nil) in
      NNRCUnop AFlatten
               (NNRCFor t1 nnrc1
                        (NNRCFor t2 nnrc2
                                 ((NNRCBinop AConcat) (NNRCVar t1) (NNRCVar t2))))
    (* [[ σ⟨ op1 ⟩(op2) ]]_var
               == ⋃{ if [[ op1 ]]_t1 then { t1 } else {} | t1 ∈ [[ op2 ]]_var } *)
    | ASelect op1 op2 =>
      let nnrc2 := (nra_to_nnrc op2 var) in
      let t := fresh_var "tsel$" (var::nil) in
      let nnrc1 := (nra_to_nnrc op1 t) in
      NNRCUnop AFlatten
               (NNRCFor t nnrc2
                        (NNRCIf nnrc1 (NNRCUnop AColl (NNRCVar t)) (NNRCConst (dcoll nil))))
    (* [[ op1 ∥ op2 ]]_var == let t := [[ op1 ]]_var in
                                  if (t = {})
                                  then [[ op2 ]]_var
                                  else t *)
    | ADefault op1 op2 =>
      let nnrc1 := (nra_to_nnrc op1 var) in
      let nnrc2 := (nra_to_nnrc op2 var) in
      let t := fresh_var "tdef$" (var::nil) in
      (NNRCLet t nnrc1
               (NNRCIf (NNRCBinop AEq
                                  (NNRCVar t)
                                  (NNRCUnop AFlatten (NNRCConst (dcoll nil))))
                       nnrc2 (NNRCVar t)))
    (* [[ op1 ◯ op2 ]]_var == let t := [[ op2 ]]_var
                                  in [[ op1 ]]_t *)
    | AEither opl opr =>
      let nnrcl := (nra_to_nnrc opl var) in
      let nnrcr := (nra_to_nnrc opr var) in
      NNRCEither (NNRCVar var) var nnrcl var nnrcr
    | AEitherConcat op1 op2 =>
      let nnrc1 := (nra_to_nnrc op1 var) in
      let nnrc2 := (nra_to_nnrc op2 var) in
      let t := fresh_var "ec$" (var::nil) in 
      NNRCLet t nnrc2
              (NNRCEither nnrc1 var (NNRCUnop ALeft (NNRCBinop AConcat (NNRCVar var) (NNRCVar t)))
                          var (NNRCUnop ARight (NNRCBinop AConcat (NNRCVar var) (NNRCVar t))))
    | AApp op1 op2 =>
      let nnrc2 := (nra_to_nnrc op2 var) in
      let t := fresh_var "tapp$" (var::nil) in
      let nnrc1 := (nra_to_nnrc op1 t) in
      (NNRCLet t nnrc2 nnrc1)
    | AGetConstant s =>
      NNRCVar (append CONST_PREFIX s)
    end.

  (** Auxiliary lemmas used in the proof of correctness for the translation *)

  Lemma map_sem_correct (h:list (string*string)) (op:nra) dcenv (l:list data) (env:bindings) (vid:var):
    prefix CONST_PREFIX vid = false ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants dcenv) x
        = lookup equiv_dec (filterConstants env) x) ->
    (forall cenv (did: data) (env : bindings) (vid : var),
        prefix CONST_PREFIX vid = false ->
        (forall x,
            assoc_lookupr equiv_dec (mkConstants cenv) x
            = lookup equiv_dec (filterConstants env) x) ->
        lookup equiv_dec env vid = Some did ->
        nnrc_core_eval h env (nra_to_nnrc op vid) = (nra_eval h cenv op did)) ->
    rmap
      (fun x : data =>
         nnrc_core_eval h ((vid, x) :: env) (nra_to_nnrc op vid)) l
    =
    rmap (nra_eval h dcenv op) l.
  Proof.
    intros.
    induction l.
    reflexivity.
    simpl in *.
    rewrite (H1 dcenv a ((vid, a) :: env) vid); simpl; trivial;
      try solve [match_destr; congruence].
  Qed.

  (** Theorem 5.2: proof of correctness for the translation *)

  Opaque append.
  Theorem nra_sem_correct (h:list (string*string)) (op:nra) (env:bindings) (vid:var) dcenv (did:data) :
    prefix CONST_PREFIX vid = false ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants dcenv) x
        = lookup equiv_dec (filterConstants env) x) ->
    lookup equiv_dec env vid = Some did ->
    nnrc_core_eval h env (nra_to_nnrc op vid) = h ⊢ op @ₐ did ⊣ dcenv.
  Proof.
    Opaque fresh_var.
    Hint Resolve fresh_var_fresh1 fresh_var_fresh2 fresh_var_fresh3 fresh_var2_distinct.
    revert dcenv did env vid.
    nra_cases (induction op) Case; intros; simpl.
    - Case "AID"%string.
      assumption.
    - Case "AConst"%string.
      reflexivity.
    - Case "ABinop"%string.
      rewrite (IHop1 dcenv did env vid H H0 H1); trivial.
      rewrite (IHop2 dcenv did env vid H H0 H1); trivial.
    - Case "AUnop"%string.
       simpl; rewrite (IHop dcenv did env vid H H0 H1); trivial.
    - Case "AMap"%string.
      simpl; rewrite (IHop2 dcenv did env vid H H0 H1); clear IHop2.
      destruct (h ⊢ op2 @ₐ did ⊣ dcenv); try reflexivity.
      destruct d; try reflexivity.
      rewrite (map_sem_correct h op1 dcenv l env); try reflexivity; intros.
      auto.
      apply (IHop1 cenv did0 env0 vid0 H2 H3).
      assumption.
    - Case "AMapConcat"%string.
      generalize (fresh_var2_distinct  "tmc$" "tmc$" [vid]).
      simpl; intros dis.
      repeat (dest_eqdec; try congruence).
      rewrite (IHop2 dcenv did env vid H H0 H1).
      simpl.
      destruct (h ⊢ op2 @ₐ did ⊣ dcenv); try reflexivity; clear op2 IHop2.
      destruct d; try reflexivity.
      autorewrite with alg in *.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold rmap_concat in *; simpl.
      unfold oomap_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop1 dcenv a (((fresh_var "tmc$" [vid], a)) :: env) (fresh_var "tmc$" [vid])) at 1; clear IHop1; trivial.
      destruct (h ⊢ op1 @ₐ a ⊣ dcenv); try reflexivity.
      destruct d; try reflexivity.
      unfold omap_concat, orecconcat, rec_concat_sort.
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
      + rewrite rflatten_through_match.
        reflexivity.
      + simpl.
        dest_eqdec; try congruence.
    - Case "AProduct"%string.
      generalize (fresh_var2_distinct  "tprod$" "tprod$" [vid]).
      simpl; rewrite (IHop1 dcenv did env vid H H0 H1).
      intros dis.
      repeat (dest_eqdec; try congruence).
      simpl.
      destruct (h ⊢ op1 @ₐ did ⊣ dcenv); try reflexivity; clear op1 IHop1.
      destruct d; try (destruct (h ⊢ op2 @ₐ did ⊣ dcenv); reflexivity).
      autorewrite with alg in *.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold rmap_concat in *; simpl.
      unfold oomap_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop2 dcenv did ((fresh_var "tprod$" [vid], a) :: env) vid) at 1; clear IHop2; trivial.
      destruct (h ⊢ op2 @ₐ did ⊣ dcenv); try reflexivity.
      destruct d; try reflexivity.
      unfold omap_concat, orecconcat, rec_concat_sort.
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
      + rewrite rflatten_through_match.
        reflexivity.
      + simpl.
        match_destr.
        elim (fresh_var_fresh1 _ _ _ e1).
    - Case "ASelect"%string.
      simpl.
      rewrite (IHop2 dcenv did env vid H H0 H1).
      destruct (h ⊢ op2 @ₐ did ⊣ dcenv); try reflexivity. clear IHop2 op2.
      destruct d; try reflexivity.
      autorewrite with alg.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      repeat (dest_eqdec; try congruence).
      simpl.
      rewrite <- IHl; clear IHl.
      rewrite (IHop1 dcenv a) at 1.
      destruct (h ⊢ op1 @ₐ a ⊣ dcenv); try (simpl;reflexivity).
      destruct d; simpl in *; try congruence.
      destruct b.
      rewrite lift_cons_dcoll.
      reflexivity.
      rewrite match_lift_id.
      rewrite lift_empty_dcoll.
      reflexivity.
      simpl.
      trivial.
      trivial.
      simpl. match_destr; congruence.
    - Case "ADefault"%string.
      simpl. rewrite (IHop1 dcenv did env vid H H0 H1).
      case_eq (h ⊢ op1 @ₐ did ⊣ dcenv); intros; try reflexivity.
      repeat (dest_eqdec; try congruence).
      simpl.
      destruct (data_eq_dec d (dcoll [])); subst; simpl.
      + rewrite (IHop2 dcenv did); trivial.
        simpl; match_destr.
        elim (fresh_var_fresh1 _ _ _ e0).
      + destruct d; trivial. destruct l; congruence.
    - Case "AEither"%string.
      simpl. rewrite H1. match_destr.
      + apply IHop1. simpl; trivial; match_destr; try congruence.
        simpl.
        rewrite H; auto.
        simpl.
        match_destr; congruence.
      + apply IHop2. simpl; trivial; match_destr; try congruence.
        simpl.
        rewrite H; auto.
        simpl.
        match_destr; congruence.
    - Case "AEitherConcat"%string.
      rewrite H1.
      rewrite (IHop2 _ _ _ _ H H0 H1).
      match_destr; [| repeat (match_destr; trivial)].
      rewrite <- (IHop1 dcenv did ((fresh_var "ec$" (vid :: nil), d) :: env) vid); simpl; trivial.
      + unfold var in *.
        destruct (nnrc_core_eval h (_ :: env)); trivial.
        dest_eqdec; [| congruence].
        dest_eqdec; [elim (fresh_var_fresh1 _ _ _ (symmetry e0)) | ].
        dest_eqdec; [| congruence].
        match_destr; simpl; match_destr; match_destr.
      + match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
    - Case "AApp"%string.
      simpl. rewrite (IHop2 dcenv did env vid H).
      case (h ⊢ op2 @ₐ did ⊣ dcenv); intros; try reflexivity; simpl.
      rewrite (IHop1 dcenv d); simpl; try reflexivity.
      trivial. match_destr; trivial.
      congruence.
      auto.
      auto.
    - Case "AGetConstant"%string.
      generalize (filterConstants_lookup_pre env s); simpl; intros eqq1.
      rewrite <- eqq1.
      rewrite <- H0.
      rewrite mkConstants_assoc_lookupr.
      reflexivity.
  Qed.

  Lemma nra_to_nnrc_is_core :
    forall q:nra, forall init_vid,
        nnrcIsCore (nra_to_nnrc q init_vid).
  Proof.
    intro q; simpl.
    induction q; simpl; auto.
  Qed.

  (** Lemma and proof of linear size translation *)

  Section Size.

    Require Import Omega.

    Theorem nraToNNRC_size op v : 
      nnrc_size (nra_to_nnrc op v) <= 10 * nra_size op.
    Proof.
      revert v.
      induction op; simpl in *; intros; trivial.
      - omega.
      - omega.
      - specialize (IHop1 v); specialize (IHop2 v); omega.
      - specialize (IHop v); omega.
      - generalize (IHop1 (fresh_var "tmap$" [v]));
          generalize (IHop2 (fresh_var "tmap$" [v])).
        specialize (IHop1 v); specialize (IHop2 v); omega.
      - generalize (IHop1 (fresh_var "tmc$" [v])); generalize (IHop2 v).
        specialize (IHop1 v); specialize (IHop2 v); omega.
      - specialize (IHop1 v); specialize (IHop2 v); omega.
      - generalize (IHop1 (fresh_var "tsel$" [v])); generalize (IHop2 v).
        specialize (IHop1 v); specialize (IHop2 v); omega.
      - specialize (IHop1 v); specialize (IHop2 v); omega.
      - specialize (IHop1 v); specialize (IHop2 v); omega.
      - specialize (IHop1 v); specialize (IHop2 v); omega.
      - specialize (IHop2 v); specialize (IHop1 (fresh_var "tapp$" [v])); omega.
      - omega.
    Qed.

  End Size.

  Section Top.
    (* Canned initial variable for the current value *)
    Definition init_vid := "id"%string.
    
    Definition nra_to_nnrc_top (q:nra) : nnrc :=
      (NNRCLet init_vid (NNRCConst dunit)
               (nra_to_nnrc q init_vid)).

    Definition map_constants (constants:list var) (q:nnrc) : nnrc :=
      fold_right (fun constant qacc =>
                    NNRCLet (append CONST_PREFIX constant)
                            (NNRCVar constant)
                            qacc) q constants.
                    
    Lemma map_constants_is_core :
      forall constants, forall q:nnrc,
          nnrcIsCore q ->
          nnrcIsCore (map_constants constants q).
    Proof.
      intros.
      induction constants; simpl; auto.
    Qed.
      
    Definition nra_to_nnrc_top_alt (q:nra) : nnrc :=
      let constants := nra_free_variables q in
      let topq := nra_to_nnrc_top q in
      map_constants constants topq.

    Lemma nra_to_nnrc_top_is_core :
      forall q:nra, nnrcIsCore (nra_to_nnrc_top q).
    Proof.
      intros; simpl.
      split; [trivial| ].
      apply nra_to_nnrc_is_core.
    Qed.

    Lemma nra_to_nnrc_top_alt_is_core :
      forall q:nra, nnrcIsCore (nra_to_nnrc_top_alt q).
    Proof.
      intros; simpl.
      unfold nra_to_nnrc_top_alt.
      apply map_constants_is_core.
      apply nra_to_nnrc_top_is_core.
    Qed.

    Program Definition nra_to_nnrc_core_top (q:nra) : nnrc_core :=
      exist _ (nra_to_nnrc_top q) _.
    Next Obligation.
      apply nra_to_nnrc_top_is_core.
    Qed.

    Program Definition nra_to_nnrc_core_top_alt (q:nra) : nnrc_core :=
      exist _ (nra_to_nnrc_top_alt q) _.
    Next Obligation.
      apply nra_to_nnrc_top_alt_is_core.
    Qed.

    Theorem nra_to_nnrc_core_top_correct
            (h:list (string*string)) (q:nra) (env:bindings) :
      nnrc_core_eval_top h (nra_to_nnrc_core_top q) env = nra_eval_top h q env.
    Proof.
      intros.
      unfold nnrc_core_eval_top.
      unfold nra_eval_top.
      unfold nra_to_nnrc_core_top.
      unfold lift_nnrc_core.
      simpl.
      rewrite (nra_sem_correct h q
                               ((init_vid,dunit)::(rec_sort (mkConstants env)))
                               init_vid
                               (rec_sort env)
                               dunit); try reflexivity.
      simpl.
      intros.
      rewrite rec_sort_mkConstants_comm.
      rewrite filterConstants_mkConstants.
      rewrite (assoc_lookupr_lookup equiv_dec x (mkConstants (rec_sort env))).
      rewrite <- rec_sort_mkConstants_comm.
      generalize (@lookup_rev_rec_sort string ODT_string data x (mkConstants env)).
      intros.
      assert (lookup ODT_eqdec (rev (rec_sort (mkConstants env))) x
              = lookup equiv_dec (rev (rec_sort (mkConstants env))) x).
      reflexivity.
      rewrite H0 in *.
      rewrite H.
      reflexivity.
    Qed.

    Lemma revert_constants h (constants:list var) (env:bindings) (q:nnrc) :
      constants = nnrc_free_vars q ->
      (forall x, In x constants -> In x (domain env)) ->
      nnrc_core_eval h (rec_sort env) (map_constants constants q) =
      nnrc_core_eval h (rec_sort (mkConstants env)) q.
    Proof.
      revert env q.
      induction constants; intros; simpl.
      - apply nnrc_core_eval_equiv_free_in_env.
        intros.
        rewrite <- H in H1.
        simpl in H1.
        contradiction.
      - case_eq (lookup equiv_dec (rec_sort env) a); intros.
        admit.
        admit.
    Admitted.

    Theorem nra_to_nnrc_core_top_alt_correct
            (h:list (string*string)) (q:nra) (env:bindings) :
      nnrc_core_eval_top_alt h (nra_to_nnrc_core_top_alt q) env = nra_eval_top h q env.
    Proof.
      unfold nra_to_nnrc_core_top_alt.
      unfold nra_to_nnrc_top_alt.
      unfold nnrc_core_eval_top_alt.
      rewrite <- nra_to_nnrc_core_top_correct.
      unfold lift_nnrc_core; simpl.
      unfold nnrc_core_eval_top.
      unfold lift_nnrc_core.
      Opaque nra_to_nnrc_core_top.
      simpl.
      rewrite revert_constants.
      reflexivity.
      admit.
      admit.
    Admitted.
      
  End Top.
  
End NRAtocNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
