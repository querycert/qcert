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

Section NRAtoNNRC.

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

  Fixpoint nra_to_nnrc (op:alg) (var:var) : nrc :=
    match op with
      (* [[ ID ]]_var = var *)
      | AID => NRCVar var
      (* [[ Const ]]_var = Const *)
      | AConst rd => NRCConst rd
      (* [[ op1 ⊕ op2 ]]_var == [[ op1 ]]
_var ⊕ [[ op2 ]]_var *)
      | ABinop bop op1 op2 =>
        NRCBinop bop (nra_to_nnrc op1 var) (nra_to_nnrc op2 var)
      (* [[ UOP op1 ]]_var = UOP [[ op1 ]]_var *)
      | AUnop uop op1 =>
        NRCUnop uop (nra_to_nnrc op1 var)
      (* [[ χ⟨ op1 ⟩( op2 ) ]]_var = { [[ op1 ]]_t | t ∈ [[ op2 ]]_var } *)
      | AMap op1 op2 =>
        let nrc2 := (nra_to_nnrc op2 var) in
        let t := fresh_var "tmap$" (var::nil) in
        NRCFor t nrc2 (nra_to_nnrc op1 t)
      (* [[ ⋈ᵈ⟨ op1 ⟩(op2) ]]_var
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op1 ]]_t1 } | t1 ∈ [[ op2 ]]_var } *)
      | AMapConcat op1 op2 =>
        let nrc2 := (nra_to_nnrc op2 var) in
        let (t1,t2) := fresh_var2 "tmc$" "tmc$" (var::nil) in
        NRCUnop AFlatten
                (NRCFor t1 nrc2
                        (NRCFor t2 (nra_to_nnrc op1 t1)
                                ((NRCBinop AConcat) (NRCVar t1) (NRCVar t2))))
        (* [[ op1 × op2 ]]_var
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op2 ]]_var } | t1 ∈ [[ op1 ]]_var } *)
      | AProduct op1 op2 =>
        let nrc1 := (nra_to_nnrc op1 var) in
        let nrc2 := (nra_to_nnrc op2 var) in
        let (t1,t2) := fresh_var2 "tprod$" "tprod$" (var::nil) in
        NRCUnop AFlatten
                (NRCFor t1 nrc1
                        (NRCFor t2 nrc2
                                ((NRCBinop AConcat) (NRCVar t1) (NRCVar t2))))
      (* [[ σ⟨ op1 ⟩(op2) ]]_var
               == ⋃{ if [[ op1 ]]_t1 then { t1 } else {} | t1 ∈ [[ op2 ]]_var } *)
      | ASelect op1 op2 =>
        let nrc2 := (nra_to_nnrc op2 var) in
        let t := fresh_var "tsel$" (var::nil) in
        let nrc1 := (nra_to_nnrc op1 t) in
        NRCUnop AFlatten
                (NRCFor t nrc2
                        (NRCIf nrc1 (NRCUnop AColl (NRCVar t)) (NRCConst (dcoll nil))))
      (* [[ op1 ∥ op2 ]]_var == let t := [[ op1 ]]_var in
                                  if (t = {})
                                  then [[ op2 ]]_var
                                  else t *)
      | ADefault op1 op2 =>
        let nrc1 := (nra_to_nnrc op1 var) in
        let nrc2 := (nra_to_nnrc op2 var) in
        let t := fresh_var "tdef$" (var::nil) in
        (NRCLet t nrc1
                (NRCIf (NRCBinop AEq
                                 (NRCVar t)
                                 (NRCUnop AFlatten (NRCConst (dcoll nil))))
                       nrc2 (NRCVar t)))
      (* [[ op1 ◯ op2 ]]_var == let t := [[ op2 ]]_var
                                  in [[ op1 ]]_t *)
      | AEither opl opr =>
        let nrcl := (nra_to_nnrc opl var) in
        let nrcr := (nra_to_nnrc opr var) in
        NRCEither (NRCVar var) var nrcl var nrcr
      | AEitherConcat op1 op2 =>
        let nrc1 := (nra_to_nnrc op1 var) in
        let nrc2 := (nra_to_nnrc op2 var) in
        let t := fresh_var "ec$" (var::nil) in 
        NRCLet t nrc2
        (NRCEither nrc1 var (NRCUnop ALeft (NRCBinop AConcat (NRCVar var) (NRCVar t)))
                  var (NRCUnop ARight (NRCBinop AConcat (NRCVar var) (NRCVar t))))
      | AApp op1 op2 =>
        let nrc2 := (nra_to_nnrc op2 var) in
        let t := fresh_var "tapp$" (var::nil) in
        let nrc1 := (nra_to_nnrc op1 t) in
        (NRCLet t nrc2 nrc1)
    end.

  (** Auxiliary lemmas used in the proof of correctness for the translation *)

  Lemma map_sem_correct (h:list (string*string)) (op:alg) (l:list data) (env:bindings) (v:var):
    (forall (d : data) (env : bindings) (v : var),
          lookup equiv_dec env v = Some d ->
          nrc_eval h env (nra_to_nnrc op v) = h ⊢ op @ₐ d) ->
    rmap
      (fun x : data =>
         nrc_eval h ((v, x) :: env) (nra_to_nnrc op v)) l
    =
    rmap (fun_of_alg h op) l.
  Proof.
    intros.
    induction l.
    reflexivity.
    simpl in *.
    rewrite (H a ((v, a) :: env) v).
    rewrite IHl; reflexivity.
    simpl.
    match_destr; congruence.
  Qed.

  (** Theorem 5.2: proof of correctness for the translation *)

  Theorem nra_sem_correct (h:list (string*string)) (op:alg) (env:bindings) (v:var) (d:data) :
    lookup equiv_dec env v = Some d ->
    nrc_eval h env (nra_to_nnrc op v) = h ⊢ op @ₐ d.
  Proof.
    Opaque fresh_var.
    revert d env v.
    alg_cases (induction op) Case; intros.
    - Case "AID"%string.
      simpl. assumption.
    - Case "AConst"%string.
      simpl. reflexivity.
    - Case "ABinop"%string.
      simpl; rewrite (IHop1 d env v H); rewrite (IHop2 d env v H); reflexivity.
    - Case "AUnop"%string.
       simpl; rewrite (IHop d env v H); reflexivity.
    - Case "AMap"%string.
      simpl; rewrite (IHop2 d env v H); clear IHop2.
      destruct (h ⊢ op2 @ₐ d); try reflexivity.
      destruct d0; try reflexivity.
      rewrite (map_sem_correct h op1 l env); try reflexivity; intros.
      apply (IHop1 d0 env0 v0 H0).
    - Case "AMapConcat"%string.
      generalize (fresh_var2_distinct  "tmc$" "tmc$" [v]).
      simpl; intros dis.
      repeat (dest_eqdec; try congruence).
      rewrite (IHop2 d env v H).
      simpl.
      destruct (h ⊢ op2 @ₐ d); try reflexivity; clear op2 IHop2.
      destruct d0; try reflexivity.
      autorewrite with alg in *.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold rmap_concat in *; simpl.
      unfold oomap_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop1 a (((fresh_var "tmc$" [v], a)) :: env) (fresh_var "tmc$" [v])) at 1; clear IHop1.
      destruct (h ⊢ op1 @ₐ a); try reflexivity.
      destruct d0; try reflexivity.
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
      generalize (fresh_var2_distinct  "tprod$" "tprod$" [v]).
      simpl; rewrite (IHop1 d env v H).
      intros dis.
      repeat (dest_eqdec; try congruence).
      simpl.
      destruct (h ⊢ op1 @ₐ d); try reflexivity; clear op1 IHop1.
      destruct d0; try (destruct (h ⊢ op2 @ₐ d); reflexivity).
      autorewrite with alg in *.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      unfold rmap_concat in *; simpl.
      unfold oomap_concat in *.
      rewrite <- IHl; clear IHl.
      rewrite (IHop2 d ((fresh_var "tprod$" [v], a) :: env) v) at 1; clear IHop2.
      destruct (h ⊢ op2 @ₐ d); try reflexivity.
      destruct d0; try reflexivity.
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
      rewrite (IHop2 d env v H).
      destruct (h ⊢ op2 @ₐ d); try reflexivity. clear IHop2 op2.
      destruct d0; try reflexivity.
      autorewrite with alg.
      apply lift_dcoll_inversion.
      induction l; try reflexivity; simpl.
      repeat (dest_eqdec; try congruence).
      simpl.
      rewrite <- IHl; clear IHl.
      rewrite (IHop1 a) at 1.
      destruct (h ⊢ op1 @ₐ a); try (simpl;reflexivity).
      destruct d0; simpl in *; try congruence.
      destruct b.
      rewrite lift_cons_dcoll.
      reflexivity.
      rewrite match_lift_id.
      rewrite lift_empty_dcoll.
      reflexivity.
      simpl.
      match_destr; congruence.
    - Case "ADefault"%string.
      simpl. rewrite (IHop1 d env v H).
      case_eq (h ⊢ op1 @ₐ d); intros; try reflexivity.
      repeat (dest_eqdec; try congruence).
      simpl.
      destruct (data_eq_dec d0 (dcoll [])); subst; simpl.
      + rewrite (IHop2 d); trivial.
        simpl; match_destr.
        elim (fresh_var_fresh1 _ _ _ e0).
      + destruct d0; trivial. destruct l; congruence.
    - Case "AEither"%string.
      simpl. rewrite H. match_destr.
      + apply IHop1. simpl; match_destr; try congruence.
      + apply IHop2. simpl; match_destr; try congruence.
    - Case "AEitherConcat"%string.
      simpl.
      rewrite (IHop2 _ _ _ H).
      repeat (dest_eqdec; try congruence).
      match_destr.
      + rewrite (IHop1 d).
        * match_destr.
          elim (fresh_var_fresh1 _ _ _ (symmetry e0)).
        * simpl.
          match_destr.
          elim (fresh_var_fresh1 _ _ _ (symmetry e0)).
      + elim (fresh_var_fresh1 _ _ _ (symmetry e0)).
      + case (h ⊢ op2 @ₐ d); intros; try reflexivity; simpl.
        * rewrite (IHop1 d); simpl; repeat match_destr.
          elim (fresh_var_fresh1 _ _ _ e1).
        * repeat match_destr. 
    - Case "AApp"%string.
      simpl. rewrite (IHop2 d env v H).
      case (h ⊢ op2 @ₐ d); intros; try reflexivity; simpl.
      rewrite (IHop1 d0); simpl; try reflexivity.
      dest_eqdec; try congruence.
  Qed.

  (** Lemma and proof of linear size translation *)

  Section size.

  Require Import Omega.

  Theorem nraToNNRC_size op v : 
    nrc_size (nra_to_nnrc op v) <= 10 * alg_size op.
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
  Qed.

  End size.

End NRAtoNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
