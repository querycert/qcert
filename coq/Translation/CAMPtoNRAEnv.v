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

Section CAMPtoNRAEnv.
  Require Import String.
  Require Import List.

  Require Import Utils BasicRuntime.
  Require Import NRARuntime NRAEnvRuntime.
  Require Import CAMPRuntime.
  Require Import CAMPtoNRA.

  Context {fruntime:foreign_runtime}.

  (** Functions used to map input/ouput values between CAMP and NRA *)
  (* Input encoding *)

  (* Match failure returns the empty sequence, success returns a singleton sequence *)
  (* Java equivalent: CampToNra.envpat_fail *)
  Definition envpat_fail := NRAEnvConst (dcoll nil).
  (* Java equivalent: CampToNra.envpat_match *)
  Definition envpat_match op := NRAEnvUnop AColl op.

  (** Translation from CAMP to EnvNRA *)

  (* Java equivalent: CampToNra.cnraenv_of_pat *)
  Fixpoint nraenv_of_pat (p:pat) : nraenv :=
    match p with
      | pconst d' => envpat_match (NRAEnvConst d')
      | punop uop p₁ => NRAEnvMap (NRAEnvUnop uop NRAEnvID) (nraenv_of_pat p₁)
      | pbinop bop p₁ p₂ =>
        NRAEnvMap (NRAEnvBinop bop (NRAEnvUnop (ADot "a1") NRAEnvID) (NRAEnvUnop (ADot "a2") NRAEnvID))
              (NRAEnvProduct (NRAEnvMap (NRAEnvUnop (ARec "a1") NRAEnvID) (nraenv_of_pat p₁))
                         (NRAEnvMap (NRAEnvUnop (ARec "a2") NRAEnvID) (nraenv_of_pat p₂)))
      | pmap p₁ =>
        envpat_match
          (NRAEnvUnop AFlatten
                  (NRAEnvMap
                     (nraenv_of_pat p₁) NRAEnvID))
      | passert p₁ =>
        NRAEnvMap (NRAEnvConst (drec nil)) (NRAEnvSelect NRAEnvID (nraenv_of_pat p₁))
      | porElse p₁ p₂ => NRAEnvDefault (nraenv_of_pat p₁) (nraenv_of_pat p₂)
      | pit => envpat_match NRAEnvID
      | pletIt p₁ p₂ =>
        NRAEnvUnop AFlatten
               (NRAEnvMap (nraenv_of_pat p₂)
                      (nraenv_of_pat p₁))
      | pgetconstant s => envpat_match (NRAEnvGetConstant s)
      | penv => envpat_match NRAEnvEnv
      | pletEnv p₁ p₂ =>
        NRAEnvUnop AFlatten
               (NRAEnvAppEnv
                  (NRAEnvMapEnv (nraenv_of_pat p₂))
                  (NRAEnvUnop AFlatten
                          (NRAEnvMap (NRAEnvBinop AMergeConcat NRAEnvEnv NRAEnvID) (nraenv_of_pat p₁))))
      | pleft =>
        NRAEnvEither (envpat_match NRAEnvID) (envpat_fail)
      | pright =>
        NRAEnvEither (envpat_fail) (envpat_match NRAEnvID)
    end.

  (** top level version sets up the appropriate input 
      (with an empty context) 
  *)

  Definition nraenv_of_pat_top p :=
    NRAEnvUnop AFlatten
           (NRAEnvMap (nraenv_of_pat p) (NRAEnvUnop AColl NRAEnvID)).
  
  (** Theorem 4.2: lemma of translation correctness for patterns *)

  Require Import CAMPtocNRAEnv.

  Lemma nraenv_of_pat_cnraenv_of_pat_ident q :
    cnraenv_of_nraenv (nraenv_of_pat q) = cnraenv_of_pat q.
  Proof.
    induction q; intros; try reflexivity; simpl;
    try (rewrite IHq; try reflexivity);
    try (rewrite IHq1; rewrite IHq2; try reflexivity).
  Qed.
  
  Lemma nraenv_of_pat_correct h c q env d:
    lift_failure (interp h c q env d) = nraenv_eval h c (nraenv_of_pat q) (drec env) d.
  Proof.
    rewrite cnraenv_of_pat_correct.
    unfold nraenv_eval.
    rewrite nraenv_of_pat_cnraenv_of_pat_ident.
    reflexivity.
  Qed.
  
  Lemma nraenv_of_pat_equiv_to_nra h c p bind d:
    nra_eval h (nra_of_pat p) (pat_context_data (drec (rec_sort c)) (drec bind) d) =
    nraenv_eval h c (nraenv_of_pat p) (drec bind) d.
  Proof.
    rewrite <- nraenv_of_pat_correct.
    rewrite pat_trans_correct; reflexivity.
  Qed.

  Lemma nraenv_of_pat_top_id h c p d :
    Forall (fun x => data_normalized h (snd x)) c ->
    nra_eval h (nra_of_pat_top c p) d =
    nraenv_eval h c (nraenv_of_pat_top p) (drec nil) d.
  Proof.
    intros.
    unfold nraenv_of_pat_top.
    generalize nraenv_of_pat_equiv_to_nra; intros Hequiv.
    unfold nraenv_eval in *; simpl in *.
    rewrite <- Hequiv.
    unfold pat_context_data.
    rewrite map_normalize_normalized_eq by trivial.
    reflexivity.
  Qed.
  
  Lemma epat_trans_top_correct h c p d:
    Forall (fun x => data_normalized h (snd x)) c ->
    (* XXX Why nil for local-env there?! Probably should have a interp_top with fixed nil local-env XXX *)
    lift_failure (interp h c p nil d) = nraenv_eval h c (nraenv_of_pat_top p) (drec nil) d.
  Proof.
    intros.
    rewrite <- (nraenv_of_pat_top_id h c); trivial.
    rewrite pat_trans_correct.
    rewrite pat_trans_top_pat_context; trivial; reflexivity.
  Qed.

  Section Top.
    (* Java equivalent: CampToNra.convert *)
    (* Toplevel translation call XXX TODO: Why are there two??? XXX *)
    Definition translate_pat_to_nraenv (p:pat) : nraenv :=
      (* Produces the initial plan *)
      NRAEnvAppEnv (nraenv_of_pat p) (NRAEnvConst (drec nil)).

  End Top.

  Section size.
    Require Import Omega.
    
    (** Proof showing linear size translation *)
    Lemma pat_trans_size p :
      nraenv_size (nraenv_of_pat p) <= 13 * pat_size p.
    Proof.
      induction p; simpl; omega.
    Qed.

  End size.

  Section sugar.
    Definition nraenv_of_pand (p1 p2:pat) : nraenv :=
      nraenv_of_pat (pand p1 p2).

    Definition nraenv_for_pand (q1 q2: nraenv) : nraenv :=
      NRAEnvUnop AFlatten
                 (NRAEnvAppEnv (NRAEnvMapEnv q2)
                               (NRAEnvUnop AFlatten
                                           (NRAEnvMap (NRAEnvBinop AMergeConcat NRAEnvEnv NRAEnvID)
                                                      (NRAEnvMap (NRAEnvConst (drec nil))
                                                                 (NRAEnvSelect NRAEnvID q1))))).
  
    Lemma nraenv_of_pand_works (p1 p2:pat) :
      nraenv_of_pat (pand p1 p2) = nraenv_for_pand (nraenv_of_pat p1) (nraenv_of_pat p2).
    Proof.
      reflexivity.
    Qed.

    (* WW *)

    Definition nraenv_of_WW (p:pat) :=
      nraenv_of_pat (WW p).

  End sugar.

End CAMPtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
