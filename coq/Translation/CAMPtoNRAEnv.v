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
  Definition envpat_fail := ANConst (dcoll nil).
  (* Java equivalent: CampToNra.envpat_match *)
  Definition envpat_match op := ANUnop AColl op.

  (** Translation from CAMP to EnvNRA *)

  (* Java equivalent: CampToNra.algenv_of_pat *)
  Fixpoint algenv_of_pat (p:pat) : algenv :=
    match p with
      | pconst d' => envpat_match (ANConst d')
      | punop uop p₁ => ANMap (ANUnop uop ANID) (algenv_of_pat p₁)
      | pbinop bop p₁ p₂ =>
        ANMap (ANBinop bop (ANUnop (ADot "a1") ANID) (ANUnop (ADot "a2") ANID))
              (ANProduct (ANMap (ANUnop (ARec "a1") ANID) (algenv_of_pat p₁))
                         (ANMap (ANUnop (ARec "a2") ANID) (algenv_of_pat p₂)))
      | pmap p₁ =>
        envpat_match
          (ANUnop AFlatten
                  (ANMap
                     (algenv_of_pat p₁) ANID))
      | passert p₁ =>
        ANMap (ANConst (drec nil)) (ANSelect ANID (algenv_of_pat p₁))
      | porElse p₁ p₂ => ANDefault (algenv_of_pat p₁) (algenv_of_pat p₂)
      | pit => envpat_match ANID
      | pletIt p₁ p₂ =>
        ANUnop AFlatten
               (ANMap (algenv_of_pat p₂)
                      (algenv_of_pat p₁))
      | pgetconstant s => envpat_match (ANGetConstant s)
      | penv => envpat_match ANEnv
      | pletEnv p₁ p₂ =>
        ANUnop AFlatten
               (ANAppEnv
                  (ANMapEnv (algenv_of_pat p₂))
                  (ANUnop AFlatten
                          (ANMap (ANBinop AMergeConcat ANEnv ANID) (algenv_of_pat p₁))))
      | pleft =>
        ANEither (envpat_match ANID) (envpat_fail)
      | pright =>
        ANEither (envpat_fail) (envpat_match ANID)
    end.

  (** top level version sets up the appropriate input 
      (with an empty context) 
  *)

  Definition algenv_of_pat_top p :=
    ANUnop AFlatten
           (ANMap (algenv_of_pat p) (ANUnop AColl ANID)).
  
  (** Theorem 4.2: lemma of translation correctness for patterns *)

  Local Open Scope alg_scope.

  Lemma pat_envtrans_correct h c q env d:
    lift_failure (interp h c q env d) = fun_of_algenv h c (algenv_of_pat q) (drec env) d.
  Proof.
    revert d env; induction q; simpl; intros.
    (* pconst *)
    - reflexivity.
    (* punop *)
    - rewrite <- IHq; clear IHq; simpl.
      destruct (interp h c q env d); try reflexivity.
      simpl; destruct (fun_of_unaryop h u res); reflexivity.
    (* pbinop *)
    - rewrite <- IHq1; rewrite <- IHq2; clear IHq1 IHq2.
      destruct (interp h c q1 env d); try reflexivity.
      destruct (interp h c q2 env d); try reflexivity.
      simpl; destruct (fun_of_binop h b res res0); reflexivity.
    (* pmap *)
    - destruct d; try reflexivity.
      unfold rmap_concat in *; simpl in *.
      unfold olift, liftpr ; simpl.
      induction l; try reflexivity; simpl.
      unfold lift_failure in *.
      rewrite <- (IHq a env); clear IHq.
      destruct (interp h c q env a); try reflexivity; simpl.
      * rewrite IHl; clear IHl; simpl.
        unfold lift; simpl.
        destruct (rmap (fun_of_algenv h c (algenv_of_pat q) (drec env)) l); try reflexivity; simpl.
        unfold rflatten, lift; simpl.
        destruct (oflat_map
            (fun x : data =>
             match x with
             | dcoll y => Some y
             | _ => None
             end) l0); reflexivity.
      * unfold lift, liftpr in *; simpl in *.
        revert IHl; generalize (rmap (fun_of_algenv h c (algenv_of_pat q) (drec env)) l); intros.
        destruct o; simpl in *.
        revert IHl; generalize (gather_successes (map (interp h c q env) l)); intros.
        destruct p; unfold rflatten in *; simpl in *; try congruence;
        revert IHl; generalize (oflat_map
              (fun x : data =>
               match x with
               | dcoll y => Some y
               | _ => None
               end) l0); simpl; intros;
        destruct o; simpl; congruence.
        revert IHl; generalize (gather_successes (map (interp h c q env) l)); intros.
        destruct p; try congruence.
    (* passert *)
    - rewrite <- IHq; clear IHq; simpl.
      destruct (interp h c q env d); try reflexivity.
      destruct res; try reflexivity; simpl.
      destruct b; reflexivity.
    (* porElse *)
    - rewrite <- IHq1; clear IHq1; simpl.
      destruct (interp h c q1 env d); simpl; auto.
    (* pit *)
    - reflexivity.
    (* pletIt *)
    - rewrite <- IHq1; clear IHq1; simpl.
      destruct (interp h c q1 env d); try reflexivity.
      simpl.
      specialize (IHq2 res).
      unfold pat_context_data in IHq2.
      rewrite <- IHq2; clear IHq2.
      destruct (interp h c q2 env res); reflexivity.      
    (* pgetconstant *)
    - destruct (edot c s); simpl; trivial.
    (* penv *)
    - eauto. 
    (* pletEnv *)
    - rewrite <- IHq1; clear IHq1; simpl.
      destruct (interp h c q1 env d); try reflexivity; simpl.
      destruct res; try reflexivity; simpl.
      destruct (merge_bindings env l); try reflexivity; simpl.
      specialize (IHq2 d l0).
      rewrite <- IHq2; clear IHq2; simpl.
      destruct (interp h c q2 l0 d); try reflexivity.
    (* pleft *)
    - destruct d; simpl; trivial.
    (* pright *)
    - destruct d; simpl; trivial.
  Qed.
  
  Lemma pat_envtrans_equiv_to_alg h c p bind d:
    nra_eval h (alg_of_pat p) (pat_context_data (drec (rec_sort c)) (drec bind) d) =
    fun_of_algenv h c (algenv_of_pat p) (drec bind) d.
  Proof.
    rewrite <- pat_envtrans_correct.
    rewrite pat_trans_correct; reflexivity.
  Qed.

  Lemma algenv_of_pat_top_id h c p d :
    Forall (fun x => data_normalized h (snd x)) c ->
    nra_eval h (alg_of_pat_top c p) d =
    fun_of_algenv h c (algenv_of_pat_top p) (drec nil) d.
  Proof.
    intros.
    simpl.
    rewrite <- pat_envtrans_equiv_to_alg.
    unfold pat_context_data.
    rewrite map_normalize_normalized_eq by trivial.
    reflexivity.
  Qed.
  
  Lemma epat_trans_top_correct h c p d:
    Forall (fun x => data_normalized h (snd x)) c ->
    (* XXX Why nil for local-env there?! Probably should have a interp_top with fixed nil local-env XXX *)
    lift_failure (interp h c p nil d) = fun_of_algenv h c (algenv_of_pat_top p) (drec nil) d.
  Proof.
    intros.
    unfold fun_of_algenv.
    rewrite <- (algenv_of_pat_top_id h c); trivial.
    rewrite pat_trans_correct.
    rewrite pat_trans_top_pat_context; trivial; reflexivity.
  Qed.

  Section Top.
    (* Java equivalent: CampToNra.convert *)
    (* Toplevel translation call XXX TODO: Why are there two??? XXX *)
    Definition translate_pat_to_algenv (p:pat) : algenv :=
      (* Produces the initial plan *)
      ANAppEnv (algenv_of_pat p) (ANConst (drec nil)).

  End Top.

  Section size.
    Require Import Omega.
    
    (** Proof showing linear size translation *)
    Lemma pat_trans_size p :
      algenv_size (algenv_of_pat p) <= 13 * pat_size p.
    Proof.
      induction p; simpl; omega.
    Qed.

  End size.

End CAMPtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
