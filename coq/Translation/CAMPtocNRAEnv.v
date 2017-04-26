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

Section CAMPtocNRAEnv.
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
  (* Java equivalent: CampToNra.nraenv_fail *)
  Definition nraenv_fail := ANConst (dcoll nil).
  (* Java equivalent: CampToNra.nraenv_match *)
  Definition nraenv_match op := ANUnop AColl op.

  (** Translation from CAMP to EnvNRA *)

  (* Java equivalent: CampToNra.cnraenv_of_camp *)
  Fixpoint cnraenv_of_camp (p:camp) : cnraenv :=
    match p with
      | pconst d' => nraenv_match (ANConst d')
      | punop uop p₁ => ANMap (ANUnop uop ANID) (cnraenv_of_camp p₁)
      | pbinop bop p₁ p₂ =>
        ANMap (ANBinop bop (ANUnop (ADot "a1") ANID) (ANUnop (ADot "a2") ANID))
              (ANProduct (ANMap (ANUnop (ARec "a1") ANID) (cnraenv_of_camp p₁))
                         (ANMap (ANUnop (ARec "a2") ANID) (cnraenv_of_camp p₂)))
      | pmap p₁ =>
        nraenv_match
          (ANUnop AFlatten
                  (ANMap
                     (cnraenv_of_camp p₁) ANID))
      | passert p₁ =>
        ANMap (ANConst (drec nil)) (ANSelect ANID (cnraenv_of_camp p₁))
      | porElse p₁ p₂ => ANDefault (cnraenv_of_camp p₁) (cnraenv_of_camp p₂)
      | pit => nraenv_match ANID
      | pletIt p₁ p₂ =>
        ANUnop AFlatten
               (ANMap (cnraenv_of_camp p₂)
                      (cnraenv_of_camp p₁))
      | pgetconstant s => nraenv_match (ANGetConstant s)
      | penv => nraenv_match ANEnv
      | pletEnv p₁ p₂ =>
        ANUnop AFlatten
               (ANAppEnv
                  (ANMapEnv (cnraenv_of_camp p₂))
                  (ANUnop AFlatten
                          (ANMap (ANBinop AMergeConcat ANEnv ANID) (cnraenv_of_camp p₁))))
      | pleft =>
        ANEither (nraenv_match ANID) (nraenv_fail)
      | pright =>
        ANEither (nraenv_fail) (nraenv_match ANID)
    end.

  (** top level version sets up the appropriate input 
      (with an empty context) 
  *)

  Definition cnraenv_of_camp_top p :=
    ANUnop AFlatten
           (ANMap (cnraenv_of_camp p) (ANUnop AColl ANID)).
  
  (** Theorem 4.2: lemma of translation correctness for patterns *)

  Local Open Scope nra_scope.

  Lemma cnraenv_of_camp_correct h c q env d:
    lift_failure (interp h c q env d) = cnraenv_eval h c (cnraenv_of_camp q) (drec env) d.
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
        destruct (rmap (cnraenv_eval h c (cnraenv_of_camp q) (drec env)) l); try reflexivity; simpl.
        unfold rflatten, lift; simpl.
        destruct (oflat_map
            (fun x : data =>
             match x with
             | dcoll y => Some y
             | _ => None
             end) l0); reflexivity.
      * unfold lift, liftpr in *; simpl in *.
        revert IHl; generalize (rmap (cnraenv_eval h c (cnraenv_of_camp q) (drec env)) l); intros.
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
      unfold nra_context_data in IHq2.
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
  
  Lemma cnraenv_of_camp_equiv_to_nra h c p bind d:
    nra_eval h (nra_of_camp p) (nra_context_data (drec (rec_sort c)) (drec bind) d) =
    cnraenv_eval h c (cnraenv_of_camp p) (drec bind) d.
  Proof.
    rewrite <- cnraenv_of_camp_correct.
    rewrite camp_trans_correct; reflexivity.
  Qed.

  Lemma cnraenv_of_camp_top_id h c p d :
    Forall (fun x => data_normalized h (snd x)) c ->
    nra_eval h (nra_of_camp_top c p) d =
    cnraenv_eval h c (cnraenv_of_camp_top p) (drec nil) d.
  Proof.
    intros.
    simpl.
    rewrite <- cnraenv_of_camp_equiv_to_nra.
    unfold nra_context_data.
    rewrite map_normalize_normalized_eq by trivial.
    reflexivity.
  Qed.
  
  Lemma ecamp_trans_top_correct h c p d:
    Forall (fun x => data_normalized h (snd x)) c ->
    (* XXX Why nil for local-env there?! Probably should have a interp_top with fixed nil local-env XXX *)
    lift_failure (interp h c p nil d) = cnraenv_eval h c (cnraenv_of_camp_top p) (drec nil) d.
  Proof.
    intros.
    unfold cnraenv_eval.
    rewrite <- (cnraenv_of_camp_top_id h c); trivial.
    rewrite camp_trans_correct.
    rewrite camp_trans_top_nra_context; trivial; reflexivity.
  Qed.

  Section Top.
    (* Java equivalent: CampToNra.convert *)
    (* Toplevel translation call XXX TODO: Why are there two??? XXX *)
    Definition translate_camp_to_cnraenv (p:camp) : cnraenv :=
      (* Produces the initial plan *)
      ANAppEnv (cnraenv_of_camp p) (ANConst (drec nil)).

  End Top.

  Section size.
    Require Import Omega.
    
    (** Proof showing linear size translation *)
    Lemma camp_trans_size p :
      cnraenv_size (cnraenv_of_camp p) <= 13 * camp_size p.
    Proof.
      induction p; simpl; omega.
    Qed.

  End size.

  Section sugar.
    Definition cnraenv_of_pand (p1 p2:camp) : cnraenv :=
      cnraenv_of_camp (pand p1 p2).

    Definition cnraenv_for_pand (q1 q2: cnraenv) : cnraenv :=
      ANUnop AFlatten
             (ANAppEnv (ANMapEnv q2)
                       (ANUnop AFlatten
                               (ANMap (ANBinop AMergeConcat ANEnv ANID)
                                      (ANMap (ANConst (drec nil))
                                             (ANSelect ANID q1))))).
  
    Lemma cnraenv_of_pand_works (p1 p2:camp) :
      cnraenv_of_camp (pand p1 p2) = cnraenv_for_pand (cnraenv_of_camp p1) (cnraenv_of_camp p2).
    Proof.
      reflexivity.
    Qed.

    (* WW *)

    Definition cnraenv_of_WW (p:camp) :=
      cnraenv_of_camp (WW p).
  End sugar.
  
End CAMPtocNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
