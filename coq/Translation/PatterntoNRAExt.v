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

Section PatterntoNRAExt.

  Require Import String.
  Require Import List.

  Require Import Utils BasicRuntime.
  Require Import NRARuntime.
  Require Import Pattern.
  Require Import PatterntoNRA.

  Local Open Scope string_scope.
  Local Open Scope list_scope.

  (** Functions used to map input/ouput values between CAMP and NRA *)
  (* Input encoding *)

  Definition epat_bind := AXUnop (ADot "PBIND") AXID.
  Definition epat_data := AXUnop (ADot "PDATA") AXID.

  (* Match failure returns the empty sequence, success returns a singleton sequence *)
  Definition epat_fail := AXConst (dcoll nil).
  Definition epat_match op := AXUnop AColl op.
  Definition epat_context abind adata :=
    (AXBinop AConcat)
      ((AXUnop (ARec "PBIND")) abind)
      ((AXUnop (ARec "PDATA")) adata).
  Definition epat_withbinding :=
    epat_context epat_bind epat_bind.

  (** Translation from CAMP to ENRA *)

  Fixpoint algext_of_pat (p:pat) : algext :=
    match p with
      | pconst d' => epat_match (AXConst d')
      | punop uop p₁ => AXMap (AXUnop uop AXID) (algext_of_pat p₁)
      | pbinop bop p₁ p₂ =>
        AXMap (AXBinop bop (AXUnop (ADot "a1") AXID) (AXUnop (ADot "a2") AXID))
              (AXProduct (AXMap (AXUnop (ARec "a1") AXID) (algext_of_pat p₁))
                         (AXMap (AXUnop (ARec "a2") AXID) (algext_of_pat p₂)))
      | pmap p₁ =>
        epat_match
          (AXUnop AFlatten
                  (AXMap
                     (algext_of_pat p₁)
                     (AXUnnestTwo
                        "a1"
                        "PDATA"
                        (AXUnop AColl (AXBinop AConcat
                                               (AXUnop (ARec "PBIND") (AXUnop (ADot "PBIND") AXID))
                                               (AXUnop (ARec "a1") (AXUnop (ADot "PDATA") AXID)))))))
      | passert p₁ =>
        AXMap (AXConst (drec nil)) (AXSelect AXID (algext_of_pat p₁))
      | porElse p₁ p₂ =>
        AXDefault (algext_of_pat p₁) (algext_of_pat p₂)
      | pit => epat_match epat_data
      | pletIt p₁ p₂ =>
        AXUnop AFlatten
               (AXMap (algext_of_pat p₂)
                      (AXUnnestTwo
                         "a1"
                         "PDATA"
                         (AXUnop AColl
                                 (AXBinop AConcat
                                          (AXUnop (ARec "PBIND") (AXUnop (ADot "PBIND") AXID))
                                          (AXUnop (ARec "a1") (algext_of_pat p₁))))))
      | penv => epat_match epat_bind
      | pletEnv p₁ p₂ =>
        AXUnop AFlatten
               (AXMap
                  (algext_of_pat p₂)
                  (AXUnnestTwo
                     "PBIND1"
                     "PBIND"
                     (AXMap (AXBinop AConcat
                                     (AXUnop (ARec "PDATA") (AXUnop (ADot "PDATA") AXID))
                                     (AXUnop (ARec "PBIND1") (AXBinop AMergeConcat
                                                                      (AXUnop (ADot "PBIND") AXID)
                                                                      (AXUnop (ADot "PBIND1") AXID))))
                          (AXUnnestTwo
                             "a1"
                             "PBIND1"
                             (AXUnop AColl
                                    (AXBinop AConcat
                                            AXID
                                            (AXUnop (ARec "a1") (algext_of_pat p₁))))))))
      | pleft =>
        AXApp (AXEither (epat_match AXID) (epat_fail)) epat_data
      | pright =>
        AXApp (AXEither (epat_fail) (epat_match AXID)) epat_data
    end.

  (** top level version sets up the appropriate input 
      (with an empty context) 
  *)

  Definition algext_of_pat_top p :=
    AXUnop AFlatten
           (AXMap
              (algext_of_pat p)
              (AXUnop AColl
                      (AXBinop AConcat
                               (AXUnop (ARec "PBIND") (AXConst (drec nil)))
                               (AXUnop (ARec "PDATA") AXID)))).

  (** Theorem 4.2: lemma of translation correctness for patterns *)

  Lemma algext_pat_id p :
    alg_of_algext (algext_of_pat p) = alg_of_pat p.
  Proof.
    induction p; simpl; try reflexivity.
    - rewrite IHp; reflexivity.
    - rewrite IHp1; rewrite IHp2; reflexivity.
    - rewrite IHp; reflexivity.
    - rewrite IHp; reflexivity.
    - rewrite IHp1; rewrite IHp2; reflexivity.
    - rewrite IHp1; rewrite IHp2; reflexivity.
    - rewrite IHp1; rewrite IHp2; reflexivity.
  Qed.
      
  Lemma epat_trans_correct h p bind d:
    lift_failure (interp h p bind d) = fun_of_algext h (algext_of_pat p) (pat_context_data (drec bind) d).
  Proof.
    unfold fun_of_algext.
    rewrite algext_pat_id; simpl.
    apply pat_trans_correct.
  Qed.

  Lemma algext_of_pat_top_id p :
    alg_of_algext (algext_of_pat_top p) = alg_of_pat_top p.
  Proof.
    simpl.
    unfold alg_of_pat_top.
    rewrite algext_pat_id; reflexivity.
  Qed.
  
  Lemma epat_trans_top_correct h p d:
    lift_failure (interp h p nil d) = fun_of_algext h (algext_of_pat_top p) d.
  Proof.
    unfold fun_of_algext.
    rewrite algext_of_pat_top_id.
    apply pat_trans_top_correct.
  Qed.

End PatterntoNRAExt.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
