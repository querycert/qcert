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

Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import List.
Require Import EquivDec.

Require Import Utils BasicRuntime.
Require Import LData.
Require Import NNRCRuntime NNRCMRRuntime ForeignToReduceOps.

Local Open Scope list_scope.

Section NNRCMRtoNNRC.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {ftoredop:foreign_to_reduce_op}.

  Context (h:brand_relation_t).

  Definition map_to_nnrc (map:map_fun) (inputn:nrc) :=
    match map with
    | MapDist (v, n) =>
      NRCFor v inputn n
    | MapDistFlatten (v, n) =>
      NRCUnop AFlatten (NRCFor v inputn n)
    | MapScalar (v, n) =>
      NRCUnop AFlatten (NRCFor v (NRCUnop AColl inputn) n)
    end.

  Definition unlocalized (input_d:localized_data) : data :=
    match input_d with
    | Dscalar d => d
    | Ddistributed dl => dcoll dl
    end.
  
  Lemma rmap_function_with_no_free_vars_env v n l env :
    function_with_no_free_vars (v, n) ->
    rmap (fun d : data => nrc_eval h ((v, d) :: nil) n) l =
    rmap (fun d1 : data => nrc_eval h ((v, d1) :: env) n) l.
  Proof.
    intros.
    induction l; try reflexivity.
    simpl.
    unfold function_with_no_free_vars in *; simpl in *.
    rewrite <- (nrc_eval_single_context_var_cons h env n v a H).
    destruct (nrc_eval h ((v, a) :: nil) n).
    - rewrite IHl; reflexivity.
    - reflexivity.
  Qed.
  
  Lemma map_to_nnrc_correct env (map:map_fun) (input_d:localized_data) (inputn:nrc) :
    map_well_formed map ->
    map_well_localized map input_d ->
    nrc_eval h env inputn = Some (unlocalized input_d) ->
    lift dcoll (mr_map_eval h map input_d) = nrc_eval h env (map_to_nnrc map inputn).
  Proof.
    intros.
    destruct map; destruct input_d; simpl in *; try contradiction.
    - destruct p; simpl.
      rewrite H1.
      f_equal.
      apply (rmap_function_with_no_free_vars_env _ _ _ _ H).
    - destruct p; simpl.
      rewrite H1; simpl.
      autorewrite with alg.
      f_equal; f_equal.
      apply (rmap_function_with_no_free_vars_env _ _ _ _ H).
    - destruct p; simpl.
      rewrite H1; simpl.
      rewrite (nrc_eval_single_context_var_cons h env n v d H).
      destruct (nrc_eval h ((v, d) :: env) n); simpl; try reflexivity.
      unfold rflatten; simpl.
      destruct d0; try reflexivity.
      rewrite app_nil_r.
      reflexivity.
  Qed.

  Definition foreign_of_reduce_op (op:reduce_op) :=
    match op with
    | RedOpForeign fop => NRCConst dunit (* Need Louis or Avi's advice here *)
    end.
  
  Definition reduce_to_nnrc (red:reduce_fun) (inputn:nrc) : nrc :=
    match red with
    | RedId => inputn
    | RedCollect (v, n) => NRCLet v inputn n
    | RedOp op => (foreign_of_reduce_op op)
    | RedSingleton => NRCConst dunit (* This will be a problem, again, ...*)
    end.
  
  Lemma reduce_to_nnrc_correct env (red:reduce_fun) (input_d:list data) (inputn:nrc) :
    reduce_well_formed red ->
    nrc_eval h env inputn = Some (dcoll input_d) ->
    lift unlocalized (mr_reduce_eval h red input_d) = nrc_eval h env (reduce_to_nnrc red inputn).
  Proof.
    intros.
    destruct red; simpl in *.
    (* RedId *)
    - auto.
    (* RedCollect *)
    - destruct p; simpl.
      rewrite H0; simpl.
      rewrite <- (nrc_eval_single_context_var_cons h env n v (dcoll input_d) H).
      destruct (nrc_eval h ((v, dcoll input_d) :: nil) n); reflexivity.
    (* RedOp *)
    - admit.
    (* RedSingleton *)
    - admit.
  Admitted.

  Definition map_reduce_to_nnrc (inputn:nrc) (map:map_fun) (reduce:reduce_fun) :=
    reduce_to_nnrc reduce (map_to_nnrc map inputn).
  
  Definition nnrcmr_to_nnrc (mr:mr) : nrc :=
    NRCLet (mr_output mr)
           (map_reduce_to_nnrc (NRCVar (mr_input mr)) (mr_map mr) (mr_reduce mr))
           (NRCVar (mr_output mr)).

End NNRCMRtoNNRC.


(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
