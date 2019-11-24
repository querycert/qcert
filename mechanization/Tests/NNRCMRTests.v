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

Require Import BrandRelation.

Require Import ZArith.
Local Open Scope Z_scope.
Require Import String.
Local Open Scope string.
Require Import List.
Import ListNotations.

Require Import CommonSystem.
Require Import CAMPRuntime.
Require Import CAMPRuleRuntime.
Require Import TrivialModel.
Require Import CompEnv.
Require Import CompDriver.
Require Import CompEval.
Require Import NNRCShadow.
Require Import NNRC.
Require Import NNRCtoNNRCMR.
  
(* This module encodes the examples in sample-rules.txt *)
Section NNRCMRTest.

Local Open Scope camp_rule_scope.
Example R01 :=
  rule_when ("c" INSTANCEOF ["entities.Customer"] WHERE (passert (pbinop AEq (pbdot "age" (pit)) (#` 32))));;
  rule_return (pbinop ASConcat (toString (#` "Customer =")) (toString (pletIt ((lookup "c")) (pbdot "name" (pit)))))
.

Definition test01BrandRelationList := [("entities.MainEntity", "com.ibm.ia.model.Entity")
   ;("entities.Purchase", "com.ibm.ia.model.Entity")
   ;("entities.Customer", "com.ibm.ia.model.Entity")].

Program Instance test01BrandRelation : brand_relation 
 := mkBrand_relation test01BrandRelationList (eq_refl _) (eq_refl _).

Definition com_ibm_ia_model_Entity : rtype
 := Rec Open (rec_sort []) rec_sort_pf.

Definition entities_Customer : rtype
 := Rec Open (rec_sort [("cid", Nat)
  ;("age", Nat)
  ;("name", String)]) rec_sort_pf.

Definition entities_Purchase : rtype
 := Rec Open (rec_sort [("cid", Nat)
  ;("pid", Nat)
  ;("name", String)
  ;("quantity", Nat)]) rec_sort_pf.

Definition entities_MainEntity : rtype
 := Rec Open (rec_sort [("id", Nat)
  ;("doubleAttribute", Nat)
  ;("stringId", String)]) rec_sort_pf.

Definition test01Types :=
   (rec_sort [("com.ibm.ia.model.Entity", com_ibm_ia_model_Entity)
   ;("entities.Customer", entities_Customer)
   ;("entities.Purchase", entities_Purchase)
   ;("entities.MainEntity", entities_MainEntity)]).

Definition test01BrandContext := mkBrand_context test01Types (eq_refl _).

Local Obligation Tactic := fast_refl.
Program Instance test01BrandModel : brand_model 
 := mkBrand_model test01BrandRelation test01BrandContext (eq_refl _) (eq_refl _).

Definition exampleWMType : rtype := Coll (Any).

Example exampleWM : list data := [
  dbrand (singleton "entities.Customer") (drec (rec_sort [("name",dstring "John Doe"); ("cid",dnat (123)); ("age",dnat (32))]));
  dbrand (singleton "entities.Customer") (drec (rec_sort [("name",dstring "Jane Doe"); ("cid",dnat (124)); ("age",dnat (32))]));
  dbrand (singleton "entities.Customer") (drec (rec_sort [("name",dstring "Jim Does"); ("cid",dnat (125)); ("age",dnat (34))]));
  dbrand (singleton "entities.Customer") (drec (rec_sort [("name",dstring "Jill Does"); ("cid",dnat (126)); ("age",dnat (32))]));
  dbrand (singleton "entities.Customer") (drec (rec_sort [("name",dstring "Joan Doe"); ("cid",dnat (127)); ("age",dnat (34))]));
  dbrand (singleton "entities.Customer") (drec (rec_sort [("name",dstring "James Do"); ("cid",dnat (128)); ("age",dnat (35))]));
  dbrand (singleton "entities.Purchase") (drec (rec_sort [("name",dstring "Tomatoe"); ("pid",dnat (1)); ("quantity",dnat (3)); ("cid",dnat (123))]));
  dbrand (singleton "entities.Purchase") (drec (rec_sort [("name",dstring "Potatoe"); ("pid",dnat (2)); ("quantity",dnat (1)); ("cid",dnat (123))]));
  dbrand (singleton "entities.Purchase") (drec (rec_sort [("name",dstring "Stiletto"); ("pid",dnat (3)); ("quantity",dnat (64)); ("cid",dnat (125))]));
  dbrand (singleton "entities.Purchase") (drec (rec_sort [("name",dstring "Libretto"); ("pid",dnat (4)); ("quantity",dnat (62)); ("cid",dnat (126))]));
  dbrand (singleton "entities.Purchase") (drec (rec_sort [("name",dstring "Dough"); ("pid",dnat (5)); ("quantity",dnat (4)); ("cid",dnat (128))]));
  dbrand (singleton "entities.Purchase") (drec (rec_sort [("name",dstring "Croissant"); ("pid",dnat (6)); ("quantity",dnat (2)); ("cid",dnat (128))]));
  dbrand (singleton "entities.MainEntity") (drec (rec_sort [("id",dnat (201)); ("stringId",dstring "201"); ("doubleAttribute",dnat (4))]));
  dbrand (singleton "entities.MainEntity") (drec (rec_sort [("id",dnat (202)); ("stringId",dstring "202"); ("doubleAttribute",dnat (100))]))
].

Example Result_R01_JRules := List.map dconst [
  "Customer =John Doe";
  "Customer =Jane Doe";
  "Customer =Jill Does"
].
Example R01_nrcmr := rule_to_nnrcmr R01.
Example Result_R01_Coq := lift_rule_failure (@eval_nnrcmr_world _ _ test01BrandRelationList R01_nrcmr exampleWM).
Eval vm_compute in Result_R01_Coq.
Example R01_verify : validate_success Result_R01_Coq Result_R01_JRules = true.
Proof. fast_refl. Qed.

(*
Set Printing Depth 1000.
Eval vm_compute in R01_nrcmr.
*)

(* MR chain compiler *)

Example nrc_R01 := (rule_to_nraenv_to_nnrc_optim R01).
(* Eval vm_compute in nrc_R01. *)

Example free_vars_R01 :=  List.map (fun x => (x, Vdistr)) (nnrc_free_vars nrc_R01).
Example nrcmr_R01 := nnrc_to_nnrcmr "unit" free_vars_R01 nrc_R01.
(* Eval vm_compute in nrcmr_R01. *)

Example nrcmr_R01_optimized :=
  nnrcmr_optim nrcmr_R01.
(* Eval vm_compute in nrcmr_R01_optimized. *)



(* ---------------- *)

(* NNRC Example 06 from https://github.rtp.raleigh.ibm.com/meta/global-rules/issues/23 :
     let one = { 1 } in
     let b = { x = one | x in venv } in
     { not(y) | y in b }
*)
Example ex06 :=
  NNRCLet "x1" (NNRCUnop AColl (NNRCConst (dnat 1)))
          (NNRCLet "x2" (NNRCFor "x3" (NNRCVar "x0")
                               (NNRCBinop AEq (NNRCVar "x3") (NNRCVar "x1")))
                  (NNRCFor "x4" (NNRCVar "x2")
                          (NNRCUnop ANeg (NNRCVar "x4")))).
Example ex06nnrcmr_chain := nnrc_to_nnrcmr_chain "x0" nil ex06.

(* Eval compute in ex06nnrcmr_chain. *)

(* ---------------- *)

(* nested loop *)

Example loop_nest :=
  let i := "x1" in
  let j := "x2" in
  NNRCFor i (NNRCConst (dcoll (dnat 1 :: dnat 2 :: nil)))
         (NNRCFor j (NNRCConst (dcoll (dstring "a" :: dstring "b" :: nil)))
         (NNRCVar j)).

Eval vm_compute in @eval_nnrc _ nil loop_nest nil.

Example loop_nest_mr := nnrc_to_nnrcmr "x0" nil loop_nest.
Eval vm_compute in loop_nest_mr.
Eval vm_compute in @eval_nnrcmr _ _ nil loop_nest_mr (("x0", dunit)::nil).


(* ---------------- *)

(* Small examples *)

(* 1 *)

Example nrc_const := NNRCConst (dnat 1).
Example free_vars_const : list (var * dlocalization) := nil.
Example nrcmr_const := nnrc_to_nnrcmr_chain nrc_const "unit" nil "output".
Eval vm_compute in nrcmr_const.
Example env_const : bindings := nil.
Example res_const :=
  lift (fun env => nrcmr_eval nil env nrcmr_const) (load_init_env "unit" free_vars_const env_const).
Eval vm_compute in olift get_result res_const.


(* count { 1; 1 } *)

Example nrc_count_const := NRCUnop ACount (NRCConst (dcoll (dnat 1 :: dnat 1 :: nil))).
Example free_vars_count_const : list (var * localization) := nil.
Example nrcmr_count_const := nnrc_to_nnrcmr_chain nrc_count_const "unit" nil "output".
Eval vm_compute in nrcmr_count_const.
Example env_count_const : bindings := nil.
Example res_count_const :=
  lift (fun env => nrcmr_eval nil env nrcmr_count_const) (load_init_env "unit" free_vars_count_const env_count_const).
Eval vm_compute in olift get_result res_count_const.

(* count input *)

Example nrc_count_input := NRCUnop ACount (NRCVar "input").
Example free_vars_count_input := (("input", Vscalar)::nil).
Example nrcmr_count_input := nnrc_to_nnrcmr_chain nrc_count_input "unit" free_vars_count_input "output".
Eval vm_compute in nrcmr_count_input.
Example env_count_input : bindings := ("input", dcoll (dnat 1 :: dnat 1 :: nil)) :: nil.
Example res_count_input :=
  lift (fun env => nrcmr_eval nil env nrcmr_count_input) (load_init_env "unit" free_vars_count_input env_count_input).
Eval vm_compute in olift get_result res_count_input.

(* count dist_input *)

Example nrc_count_distinput := NRCUnop ACount (NRCVar "distinput").
Example free_vars_count_distinput := (("distinput", Vdistributed)::nil).
Example nrcmr_count_distinput := nnrc_to_nnrcmr_chain nrc_count_distinput "unit" free_vars_count_distinput "output".
Eval vm_compute in nrcmr_count_distinput.
Example env_count_distinput : bindings := ("distinput", dcoll (dnat 1 :: dnat 1 :: nil)) :: nil.
Example res_count_distinput :=
  lift (fun env => nrcmr_eval nil env nrcmr_count_distinput) (load_init_env "unit" free_vars_count_distinput env_count_distinput).
Eval vm_compute in olift get_result res_count_distinput.

(* input1 U input2 (input1 scalar and input2 distributed) *)
Example nrc_two_vars := NRCBinop AUnion (NRCVar "input1") (NRCVar "input2").
Example free_vars_two_vars := (("input1", Vscalar)::("input2", Vdistributed)::nil).
Example nrcmr_two_vars := nnrc_to_nnrcmr_chain nrc_two_vars "unit" free_vars_two_vars "output".
Eval vm_compute in nrcmr_two_vars.
Example env_two_vars : bindings := ("input1", dcoll (dnat 1 :: dnat 2 :: nil)) :: ("input2", dcoll (dnat 3 :: dnat 4 :: nil)) :: nil.
Example res_two_vars :=
  lift (fun env => nrcmr_eval nil env nrcmr_two_vars) (load_init_env "unit" free_vars_two_vars env_two_vars).
Eval vm_compute in olift get_result res_two_vars.


(* for x in { 0 } U input do x + 1  (input scalar) *)
Example nrc_loop_scalar :=
  NRCFor "x"
         (NRCBinop AUnion (NRCConst (dcoll (dnat 0 :: nil))) (NRCVar "input"))
         (NRCBinop (ABArith ArithPlus) (NRCVar "x") (NRCConst (dnat 1))).
Example free_vars_loop_scalar := (("input", Vscalar)::nil).
Example nrcmr_loop_scalar := nnrc_to_nnrcmr_chain nrc_loop_scalar "unit" free_vars_loop_scalar "output".
Eval vm_compute in nrcmr_loop_scalar.
Example env_loop_scalar : bindings := ("input", dcoll (dnat 1 :: dnat 2 :: nil)) :: nil.
Example res_loop_scalar :=
  lift (fun env => nrcmr_eval nil env nrcmr_loop_scalar) (load_init_env "unit" free_vars_loop_scalar env_loop_scalar).
Eval vm_compute in olift get_result res_loop_scalar.

Example nrcmr_loop_scalar_optimized :=
  mr_optimize nrcmr_loop_scalar ("output"::nil).
Eval vm_compute in nrcmr_loop_scalar_optimized.
Example res_loop_scalar_optimized :=
  lift (fun env => nrcmr_eval nil env nrcmr_loop_scalar) (load_init_env "unit" free_vars_loop_scalar env_loop_scalar).
Eval vm_compute in olift get_result res_loop_scalar.



(* for x in { 0 } U input do x + 1  (input distributed) *)
Example nrc_loop_dist :=
  NRCFor "x"
         (NRCBinop AUnion (NRCConst (dcoll (dnat 0 :: nil))) (NRCVar "input"))
         (NRCBinop (ABArith ArithPlus) (NRCVar "x") (NRCConst (dnat 1))).
Example free_vars_loop_dist := (("input", Vdistributed)::nil).
Example nrcmr_loop_dist := nnrc_to_nnrcmr_chain nrc_loop_dist "unit" free_vars_loop_dist "output".
Eval vm_compute in nrcmr_loop_dist.
Example env_loop_dist : bindings := ("input", dcoll (dnat 1 :: dnat 2 :: nil)) :: nil.
Example res_loop_dist :=
  lift (fun env => nrcmr_eval nil env nrcmr_loop_dist) (load_init_env "unit" free_vars_loop_dist env_loop_dist).
Eval vm_compute in olift get_result res_loop_dist.


End SampleRules.

