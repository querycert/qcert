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

Section CompConfig.
  Require Import List.
  Require Import String.
  
  (* Basic *)
  Require Import BasicSystem.
  Require Import TypingRuntime.
  Require Import ForeignReduceOps.

  Context {ft:foreign_type}.
  Context {fr:foreign_runtime}.
  Context {bm:brand_model}.
  
  Require Import OptimizerLogger.
  Require Import CompLang CompEnv.
  
  Section optim.
    Require Import TNNRCOptimizer.
    Require Import NRAEnvOptimizer.
    Require Import OptimizerStep.

    (* CompLang.type_of_language does not suffice, since some language 
       (the core ones) have optimizations specified in a different language 
       (via conversion) *)

    Definition optim_type_of_language (l:language) : Set :=
      match l with
      | L_nra => nraenv
      | L_nraenv_core => nraenv
      | L_nraenv => nraenv
      | L_nnrc_core => nnrc
      | L_nnrc => nnrc
      | _ => Empty_set
      end.

    Definition optim_config_list_type := list {l:language & (string * list (OptimizerStep (optim_type_of_language l)))}%type.

    Definition optim_config_list : optim_config_list_type
      := existT _ L_nra ("NRAEnv.Optim.NRAEnvOptimizer"%string, tnraenv_optim_list)
        :: existT _ L_nraenv_core ("NRAEnv.Optim.NRAEnvOptimizer"%string, tnraenv_optim_list)
        :: existT _ L_nraenv ("NRAEnv.Optim.NRAEnvOptimizer"%string, tnraenv_optim_list)
        :: existT _ L_nnrc_core ("NNRC.Optim.TNNRCOptimizer"%string,tnnrc_optim_list)
        :: existT _ L_nnrc ("NNRC.Optim.TNNRCOptimizer"%string,tnnrc_optim_list)
        :: nil.
      
    Definition optim_config : Set :=
      list (language * optim_phases_config).

    Definition optim_config_default : optim_config :=
      (* Same default optimizations for NRA, NRAEnv and NRAEnvCore *)
      (L_nra, default_nraenv_optim_phases)
        :: (L_nraenv_core, default_nraenv_optim_phases)
        :: (L_nraenv, default_nraenv_optim_phases)
        (* Same default optimizations for NNRC and NNRCCore *)
        :: (L_nnrc_core, default_nnrc_optim_phases)
        :: (L_nnrc, default_nnrc_optim_phases)
        :: nil.

    Definition get_default_optim_config (l:language) : optim_phases_config :=
      match lookup language_eq_dec optim_config_default l with
      | Some x => x
      | None => nil
      end.

    Definition get_optim_config (l:language) (oc:optim_config) : optim_phases_config :=
      match lookup language_eq_dec oc l with
      | Some opc => opc
      | None => get_default_optim_config l
      end.

    Require Import Permutation.

    Remark optim_config_list_default_in_sync :
      Permutation
        (map (@projT1 _ _) optim_config_list)
        (map fst optim_config_default).
    Proof.
      apply permutation_prover.
      vm_compute.
      trivial.
    Qed.
      
  End optim.

  Record driver_config :=
    mkDvConfig
      { comp_qname : string;
        comp_class_name : string; (* Class name different from rule name in Java case *)
        comp_brand_rel : list (string * string) (* brand_relation *);
        comp_input_type : rtype (* input type for inference *);
        comp_mr_vinit : string;
        comp_vdbindings : vdbindings;
        comp_java_imports : string;
        comp_optim_config : optim_config; }.

  (* Trivial driver configuration -- used in some proofs *)
  
  Definition trivial_driver_config : driver_config
    := mkDvConfig
         EmptyString
         EmptyString
         nil
         ⊥
         EmptyString
         nil
         EmptyString
         nil.

  (* Default driver configuration *)

  Definition default_dv_config :=
    mkDvConfig
      (* comp_qname = *) "query"
      (* class_name = *) "query"
      (* comp_brand_rel = *) nil
      (* comp_input_type = *) RType.Unit
      (* comp_mr_vinit = *) init_vinit
      (* comp_vdbindings = *) nil
      (* comp_java_imports = *) ""
      (* comp_optim_config = *) nil.

End CompConfig.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
