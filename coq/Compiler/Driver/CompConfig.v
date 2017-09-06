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
  
  (* Common *)
  Require Import CommonSystem.
  Require Import TypingRuntime.
  Require Import ForeignReduceOps.

  Context {ft:foreign_type}.
  Context {fr:foreign_runtime}.
  Context {bm:brand_model}.
  
  Require Import OptimizerLogger.
  Require Import CompLang CompEnv.
  
  Section optim.
    Require Import NNRCOptimizer.
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
      := existT _ L_nraenv ("NRAEnv.Optim.NRAEnvOptimizer"%string, tnraenv_optim_list)
        :: existT _ L_nnrc ("NNRC.Optim.TNNRCOptimizer"%string,tnnrc_optim_list)
        :: nil.

    Definition optim_config : Set :=
      list (language * optim_phases_config).

    Definition optim_config_default : optim_config :=
      (* Default optimizations for NRAEnv *)
      (L_nraenv, default_nraenv_optim_phases)
        (* Default optimizations for NNRC *)
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

  Section constants.
    (* Each global variable has a localization and a local type *)
    Record constant_config :=
      mkConstantConfig { constant_localization : dlocalization;
                         constant_type : rtype;
                         constant_source : option string }.

    Definition constants_config := list (string * constant_config).

    Definition vdbindings_of_constants_config (cconf:constants_config) :=
      map (fun xy => (fst xy, (snd xy).(constant_localization))) cconf.

    Definition tbindings_of_constants_config (cconf:constants_config) :=
      map (fun xy => (fst xy, (snd xy).(constant_type))) cconf.

    Definition tdbinding_of_constant_config (gc:string * constant_config) :=
      let (s,cc) := gc in
      (s,v_and_t_to_dt cc.(constant_localization) cc.(constant_type)).
    
    Definition tdbindings_of_constants_config (gc:constants_config) :=
      map tdbinding_of_constant_config gc.
    
    (* Used to show a constant_config exists for a given tdbindings *)
    Definition constant_config_of_tdbinding_opt (td:string * drtype) : string * constant_config :=
      match td with
      | (s,Tlocal t) => (s,mkConstantConfig Vlocal t None)
      | (s,Tdistr t) => (s,mkConstantConfig Vdistr (Coll t) None)
      end.
    Definition constant_config_of_tdbinding (td:string * drtype) : string * constant_config :=
      match td with
      | (s,Tlocal t) => (s,mkConstantConfig Vlocal t None)
      | (s,Tdistr t) => (s,mkConstantConfig Vdistr t None)
      end.
    Definition constants_config_of_tdbindings (tds:tdbindings) : constants_config :=
      map constant_config_of_tdbinding tds.

    (* And it has the right merge property *)
    Lemma constants_config_of_tdbindings_merges (tds:tdbindings) :
        tdbindings_of_constants_config (constants_config_of_tdbindings tds)
        = tds.
    Proof.
      induction tds; simpl.
      - reflexivity.
      - unfold tdbindings_of_constants_config in *; simpl.
        rewrite IHtds; clear IHtds.
        destruct a; simpl in *.
        destruct d; simpl in *; reflexivity.
    Qed.

    (* One more property for vdbindings access to constant_config. *)
    Lemma vdbindings_of_constants_config_commutes x:
      vdbindings_of_constants_config (constants_config_of_tdbindings x)
      = vdbindings_of_tdbindings x.
    Proof.
      induction x; simpl.
      - reflexivity.
      - rewrite IHx.
        destruct a; simpl.
        destruct d; simpl; reflexivity.
    Qed.
    
    (* Used to show a constant_config exists for a given avoid list *)
    Definition one_tdbindings_of_avoid_list (avoid:list string) : tdbindings :=
      map (fun x => (x,Tlocal Unit)) avoid.

    Definition one_constant_config_of_avoid_list (avoid:list string) : constants_config :=
      constants_config_of_tdbindings (one_tdbindings_of_avoid_list avoid).

    Lemma one_constant_config_of_avoid_list_extracts (avoid:list string) :
      map fst (vdbindings_of_constants_config (one_constant_config_of_avoid_list avoid)) = avoid.
    Proof.
      unfold one_constant_config_of_avoid_list.
      induction avoid; simpl.
      - reflexivity.
      - rewrite IHavoid; reflexivity.
    Qed.
      
  End constants.
  
  Record driver_config :=
    mkDvConfig
      { comp_qname : string;
        comp_qname_lowercase : string;
        comp_class_name : string; (* Class name different from rule name in Java case *)
        comp_brand_rel : list (string * string) (* brand_relation *);
        comp_mr_vinit : string;
        comp_constants : constants_config;
        comp_java_imports : string;
        comp_optim_config : optim_config; }.

  (* Trivial driver configuration -- used in some proofs *)
  
  Definition trivial_driver_config : driver_config
    := mkDvConfig
         EmptyString
         EmptyString
         EmptyString
         nil
         EmptyString
         nil
         EmptyString
         nil.

  (* Default driver configuration *)

  Definition default_dv_config :=
    mkDvConfig
      (* comp_qname = *) "query"
      (* comp_qname_lowercase = *) "query"
      (* class_name = *) "query"
      (* comp_brand_rel = *) nil
      (* comp_mr_vinit = *) init_vinit
      (* comp_tdbindings = *) nil
      (* comp_java_imports = *) ""
      (* comp_optim_config = *) nil.

End CompConfig.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
