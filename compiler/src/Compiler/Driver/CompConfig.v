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

Require Import List.
Require Import String.
Require Import Permutation.
Require Import ZArith.

(* Common *)
Require Import Utils.

Require Import CommonSystem.
Require Import TypingRuntime.
Require Import ForeignReduceOps.

Require Import OptimizerLogger.
Require Import CompLang CompEnv.

Require Import NNRCOptimizer.
Require Import NRAEnvOptimizer.
Require Import NNRSimpOptimizer.
Require Import OptimizerStep.

Section CompConfig.
  Context {ft:foreign_type}.
  Context {fr:foreign_runtime}.
  Context {bm:brand_model}.

  Section optim.
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
      | L_nnrs_imp => nnrs_imp
      | _ => Empty_set
      end.

    Definition optim_config_type_of_language (l:language) : Set :=
      match l with
      | L_nnrs_imp => list (OptimizerStep nnrs_imp_expr) * list (OptimizerStep nnrs_imp_stmt) * list (OptimizerStep nnrs_imp)
      | _ => list (OptimizerStep (optim_type_of_language l))
      end.

    Definition optim_config_list_type := list {l:language & (string * optim_config_type_of_language l)}%type.

    Definition optim_config_list : optim_config_list_type
      := existT _ L_nraenv ("NRAEnv.Optim.NRAEnvOptimizer"%string, tnraenv_optim_list)
       :: existT _ L_nnrc ("NNRC.Optim.TNNRCOptimizer"%string,tnnrc_optim_list)
       :: existT _ L_nnrs_imp ("NNRSimp.Optim.NNRSimpOptimizer"%string,
                               (nnrs_imp_expr_optim_list, nnrs_imp_stmt_optim_list, nnrs_imp_optim_list))
        :: nil.

    Definition optim_config_of_language (l:language) : Set :=
      list match l return Set with
      | L_nnrs_imp => optim_phase3_config
      | _ => optim_phase_config
      end.

    Definition optim_config : Set :=
      list ({l:language & optim_config_of_language l}).

    Definition optim_config_default : optim_config :=
      (* Default optimizations for NRAEnv *)
      (existT _ L_nraenv default_nraenv_optim_phases)
        (* Default optimizations for NNRC *)
        :: (existT _ L_nnrc default_nnrc_optim_phases)
        (* Default optimizations for NNRSimp *)
        :: (existT _ L_nnrs_imp default_nnrs_imp_optim_phases)
        :: nil.

    (* lookup for dependent association lists *)
        Fixpoint lookupT {A : Type} {B:A->Type}
             (dec : forall a a' : A, {a = a'} + {a <> a'})
             (l:list (sigT B)) (a:A) : option (B a)
      := match l with
         | nil => None
         | existT _ f v :: os =>
           match dec f a with
           | left pf => Some (match pf with eq_refl _ => v end)
           | right _ => lookupT dec os a
           end
         end.
    
    Definition get_default_optim_config (l:language) : optim_config_of_language l :=
      match lookupT language_eq_dec optim_config_default l with
      | Some x => x
      | None => nil
      end.

    Definition get_optim_config (l:language) (oc:optim_config) : optim_config_of_language l :=
      match lookupT language_eq_dec oc l with
      | Some opc => opc
      | None => get_default_optim_config l
      end.

    Remark optim_config_list_default_in_sync :
      Permutation
        (map (@projT1 _ _) optim_config_list)
        (map (@projT1 _ _) optim_config_default).
    Proof.
      apply permutation_prover.
      vm_compute.
      trivial.
    Qed.

    Local Open Scope string.

    Section serialization.
      Section to_json.

        Definition optimizer_step_to_json {lang:Set}
                   (optim:OptimizerStep lang) : json
          := jobject (("name", jstring (optim_step_name optim))
                     ::("description", jstring (optim_step_description optim))
                     ::("lemma", jstring(optim_step_lemma optim))
                     :: nil).

        Definition optim_config_type_of_language_to_json {l:language} :
          optim_config_type_of_language l -> json
          := match l with
             | L_nnrs_imp =>
               (fun '(optims_e, optims_s, optims_t) =>
                  jobject (("expr", jarray (map optimizer_step_to_json optims_e))
                          ::("stmt", jarray (map optimizer_step_to_json optims_s))
                          ::("top",jarray (map optimizer_step_to_json optims_t))
                          ::nil))
             | _ => (fun optims =>
                       jobject (("top", jarray (map optimizer_step_to_json optims))
                               ::nil))
             end.

        Definition optim_config_elem_type_to_json
                   (poc:{l:language & (string * optim_config_type_of_language l)}%type) : json
          := let '(existT _ l (optim_module_name, oc)) := poc in
             jobject (("language", jobject (
                                       ("name", jstring (name_of_language l))
                                         ::("modulebase", jstring optim_module_name)
                                         ::nil))
                        ::("optims", optim_config_type_of_language_to_json oc)
                        ::nil).
             
        Definition optim_config_list_type_to_json (l:optim_config_list_type) : json
          := jobject (("optims", jarray (map optim_config_elem_type_to_json l))::nil).

        Definition optim_config_list_to_json : json
          := optim_config_list_type_to_json optim_config_list.

        Definition optim_phase_config_to_json (phase:optim_phase_config) : json
          := let '(phase_name, optims, phase_iter):=phase in
             jobject ( ("name", jstring phase_name)
                      :: ("optims", jobject (("top", jarray (map jstring optims))::nil))
                      :: ("iter", jnumber (float_of_int (Z.of_nat phase_iter)))
                      :: nil).

        Definition optim_phase3_config_to_json (phase:optim_phase3_config)
          := let '(phase_name, optims_e, optims_s, optims_t, phase_iter):=phase in
             jobject ( ("name", jstring phase_name)
                      :: ("optims",
                          jobject (("expr", jarray (map jstring optims_e))
                                  :: ("stmt", jarray (map jstring optims_s))
                                  :: ("top", jarray (map jstring optims_t))
                                  ::nil))
                      :: ("iter", jnumber (float_of_int (Z.of_nat phase_iter)))
                      :: nil).

        Definition optim_config_of_language_to_json {l:language} : 
          optim_config_of_language l -> list json
          := match l with
             | L_nnrs_imp =>
               map optim_phase3_config_to_json
             | _ =>
               map optim_phase_config_to_json
             end.    
        
        Definition optim_config_elem_to_json (oc:({l:language & optim_config_of_language l})) : json
          := let '(existT _ language_name phases) := oc in
             jobject ( ("language", jstring (name_of_language language_name))
                      :: ("phases", jarray (optim_config_of_language_to_json phases))
                      :: nil).
        
        Definition optim_config_to_json (oc:optim_config) : json
          := jarray (map optim_config_elem_to_json oc).

        Definition optim_config_default_to_json : json
          := optim_config_to_json optim_config_default.

      End to_json.

        Section from_json.
          Let json_to_optim_phase_err {A:Type} (s:string) : string + A
          := inl (append "Ill-formed phase optim configuration" s).

        Definition unjstringlist {E} (err:E+string) (l:list json) : E + list string
          := lift_err_map
               (fun d =>
                  match d with
                  | jstring s => inr s
                  | _ => err
                  end) l.

        Definition json_to_optim_phase_config (d:json) : string + optim_phase_config
          := match d with
             | jobject rec =>
               match lookup string_dec rec "name" with
               | None => json_to_optim_phase_err " (missing name)"
               | Some (jstring name) =>
                 match lookup string_dec rec "optims" with
                 | None => json_to_optim_phase_err " (missing optims)"
                 | Some (jobject optims) =>
                   match lookup string_dec optims "top" with
                   | None => json_to_optim_phase_err " (missing optims.top)"
                   | Some (jarray top) =>
                     match unjstringlist (json_to_optim_phase_err " (one of the optims is not a string)") top with
                     | inl e => inl e
                     | inr optims_list =>                              
                       match lookup string_dec rec "iter" with
                       | None => json_to_optim_phase_err " (missing iter)"
                       | Some (jnumber iter) =>
                         let iter' := float_truncate iter in
                         if Z_lt_dec iter' 0
                         then json_to_optim_phase_err " (the number of iterations is negative)"
                         else inr (name, optims_list, Z.to_nat iter')
                       | Some _ => json_to_optim_phase_err " (iter is not a number)"
                       end
                     end
                   | Some _ =>  json_to_optim_phase_err " (optims.top is not a list)"
                   end
                 | Some _ => json_to_optim_phase_err " (optims is not a list)"
                 end
               | Some _ => json_to_optim_phase_err " (name is not a string)"
               end
             | _ => json_to_optim_phase_err " (not a record)"
             end.
        
        Definition json_to_optim_phase3_config (d:json) : string + optim_phase3_config
          := match d with
             | jobject rec =>
               match lookup string_dec rec "name" with
               | None => json_to_optim_phase_err " (missing name)"
               | Some (jstring name) =>
                 match lookup string_dec rec "optims" with
                 | None => json_to_optim_phase_err " (missing optims)"
                 | Some (jobject optims) =>
                   match lookup string_dec optims "expr" with
                   | None => json_to_optim_phase_err " (missing optims.expr)"
                   | Some (jarray optims_e) =>
                     match unjstringlist (json_to_optim_phase_err " (one of the optims.expr is not a string)") optims_e with
                   | inl e => inl e
                   | inr optims_list_e =>
                     match lookup string_dec optims "stmt" with
                     | None => json_to_optim_phase_err " (missing optims.stmt)"
                     | Some (jarray optims_s) =>
                       match unjstringlist (json_to_optim_phase_err " (one of the optims.stmt is not a string)") optims_s with
                       | inl e => inl e
                       | inr optims_list_s =>
                         match lookup string_dec optims "top" with
                         | None => json_to_optim_phase_err " (missing optims.top)"
                         | Some (jarray optims_t) =>
                           match unjstringlist (json_to_optim_phase_err " (one of the optims.top is not a string)") optims_t with
                           | inl e => inl e
                           | inr optims_list_t =>
                        match lookup string_dec rec "iter" with
                        | None => json_to_optim_phase_err " (missing iter)"
                        | Some (jnumber iter) =>
                          let iter' := float_truncate iter in 
                          if Z_lt_dec iter' 0
                          then json_to_optim_phase_err " (the number of iterations is negative)"
                          else inr (name, optims_list_e, optims_list_s, optims_list_t, Z.to_nat iter')
                        | Some _ => json_to_optim_phase_err " (iter is not a number)"
                        end
                      end
                 | Some _ => json_to_optim_phase_err " (optims.top is not a list)"
                         end
                       end
                 | Some _ => json_to_optim_phase_err " (optims.stmt is not a list)"
                     end
                   end
                 | Some _ => json_to_optim_phase_err " (optims.expr is not a list)"
                   end
                 | Some _ => json_to_optim_phase_err " (optims is not a list)"
                 end
               | Some _ => json_to_optim_phase_err " (name is not a string)"
               end
             | _ => json_to_optim_phase_err " (not a record)"
             end.

        Definition json_to_optim_config_of_language (l:language) :
          list json -> string + optim_config_of_language l
          := match l return list json -> string + optim_config_of_language l with
             | L_nnrs_imp =>
               lift_err_map json_to_optim_phase3_config
             | _ =>
               lift_err_map json_to_optim_phase_config
             end.    

        Let json_to_optim_elem_err {A:Type} (s:string) : string + A
          := inl (append "Ill-formed optim configuration" s).

        Definition json_to_optim_config_elem (d:json) :
          string + ({l:language & optim_config_of_language l})
          := match d with
             | jobject rec =>
               match lookup string_dec rec "language" with
               | None => json_to_optim_elem_err " (missing language)"
               | Some (jstring name) =>
                 let language := language_of_name_case_sensitive name in
                 match language with
                 | L_error s => json_to_optim_elem_err (append " (language is not a valid language name: " (append s ")"))
                 | _ => match lookup string_dec rec "phases" with
                        | None => json_to_optim_elem_err " (missing phases)"
                        | Some (jarray phases) =>
                          lift_err (fun p => existT _ language p)
                                   (json_to_optim_config_of_language language phases)
                        | Some _ => json_to_optim_elem_err " (phases is not a list)"
                        end
                 end
                 | Some _ => json_to_optim_elem_err " (language is not a string)"
                 end
               | _ => json_to_optim_elem_err " (not a record) "
               end.

        Definition json_to_optim_config (d:json) : string + optim_config
          := match d with
             | jarray l => lift_err_map json_to_optim_config_elem l
             | _ => inl "Ill-formed optim configuration (not a list)"
             end.

        End from_json.

        Section roundtrip_json.
          Context (float_roundtrip : forall n:Z, float_truncate (float_of_int n) = n).

        Lemma unjstringlist_jstring {E} (e:E+string) (l:list string) :
          unjstringlist e (map jstring l) = inr l.
        Proof.
          unfold unjstringlist.
          rewrite lift_err_map_map, lift_err_map_eta, lift_err_map_inr
          ; trivial.
        Qed.
                           
        Lemma optim_phase_config_to_json_to_optim_phase_config
              (config:optim_phase_config) :
          json_to_optim_phase_config (optim_phase_config_to_json config) = inr config.
        Proof.
          destruct config as [[??]?]; simpl.
          rewrite unjstringlist_jstring.
          repeat rewrite float_roundtrip.
          rewrite Nat2Z.id.
          match_case; intros.
          omega.
        Qed.

        Lemma optim_phase3_config_to_json_to_optim_phase3_config
              (config:optim_phase3_config) :
          json_to_optim_phase3_config (optim_phase3_config_to_json config) = inr config.
        Proof.
          destruct config as [[[[??]?]?]?]; simpl.
          repeat rewrite unjstringlist_jstring.
          repeat rewrite float_roundtrip.
          rewrite Nat2Z.id.
          match_case; intros.
          omega.
        Qed.

        Lemma optim_config_of_language_to_json_to_optim_config_of_language
              {l:language} (d:optim_config_of_language l) :
          json_to_optim_config_of_language l (optim_config_of_language_to_json d) = inr d.
        Proof.
          destruct l; simpl
          ;  try solve[rewrite lift_err_map_map; simpl
          ; rewrite (lift_err_map_ext _ inr)
          ; [ apply lift_err_map_inr
            | intros
              ; try rewrite optim_phase_config_to_json_to_optim_phase_config
              ; try rewrite optim_phase3_config_to_json_to_optim_phase3_config
              ; trivial]].
        Qed.

        Lemma optim_config_elem_to_json_to_optim_config_elem
              (oc:{l:language & optim_config_of_language l}) :
          no_L_error (projT1 oc) ->
          json_to_optim_config_elem (optim_config_elem_to_json oc) = inr oc.
        Proof.
          destruct oc; simpl; intros noerr.
          rewrite language_of_name_of_language by trivial.
          rewrite optim_config_of_language_to_json_to_optim_config_of_language
          ; simpl.
          destruct x; simpl in noerr; try contradiction
          ; reflexivity.
        Qed.

        Lemma optim_config_to_json_to_optim_config
              (oc:optim_config) :
          Forall (fun oce => no_L_error (projT1 oce)) oc ->
          json_to_optim_config (optim_config_to_json oc) = inr oc.
        Proof.
          intros ne.
          simpl.
          rewrite lift_err_map_map.
          rewrite (lift_err_map_ext _ inr)
          ; [ apply lift_err_map_inr | ].
          intros ? inn.
          apply optim_config_elem_to_json_to_optim_config_elem.
          rewrite Forall_forall in ne.
          eauto.
        Qed.
          
        End roundtrip_json.

    End serialization.
    
  End optim.

  Section constants.
    (* Each global variable has a localization and a local type *)
    Record constant_config :=
      mkConstantConfig { constant_localization : dlocalization;
                         constant_type : rtype;
                         constant_source : option string }.

    Definition constants_config := list (string * constant_config).

    Definition vars_of_constants_config (cconf:constants_config) :=
      map fst cconf.

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

    Lemma vars_of_one_constant_config_of_avoid_list l:
      vars_of_constants_config (one_constant_config_of_avoid_list l)
      = l.
    Proof.
      unfold one_constant_config_of_avoid_list.
      induction l; simpl.
      - reflexivity.
      - rewrite IHl.
        reflexivity.
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
