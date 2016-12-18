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

Section CldMR.
  Require Import String.
  Require Import List.
  Require Import Sorting.Mergesort.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import NNRCRuntime NNRCMRRuntime.
  Require Import CldMRUtil ForeignCloudant.
  
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {fcloudant:foreign_cloudant}.

  Context (h:list(string*string)).

  (** This provides support for the specific kind of quote
      "map/reduce" unquote that Cloudant actually provides.

      In many ways, Cloudant's notion of 'views', despite being called
      a map/reduce and providing some of the capabilities that are
      available in more common M/R framework such as Hadoop, is quite
      a different beast. Those differences are not entirely arbitrary,
      and the framework is at once less expressive than M/R and also
      more powerful and offers the following capabilities:

      - Cloudant M/R can be chained through a special directive called
        dbcopy which creates a new database that can be the input to a
        subsequent Cloudant M/R view.

      - Cloudant M/R can be executed in an incremental fashion, i.e.,
        changes on the input are propagated with limited recomputation
        and exploiting results from previous executions which are
        cached.

      To achieve that, Cloudant's M/R relies on a number of
      invariants, which we here try and expse and enforce. The most
      important such invariants are:

      - dbcopy can only be present if a reduce is present as well

      - the result of a dbcopy directive is implicitely cast into as
        collection of JSON documents in the form of key/value pairs,
        which are used to populate the newly created database/view.

      - A subsequent map over that dbcopy must access data accordingly
        (in such key/values JSON structure).

      - The "reduce" part of Cloudant M/R is heavily constrained and
        must provide two distinct functions: one called reduce, the
        other called rereduce. The rereduce function must be
        associative and commutative.

 *)
  
  (** Named Nested Relational Calculus + Map Reduce FOR CLOUDANT *)

  (* Cloudant maps are describes using two structures:

       - a map function which can be either a map or a flat_map

       - an emit function which can be either:
          -- 'dist' which is enforcing unique id's on a distributed collection
          -- 'collect' which is enforcing accumulation to a single key.

      Note that as opposed to the NNRCMR form, the collect is specified
      in the map, since it has to be obtained with an emit.

   *)
  
  (* Java equivalent: CldMapFun *)
  Inductive cld_map_fun :=
  | CldMapId : var * nnrc -> cld_map_fun           (* A -> B *)
  | CldMapFlatten : var * nnrc -> cld_map_fun.     (* A -> coll B *)

  (* Java equivalent: CldMapEmit *)
  Inductive cld_map_emit :=
  | CldEmitDist : cld_map_emit
  | CldEmitCollect : nat -> cld_map_emit.
  
  (* Java equivalent: CldMap *)
  Record cld_map :=
    mkMapCld
      { map_fun: cld_map_fun;
        map_emit: cld_map_emit }.

  Inductive cld_numeric_type :=
  | Cld_int
  | Cld_float.

  Global Instance cld_numeric_type_eqdec : EqDec cld_numeric_type eq.
  Proof.
    red. unfold equiv, complement.
    change (forall x y : cld_numeric_type, {x = y} + {x <> y}).
    decide equality.
  Defined.
  
  Inductive cld_reduce_op :=
  | CldRedOpCount : cld_reduce_op
  | CldRedOpSum (typ:cld_numeric_type): cld_reduce_op
  | CldRedOpStats (typ:cld_numeric_type): cld_reduce_op.

  (* Java equivalent: CldReduceFun *)
  Inductive cld_reduce_fun :=
  | CldRedId : cld_reduce_fun
  | CldRedAggregate : ((var * var) * nnrc) -> (var * nnrc) -> cld_reduce_fun
  | CldRedOp : cld_reduce_op -> cld_reduce_fun.
      (* first function : ((K * list B) -> C) function that computes the first reduce pass
         second function : (list C) -> C) function that computes the subsequent reduceereduce passes *)

  (* Java equivalent: CldReduce *)
  Record cld_reduce :=
    mkReduceCld
      { reduce_fun: cld_reduce_fun;
        reduce_output : option var (* where to put the result -- corresponds to dbcopy *) }.

  (* Java equivalent: CldMr *)
  Record cld_mr :=
    mkMRCld
      { cld_mr_input: var;               (* Input Cloudant Database *)
        cld_mr_map: cld_map;             (* Cloudant Map *)
        cld_mr_reduce: option cld_reduce; (* Cloudant Reduce *)
        cld_mr_reduce_default: option nnrc }.

  (* Java equivalent: CldMrl *)
  Record cld_mrl :=
    mkMRCldChain
      { cld_mr_chain: list cld_mr;
        cld_mr_last: ((list var) * nnrc) * (list var) }.
  (* Temporarily : localization should always be scalar *)

  (********************************
   ** Well formation constraints **
   ********************************)

  Definition cld_mr_causally_consistent (mr1 mr2:cld_mr) : bool
    := match mr2.(cld_mr_reduce) with
       | Some r =>
         match r.(reduce_output) with
         | Some o => mr1.(cld_mr_input) <>b o
         | None => true
         end
       | None => true
       end.

  Definition cld_mr_chain_causally_consistent : list cld_mr -> bool
    := forallb_ordpairs_refl cld_mr_causally_consistent.

  Definition cld_mrl_causally_consistent (cld_mrl: cld_mrl) : bool
    := cld_mr_chain_causally_consistent cld_mrl.(cld_mr_chain).

  Definition cld_mr_io_vars mr0 : list var
    := mr0.(cld_mr_input)::
      match mr0.(cld_mr_reduce) with
       | Some r =>
         match r.(reduce_output) with
         | Some o => o::nil
         | None => nil
         end
       | None => nil
      end.

  Definition mr_chain_io_vars (l : list mr) : list var
    := map mr_input l ++ map mr_output l.

  Definition nnrcmr_io_vars (mrl : nnrcmr) : list var
    := mr_chain_io_vars mrl.(mr_chain).

  Definition cld_mr_chain_io_vars : list cld_mr -> list var
    := flat_map cld_mr_io_vars.

  Definition cld_mrl_io_vars (cld_mrl:cld_mrl): list var
    := cld_mr_chain_io_vars cld_mrl.(cld_mr_chain).

  (* XXX Those have to be revised... *)
  
  Definition function_with_no_free_vars (f: var * nnrc) :=
    (forall (x: var), In x (nnrc_free_vars (snd f)) -> x = fst f).
  Definition function2_with_no_free_vars (f: (var * var) * nnrc) :=
    (fst (fst f)) <> (snd (fst f)) /\
    (forall x, In x (nnrc_free_vars (snd f)) -> x = (fst (fst f)) \/ x = (snd (fst f))).

  Definition init_vkey := "vkey$"%string.
  Definition init_vval := "vval$"%string.


  (*********************************
   ** Semantics of ♥ CloudantMR ♥ **
   *********************************)

  Definition add_keys_to_binding (binding: string * (list data)) : string * data :=
    (fst binding, pack_kvl (init_keys (snd binding))).

  Definition lift_binding_to_coll (binding: string * data) : option (string * (list data)) :=
    match snd binding with
    | dcoll coll => Some (fst binding, coll)
    | _ => None
    end.

  Definition cld_load_init_env
             (initunit: var) (cenv: list (string * data)) : option bindings
    :=
      match lift_map lift_binding_to_coll cenv with
      | Some cenv =>
        let full_bindings := (initunit, (dunit::nil)) :: cenv in
        Some (map add_keys_to_binding full_bindings)
      | None => None
      end.

  (********************
   * Semantics of map *
   ********************)

  Definition apply_map_fun_with_keys (doc:var) (body:nnrc) :
    list (data * data) -> option (list (data * data)) :=
    fun coll =>
      let f_map (d:data*data) :=
          let '(k, v) := d in
          match nnrc_core_eval h ((doc,v)::nil) body with
          | None => None
          | Some res => Some (k, res)
          end
      in rmap f_map coll.
  
  Definition apply_map_fun_without_keys (doc:var) (body:nnrc) :
    list (data * data) -> option (list data) :=
    fun coll =>
      let f_map (d:data*data) :=
          let (_, v) := d in
          match nnrc_core_eval h ((doc,v)::nil) body with
          | None => None
          | Some res => Some res
          end
      in rmap f_map coll.

  (* Note: CldMapFlatten allows multiple emits ... *)
  Definition cld_mr_map_eval (map: cld_map) (coll: list (data * data)) : option (list (data * data)) :=
    let map_f := map.(map_fun) in
    let emit_f := map.(map_emit) in
    match map_f with
    | CldMapId (doc, body) =>
      match emit_f with
      (* Just map and preserves input keys *)
      | CldEmitDist =>
        let nested_map := apply_map_fun_with_keys doc body coll in
        nested_map
      (* Just map and re-indexes with constant key *)
      | CldEmitCollect n =>
        let nested_map := apply_map_fun_without_keys doc body coll in
        olift (map_without_key (map_const_key n)) nested_map
      end
    | CldMapFlatten (doc, body) =>
      match emit_f with
      (* Flattens and invents new keys prefixed by the input keys *)
      | CldEmitDist =>
        let nested_map := apply_map_fun_with_keys doc body coll in
        olift (flat_map_with_key map_invent_key) nested_map
      (* Flattens and indexes with constant key *)
      | CldEmitCollect n =>
        let nested_map := apply_map_fun_without_keys doc body coll in
        let flattened_map := olift flat_map_without_key nested_map in
        olift (map_without_key (map_const_key n)) flattened_map
      end
    end.

  Lemma mapIdDist_is_map (map:var*nnrc) (coll:list data) :
    lift cld_get_values (cld_mr_map_eval (mkMapCld (CldMapId map) (CldEmitDist)) (init_keys coll)) = (mr_map_eval h (MapDist map) (Ddistr coll)).
  Proof.
    unfold cld_mr_map_eval; simpl.
    unfold init_keys; generalize 0.
    induction coll; intros; simpl in *.
    - destruct map; reflexivity.
    - destruct map; simpl.
      unfold apply_map_fun_with_keys in *; simpl.
      destruct (nnrc_core_eval h ((v, a) :: nil) n0); try reflexivity; simpl.
      rewrite <- (IHcoll (S n)); simpl; clear IHcoll.
      destruct (init_keys_aux nil (S n) coll); try reflexivity; simpl.
      destruct p; simpl.
      destruct (nnrc_core_eval h ((v, d1) :: nil) n0); try reflexivity; simpl.
      generalize ((lift (fun t' : list (data * data) => (d0, d2) :: t')
           (rmap
              (fun d3 : data * data =>
               let (k, v0) := d3 in
               match nnrc_core_eval h ((v, v0) :: nil) n0 with
               | Some res => Some (k, res)
               | None => None
               end) l))); intros.
      unfold box_key; simpl.
      unfold cld_get_values; simpl.
      destruct o; reflexivity.
  Qed.

  Lemma lift_map_boxed_cons n d coll:
    (lift (fun kvs : list (data * data) => map snd kvs)
          (lift (fun t' : list (data * data) => (box_key (n :: nil), d) :: t') coll))
    = lift (cons d) (lift (fun kvs : list (data * data) => map snd kvs) coll).
  Proof.
    destruct coll; reflexivity.
  Qed.

  Lemma mapIdCollect_is_map (map:var*nnrc) (n:nat) (coll:list data) :
    lift cld_get_values (cld_mr_map_eval (mkMapCld (CldMapId map) (CldEmitCollect n)) (init_keys coll)) = (mr_map_eval h (MapDist map) (Ddistr coll)).
  Proof.
    unfold cld_mr_map_eval; simpl.
    unfold init_keys; generalize 0.
    induction coll; intros; simpl in *.
    - destruct map; reflexivity.
    - destruct map; simpl.
      unfold apply_map_fun_without_keys in *; simpl.
      destruct (nnrc_core_eval h ((v, a) :: nil) n1); try reflexivity; simpl.
      rewrite <- (IHcoll (S n0)); simpl; clear IHcoll.
      destruct (init_keys_aux nil (S n0) coll); try reflexivity; simpl.
      destruct p; simpl.
      destruct (nnrc_core_eval h ((v, d1) :: nil) n1); try reflexivity; simpl.
      generalize ((lift (fun t' : list data => d2 :: t')
           (rmap
              (fun d3 : data * data =>
               let (_, v0) := d3 in
               match nnrc_core_eval h ((v, v0) :: nil) n1 with
               | Some res => Some res
               | None => None
               end) l))); intros.
      unfold cld_get_values; simpl.
      destruct o; try reflexivity; simpl.
      unfold rmap_index; simpl.
      rewrite lift_map_boxed_cons; simpl.
      unfold map_without_key; simpl.
      unfold rmap_index in *; simpl in *.
      admit.
  Admitted.


  (*************************
   * Semantics of group_by *
   *************************)

  Definition cld_mr_group_by_eval (l: list (data * data)) : list (data * (list data)) :=
    group_by_iter_eval_alt l.


  (***********************
   * Semantics of reduce *
   ***********************)

  Definition cld_mr_aggregate_eval (f_reduce: (var * var) * nnrc) (f_rereduce: (var * nnrc)) (groups: list (data * (list data)))  : option (list (data * data)) :=
    let (key_values_args, body) := f_reduce in
    let (key_arg, values_arg) := key_values_args in
    let f_reduce (key_values_v: data * list data) : option (data * data) :=
        let (key_v, values_v) := key_values_v in
        match nnrc_core_eval h ((values_arg, dcoll values_v) :: (key_arg, key_v) :: nil) body with
          None => None
        | Some res => Some (key_v, res)
        end
    in
    let reduced := rmap f_reduce groups in
    let f_rereduce (key_value_v: (data * data)) : option (data * data) :=
        let '(key_v, value_v) := key_value_v in
        let '(values_arg, rebody) := f_rereduce in
        match nnrc_core_eval h ((values_arg, dcoll (value_v::nil)) :: nil) rebody with
        | None => None
        | Some res => Some (key_v, res)
        end
    in
    olift (rmap f_rereduce) reduced.

  Definition cloudant_sum_op (typ:cld_numeric_type)
    := match typ with
       | Cld_int => ASum
       | Cld_float => cloudant_float_sum_op
       end.

    Definition cloudant_min_op (typ:cld_numeric_type)
    := match typ with
       | Cld_int => ANumMin
       | Cld_float => cloudant_float_min_op
       end.

    Definition cloudant_max_op (typ:cld_numeric_type)
    := match typ with
       | Cld_int => ANumMax
       | Cld_float => cloudant_float_max_op
       end.
  
  Definition cld_mr_reduce_eval (red_fun: cld_reduce_fun) (coll: list (data * data))  : option (list (data * data)) :=
    match red_fun with
    | CldRedId => Some coll
    | CldRedAggregate f_reduce f_rereduce =>
      let groups := cld_mr_group_by_eval coll in
      cld_mr_aggregate_eval f_reduce f_rereduce groups
    | CldRedOp CldRedOpCount =>
      let uop := ACount in
      let v := fun_of_unaryop h uop (dcoll (List.map snd coll)) in
      let key := dcoll (dnat 0::nil) in (* XXX Question for Jerome: what to do? XXX *)
      lift (fun res => (key, res)::nil) v
    | CldRedOp (CldRedOpSum typ) =>
      let uop := cloudant_sum_op typ in
      let v := fun_of_unaryop h uop (dcoll (List.map snd coll)) in
      let key := dcoll (dnat 0::nil) in (* XXX Question for Jerome: what to do? XXX *)
      lift (fun res => (key, res)::nil) v
    | CldRedOp (CldRedOpStats typ) =>
      let coll := dcoll (List.map snd coll) in
      let count := fun_of_unaryop h ACount coll in
      let sum := fun_of_unaryop h (cloudant_sum_op typ) coll in
      let min := fun_of_unaryop h (cloudant_min_op typ) coll in
      let max := fun_of_unaryop h (cloudant_max_op typ) coll in
      let v :=
          match (count, sum, min, max) with
          | (Some count, Some sum, Some min, Some max) =>
            Some (drec (("count"%string, count)
                          ::("max"%string, max)
                          ::("min"%string, min)
                          ::("sum"%string, sum)
                          ::nil))
          | _ => None
          end
      in
      let key := dcoll (dnat 0::nil) in (* XXX Question for Jerome: what to do? XXX *)
      lift (fun res => (key, res)::nil) v
    end.

  Lemma cld_mr_reduce_flatten_id (l:list (data * data)) :
    (cld_mr_reduce_eval CldRedId l) = Some l.
  Proof.
    reflexivity.
  Qed.


  (*******************************
   * Semantics of one map-reduce *
   *******************************)

  Definition cld_mr_eval (mr:cld_mr) (coll: list (data * data)) : option ((list (data*data)) * option var) :=
    let map_result :=
        cld_mr_map_eval mr.(cld_mr_map) coll
    in
    match mr.(cld_mr_reduce) with
    | None => lift (fun x => (x,None)) map_result
    | Some reduce =>
      let reduce_result := olift (cld_mr_reduce_eval reduce.(reduce_fun)) map_result in
      lift (fun x => (x, reduce.(reduce_output))) reduce_result
    end.

  
  
  (**************************************
   * Semantics of a chain of map-reduce *
   **************************************)

  Definition cld_merge_env (x: var) (coll: list data) (env: bindings) : option bindings :=
    match lookup equiv_dec env x with
    | None => Some ((x, dcoll coll)::env)
    | Some d =>
      match d with
      | dcoll coll' => Some ((x, dcoll (coll ++ coll') )::env)
      | _ => None
      end
    end.
  
  Definition nnrc_env_of_cld_env (form:list var) (eff: option (list data)): option bindings :=
    olift (zip form) eff. 

  Definition effective_params_from_bindings (eff:list var) (cld_env:bindings) : option (list data) :=
    lift_map
      (fun (v : var) =>
         match lookup equiv_dec cld_env v with
         | None => None
         | Some db =>
           lift (fun l => dcoll (List.map snd l)) (unpack_kvl db)
         end)
      eff.
  
  Definition cld_mr_eval_last (cld_env:bindings) (mr_last: ((list var) * nnrc) * (list var)) : option data :=
    let (formal_params, n) := fst mr_last in
    let effective_params := effective_params_from_bindings (snd mr_last) cld_env in
    let onrc_env := nnrc_env_of_cld_env formal_params effective_params in
    olift (fun nnrc_env => nnrc_core_eval h nnrc_env n) onrc_env.

  Definition cld_mr_chain_eval_inner (env:bindings) (l:list cld_mr) : option (bindings * list (data * data)) :=
    List.fold_left
      (fun (acc: option (bindings * list (data * data))) mr =>
         match acc with
         | None => None
         | Some (env', _) =>
           let cld_input := mr.(cld_mr_input) in
           match lookup equiv_dec env' cld_input with
           | None => None
           | Some kvl =>
             let coll := unpack_kvl kvl in
             match olift (cld_mr_eval mr) coll with
             | None => None
             | Some (res,None) => Some (env, res)
             | Some (res,Some x) =>
               let env'' := cld_merge_env x (pre_pack_kvl res) env' in
               olift (fun env => Some (env, res)) env''
             end
           end
         end)
      l (Some (env,nil)).

  Definition cld_mrl_eval (env:bindings) (cld_mrl:cld_mrl) : option data :=
    match cld_mr_chain_eval_inner env cld_mrl.(cld_mr_chain) with
    | None => None
    | Some (env_res, coll) =>
      cld_mr_eval_last env_res cld_mrl.(cld_mr_last)
    end.


  (*******************
   ** CLDMR library **
   *******************)

  Section cld_mr_library.
    
    (* Java equivalent: NrcmrToCldmr.idReduce *)
    Definition idReduce (v_out:option var) : cld_reduce := 
      mkReduceCld CldRedId v_out.

    (* Java equivalent: NrcmrToCldmr.collectReduce *)
    Definition collectReduce (v_out:option var) : cld_reduce :=
      mkReduceCld (CldRedAggregate (init_vkey, init_vval, NNRCVar init_vval)
                                   (init_vval, NNRCUnop AFlatten (NNRCVar init_vval))) v_out.

    (* Java equivalent: NrcmrToCldmr.opReduce *)
    Definition opReduce (op: cld_reduce_op) (v_out:option var) : cld_reduce :=
      mkReduceCld (CldRedOp op) v_out.

    Definition defaultMR : cld_mr :=
      mkMRCld init_vval (mkMapCld (CldMapId (init_vval, NNRCConst dunit)) (CldEmitCollect (99%nat))) None None (*empty default*).
    
  End cld_mr_library.

  
  Section sanitize.
    Require Import Ascii String List.
    Import ListNotations.
    Definition cldAllowedIdentifierInitialCharacters :=
      ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]%char.

    (* according to https://docs.cloudant.com/database.html,
       this cldAllowedIdentifierCharacters_fromdocs work.  
       But $ at least has been reported as causing problems with the UI.
       So we conservatively use cldAllowedIdentifierCharacters instead.
*)
    Definition cldAllowedIdentifierCharacters_fromdocs := ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_";"$";",";"+";"-";"/"]%char.
    
    Definition cldAllowedIdentifierCharacters := ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_"]%char.

    Definition cldIdentifierInitialCharacterToAdd := "z"%char.
    Definition cldIdenitiferCharacterForReplacement := "z"%char.

	(* Java equivalent: MROptimizer.cldIdentifierFixInitial *)
    Definition cldIdentifierFixInitial (ident:string) : string
    := match ident with
       (* We also don't want empty identifier names *)
       | EmptyString =>
         String cldIdentifierInitialCharacterToAdd EmptyString
       | String a _ =>
         if in_dec ascii_dec a cldAllowedIdentifierInitialCharacters
         then ident
         else String cldIdentifierInitialCharacterToAdd ident
       end.

    (* Java equivalent: MROptimizer.cldIdentifierSanitizeChar *)
    Definition cldIdentifierSanitizeChar (a:ascii)
      := if a == "$"%char (* special case for readability *)
         then "_"%char
         else if in_dec ascii_dec a cldAllowedIdentifierCharacters
              then a
              else cldIdenitiferCharacterForReplacement.

  (* Java equivalent: MROptimizer.cldIdentifierSanitizeBody *)
  Definition cldIdentifierSanitizeBody (ident:string)
    := map_string cldIdentifierSanitizeChar ident.
  
  (* Java equivalent MROptimizer.cldIdentifierSanitize *)
  Definition cldIdentifierSanitize (ident:string)
    := cldIdentifierFixInitial (cldIdentifierSanitizeBody (mk_lower ident)).
  
  (* Java equivalent (used in): MROptimizer.nrcmr_rename_graph_for_cloudant *)
  Definition cldSafeSeparator := "_"%string.

  (* Java equivalent (used in): MROptimizer.nrcmr_rename_graph_for_cloudant *)
  Definition cldAvoidList : list string := [].

  End sanitize.
End CldMR.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
