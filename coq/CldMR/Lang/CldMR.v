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

(** CldMR is a language to describe chains of Map/Reduce views in the
Cloudant Database, followed by some local computation over the result
of the views. *)

(** Cloudant's notion of 'views' provides some of the capabilities
    that are available in more common Map/Reduce framework such as Hadoop,
    but has a number of different properties. *)

(** Cloudant notion of views is less expressive than general purpose
    Map/Reduce but offers the following additional capabilities:
- Cloudant views can be chained through a special directive called
  dbcopy which creates a new database that can be the input to a
  subsequent Cloudant view.
- Cloudant views are computed in an incremental fashion, i.e., changes
  on the input are propagated with limited recomputation and
  exploiting results from previous executions which are cached. *)

(** To achieve that, Cloudant views relies on a number of invariants,
    which we expose and try to enforce. The most important invariants
    are:
- A [dbcopy] can only be present if a reduce is present as well.
- the result of a [dbcopy] directive is implicitely coerced into a a
  database in the form of key/value pairs, which are used to populate
  the newly created database/view.
- A subsequent map over that dbcopy must access data accordingly (in
  such key/values JSON structure).
- The "reduce" part of Cloudant views is heavily constrained and must
  provide two distinct functions: one called [reduce], the other
  called [rereduce]. The [rereduce] function must be associative and
  commutative.  *)

(** Finally, Cloudant views support special purposes reducers for the
most common aggregate functions (count, sum, and average). We provide
a representation to take advantage of those. *)

(** Summary:
- Language: CldMR (Cloudant Map/Reduce)
- Based on: Cloudant DB documentation.
- URL: https://console.ng.bluemix.net/docs/services/Cloudant/api/creating_views.html#views-mapreduce-
- Languages translating to CldMR: NNRCMR
- Languages translating from CldMR: Cloudant
*)

Require Import String.
Require Import List.
Require Import Sorting.Mergesort.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRCRuntime.
Require Import NNRCMRRuntime.
Require Import CldMRUtil.
Require Import ForeignCloudant.
  
Section CldMR.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {fcloudant:foreign_cloudant}.

  Context (h:list(string*string)).

  (** * Abstract Syntax *)

  (** As in NNRCMR, all local computation inside the map or the reduce
  in CldMR is described using NNRC expressions. *)
  
  (** ** Map *)
  
  (** The [map] part of a Cloudant view is described using two
  components:
- a map function which can be either a map or a flat_map, which is
  applied to every document in the input database.
- an emit function which controls the generation of keys passed to the
  reduce. The emit function is either: (i) [dist] which creates unique
  id's for the result of the map and results in a distributed
  collection, (ii) [collect] which is enforcing accumulation to a
  single output document with a single key. *)

  (** Note that as opposed to NNRCMR, the collect is specified in the
  map rather than the reduce, since it has to be controlled through an
  emit. *)
  
  (** Also note that this model does not cover a group-by semantics
  but only simpler forms of reduce. *)
  
  (* Java equivalent: CldMapFun *)
  Inductive cld_map_fun :=
  | CldMapId : var * nnrc -> cld_map_fun           (**r [A -> B] *)
  | CldMapFlatten : var * nnrc -> cld_map_fun.     (**r [A -> coll B] *)

  (* Java equivalent: CldMapEmit *)
  Inductive cld_map_emit :=
  | CldEmitDist : cld_map_emit                     (**r Emit one key per input document *)
  | CldEmitCollect : nat -> cld_map_emit.          (**r Emit a single key for all documents *)
  
  (* Java equivalent: CldMap *)
  Record cld_map :=
    mkMapCld
      { map_fun: cld_map_fun;
        map_emit: cld_map_emit }.

  (** ** Reduce *)
  
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
  | CldRedOpCount : cld_reduce_op                          (**r Special reducer: [_count] *)
  | CldRedOpSum (typ:cld_numeric_type): cld_reduce_op      (**r Special reducer: [_sum] *)
  | CldRedOpStats (typ:cld_numeric_type): cld_reduce_op.   (**r Special reducer: [_stat] *)

  (* Java equivalent: CldReduceFun *)
  Inductive cld_reduce_fun :=
  | CldRedId : cld_reduce_fun                                 (**r Reduce is identity *)
  | CldRedAggregate :                                         (**r Arbitrary reduce + rereduce *)
      ((var * var) * nnrc) -> (var * nnrc) -> cld_reduce_fun
  | CldRedOp : cld_reduce_op -> cld_reduce_fun.               (**r Special reducer *)

  (** In the case of the arbirary reduce operation: the first function
      is the [reduce] and applied once on each key/value pair
      resulting from the map [(K * list B) -> C]; the second function
      is the [rereduce] and applied on the result of the first
      function [(list C) -> C]. *)

  (* Java equivalent: CldReduce *)
  Record cld_reduce :=
    mkReduceCld
      { reduce_fun: cld_reduce_fun;   (**r reduce function *)
        reduce_output : option var }. (**r Output database [dbcopy] *)

  (** ** Map/Reduce View *)
  
  (* Java equivalent: CldMr *)
  Record cldmr_step :=
    mkMRCld
      { cldmr_step_input: var;                    (**r Input database *)
        cldmr_step_map: cld_map;                  (**r Map *)
        cldmr_step_reduce: option cld_reduce;     (**r Reduce *)
        cldmr_step_reduce_default: option nnrc }. (**r Default when database is empty *)

  (** ** Map/Reduce Chains *)

  (** The top-level data structure includes a list of Map/Reduce
  views, followed by an additional expressions which is used to gather
  all the results from the views and compute the final results. This
  is meant to be evaluated locally. *)
  
  (* Java equivalent: CldMrl *)
  Record cldmr :=
    mkMRCldChain
      { cldmr_chain: list cldmr_step;
        cldmr_last: ((list var) * nnrc) * (list var) }.


  (********************************
   ** Well formation constraints **
   ********************************)

  (** * Well-formed properties *)
  
  Definition cldmr_step_causally_consistent (mr1 mr2:cldmr_step) : bool
    := match mr2.(cldmr_step_reduce) with
       | Some r =>
         match r.(reduce_output) with
         | Some o => mr1.(cldmr_step_input) <>b o
         | None => true
         end
       | None => true
       end.

  Definition cldmr_chain_causally_consistent : list cldmr_step -> bool
    := forallb_ordpairs_refl cldmr_step_causally_consistent.

  Definition cldmr_causally_consistent (cldmr: cldmr) : bool
    := cldmr_chain_causally_consistent cldmr.(cldmr_chain).

  Definition cldmr_step_io_vars mr0 : list var
    := mr0.(cldmr_step_input)::
      match mr0.(cldmr_step_reduce) with
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

  Definition cldmr_chain_io_vars : list cldmr_step -> list var
    := flat_map cldmr_step_io_vars.

  Definition cldmr_io_vars (cldmr:cldmr): list var
    := cldmr_chain_io_vars cldmr.(cldmr_chain).

  (* XXX Those have to be revised... *)
  
  Definition function_with_no_free_vars (f: var * nnrc) :=
    (forall (x: var), In x (nnrc_free_vars (snd f)) -> x = fst f).
  Definition function2_with_no_free_vars (f: (var * var) * nnrc) :=
    (fst (fst f)) <> (snd (fst f)) /\
    (forall x, In x (nnrc_free_vars (snd f)) -> x = (fst (fst f)) \/ x = (snd (fst f))).

  Definition init_vkey := "vkey$"%string.
  Definition init_vval := "vval$"%string.

  (** * Evaluation Semantics *)

  (*********************************
   ** Semantics of ♥ CloudantMR ♥ **
   *********************************)

  (** A few useful functions for key manipulation, lifting and
  building the initial CldMR environment. *)
  
  Definition add_keys_to_binding (binding: string * (list data)) : string * data :=
    (fst binding, pack_kvl (init_keys (snd binding))).

  Definition lift_binding_to_coll (binding: string * data) : option (string * (list data)) :=
    match snd binding with
    | dcoll coll => Some (fst binding, coll)
    | _ => None
    end.

  (** The evaluation relies on the existence of an initial database
  containing a single document with the unit value. This is necessary
  in order to trigger computation when all other input databases are
  empty. *)
  
  Definition cld_load_init_env
             (initunit: var) (cenv: list (string * data)) : option bindings
    :=
      match lift_map lift_binding_to_coll cenv with
      | Some cenv =>
        let full_bindings := (initunit, (dunit::nil)) :: cenv in
        Some (map add_keys_to_binding full_bindings)
      | None => None
      end.

  (** ** Map *)
  
  (********************
   * Semantics of map *
   ********************)

  Definition apply_map_fun_with_keys (doc:var) (body:nnrc) :
    list (data * data) -> option (list (data * data)) :=
    fun coll =>
      let f_map (d:data*data) :=
          let '(k, v) := d in
          match nnrc_core_eval h empty_cenv ((doc,v)::nil) body with
          | None => None
          | Some res => Some (k, res)
          end
      in lift_map f_map coll.
  
  Definition apply_map_fun_without_keys (doc:var) (body:nnrc) :
    list (data * data) -> option (list data) :=
    fun coll =>
      let f_map (d:data*data) :=
          let (_, v) := d in
          match nnrc_core_eval h empty_cenv ((doc,v)::nil) body with
          | None => None
          | Some res => Some res
          end
      in lift_map f_map coll.

  (* Note: CldMapFlatten allows multiple emits ... *)
  Definition cldmr_step_map_eval (map: cld_map) (coll: list (data * data)) : option (list (data * data)) :=
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
    lift cld_get_values (cldmr_step_map_eval (mkMapCld (CldMapId map) (CldEmitDist)) (init_keys coll)) = (mr_map_eval h (MapDist map) (Ddistr coll)).
  Proof.
    unfold cldmr_step_map_eval; simpl.
    unfold init_keys; generalize 0.
    induction coll; intros; simpl in *.
    - destruct map; reflexivity.
    - destruct map; simpl.
      unfold apply_map_fun_with_keys in *; simpl.
      destruct (nnrc_core_eval h empty_cenv ((v, a) :: nil) n0); try reflexivity; simpl.
      rewrite <- (IHcoll (S n)); simpl; clear IHcoll.
      destruct (init_keys_aux nil (S n) coll); try reflexivity; simpl.
      destruct p; simpl.
      destruct (nnrc_core_eval h empty_cenv ((v, d1) :: nil) n0); try reflexivity; simpl.
      generalize ((lift (fun t' : list (data * data) => (d0, d2) :: t')
           (lift_map
              (fun d3 : data * data =>
               let (k, v0) := d3 in
               match nnrc_core_eval h empty_cenv ((v, v0) :: nil) n0 with
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

  (* Should be revised -JS 
  Lemma mapIdCollect_is_map (map:var*nnrc) (n:nat) (coll:list data) :
    lift cld_get_values (cldmr_step_map_eval (mkMapCld (CldMapId map) (CldEmitCollect n)) (init_keys coll)) = (mr_map_eval h (MapDist map) (Ddistr coll)).
  Proof.
  *)

  (** ** Reduce *)
  
  (*************************
   * Semantics of group_by *
   *************************)

  Definition cldmr_step_group_by_eval (l: list (data * data)) : list (data * (list data)) :=
    group_by_iter_eval_alt l.


  (***********************
   * Semantics of reduce *
   ***********************)

  Definition cldmr_step_aggregate_eval (f_reduce: (var * var) * nnrc) (f_rereduce: (var * nnrc)) (groups: list (data * (list data)))  : option (list (data * data)) :=
    let (key_values_args, body) := f_reduce in
    let (key_arg, values_arg) := key_values_args in
    let f_reduce (key_values_v: data * list data) : option (data * data) :=
        let (key_v, values_v) := key_values_v in
        match nnrc_core_eval h empty_cenv ((values_arg, dcoll values_v) :: (key_arg, key_v) :: nil) body with
          None => None
        | Some res => Some (key_v, res)
        end
    in
    let reduced := lift_map f_reduce groups in
    let f_rereduce (key_value_v: (data * data)) : option (data * data) :=
        let '(key_v, value_v) := key_value_v in
        let '(values_arg, rebody) := f_rereduce in
        match nnrc_core_eval h empty_cenv ((values_arg, dcoll (value_v::nil)) :: nil) rebody with
        | None => None
        | Some res => Some (key_v, res)
        end
    in
    olift (lift_map f_rereduce) reduced.

  Definition cloudant_sum_op (typ:cld_numeric_type)
    := match typ with
       | Cld_int => OpNatSum
       | Cld_float => cloudant_float_sum_op
       end.

    Definition cloudant_min_op (typ:cld_numeric_type)
    := match typ with
       | Cld_int => OpNatMin
       | Cld_float => cloudant_float_min_op
       end.

    Definition cloudant_max_op (typ:cld_numeric_type)
    := match typ with
       | Cld_int => OpNatMax
       | Cld_float => cloudant_float_max_op
       end.
  
  Definition cldmr_step_reduce_eval (red_fun: cld_reduce_fun) (coll: list (data * data))  : option (list (data * data)) :=
    match red_fun with
    | CldRedId => Some coll
    | CldRedAggregate f_reduce f_rereduce =>
      let groups := cldmr_step_group_by_eval coll in
      cldmr_step_aggregate_eval f_reduce f_rereduce groups
    | CldRedOp CldRedOpCount =>
      let uop := OpCount in
      let v := unary_op_eval h uop (dcoll (List.map snd coll)) in
      let key := dcoll (dnat 0::nil) in (* XXX Question for Jerome: what to do? XXX *)
      lift (fun res => (key, res)::nil) v
    | CldRedOp (CldRedOpSum typ) =>
      let uop := cloudant_sum_op typ in
      let v := unary_op_eval h uop (dcoll (List.map snd coll)) in
      let key := dcoll (dnat 0::nil) in (* XXX Question for Jerome: what to do? XXX *)
      lift (fun res => (key, res)::nil) v
    | CldRedOp (CldRedOpStats typ) =>
      let coll := dcoll (List.map snd coll) in
      let count := unary_op_eval h OpCount coll in
      let sum := unary_op_eval h (cloudant_sum_op typ) coll in
      let min := unary_op_eval h (cloudant_min_op typ) coll in
      let max := unary_op_eval h (cloudant_max_op typ) coll in
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

  Lemma cldmr_step_reduce_flatten_id (l:list (data * data)) :
    (cldmr_step_reduce_eval CldRedId l) = Some l.
  Proof.
    reflexivity.
  Qed.


  (** ** Map/Reduce View *)
  
  (*******************************
   * Semantics of one map-reduce *
   *******************************)

  Definition cldmr_step_eval (mr:cldmr_step) (coll: list (data * data)) : option ((list (data*data)) * option var) :=
    let map_result :=
        cldmr_step_map_eval mr.(cldmr_step_map) coll
    in
    match mr.(cldmr_step_reduce) with
    | None => lift (fun x => (x,None)) map_result
    | Some reduce =>
      let reduce_result := olift (cldmr_step_reduce_eval reduce.(reduce_fun)) map_result in
      lift (fun x => (x, reduce.(reduce_output))) reduce_result
    end.


  (** ** Map/Reduce Chain *)
  
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
  
  Definition cldmr_step_eval_last (cld_env:bindings) (mr_last: ((list var) * nnrc) * (list var)) : option data :=
    let (formal_params, n) := fst mr_last in
    let effective_params := effective_params_from_bindings (snd mr_last) cld_env in
    let onrc_env := nnrc_env_of_cld_env formal_params effective_params in
    olift (fun nnrc_env => nnrc_core_eval h empty_cenv nnrc_env n) onrc_env.

  Definition cldmr_chain_eval_inner (env:bindings) (l:list cldmr_step) : option (bindings * list (data * data)) :=
    List.fold_left
      (fun (acc: option (bindings * list (data * data))) mr =>
         match acc with
         | None => None
         | Some (env', _) =>
           let cld_input := mr.(cldmr_step_input) in
           match lookup equiv_dec env' cld_input with
           | None => None
           | Some kvl =>
             let coll := unpack_kvl kvl in
             match olift (cldmr_step_eval mr) coll with
             | None => None
             | Some (res,None) => Some (env, res)
             | Some (res,Some x) =>
               let env'' := cld_merge_env x (pre_pack_kvl res) env' in
               olift (fun env => Some (env, res)) env''
             end
           end
         end)
      l (Some (env,nil)).

  Definition cldmr_eval (env:bindings) (cldmr:cldmr) : option data :=
    match cldmr_chain_eval_inner env cldmr.(cldmr_chain) with
    | None => None
    | Some (env_res, coll) =>
      cldmr_step_eval_last env_res cldmr.(cldmr_last)
    end.


  (** * Map/Reduce Chain Library *)

  (** The following are built-in map/reduce which are useful for
  translations purposes. *)

  (*******************
   ** CLDMR library **
   *******************)

  Section cldmr_step_library.
    
    (* Java equivalent: NrcmrToCldmr.idReduce *)
    Definition idReduce (v_out:option var) : cld_reduce := 
      mkReduceCld CldRedId v_out.

    (* Java equivalent: NrcmrToCldmr.collectReduce *)
    Definition collectReduce (v_out:option var) : cld_reduce :=
      mkReduceCld (CldRedAggregate (init_vkey, init_vval, NNRCVar init_vval)
                                   (init_vval, NNRCUnop OpFlatten (NNRCVar init_vval))) v_out.

    (* Java equivalent: NrcmrToCldmr.opReduce *)
    Definition opReduce (op: cld_reduce_op) (v_out:option var) : cld_reduce :=
      mkReduceCld (CldRedOp op) v_out.

    Definition defaultMR : cldmr_step :=
      mkMRCld init_vval (mkMapCld (CldMapId (init_vval, NNRCConst dunit)) (CldEmitCollect (99%nat))) None None (*empty default*).
    
  End cldmr_step_library.

  (** * Toplevel *)

  (** Top-level evaluation is used externally by the Q*cert
  compiler. It is parameterized by a given database name for the
  'initial database'. It takes a CldMR chain and a global environment
  as input. *)

  Section Top.
    Definition cldmr_eval_top (vinit:var) (q:cldmr) (cenv:bindings) : option data :=
      let cenv := rec_sort cenv in
      match cld_load_init_env vinit cenv with
      | Some cenv => cldmr_eval cenv q
      | None => None
      end.

  End Top.
  
End CldMR.

