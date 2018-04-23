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

Require Import String.
Require Import List.
Require Import Sorting.Mergesort.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import ForeignReduceOps.
Require Import ForeignToReduceOps.
Require Import NNRCSystem.
Require Import NNRCMRSystem.
Require Import DNNRCSystem.
Require Import NNRCtoDNNRC.

Section NNRCMRtoDNNRC.
  Local Open Scope string_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {ftoredop:foreign_to_reduce_op}.

  Context (h:list(string*string)).

  Context {A plug_type:Set}.

  Definition map_res_id (mr_id: string) :=
    "mapRes_"++mr_id.

  (* Generates the DNNRC code corresponding to "(fun x => e1) e2" that is:
       let x = e2 in e1
   *)
  Definition gen_apply_fun (annot:A) (f: var * nnrc) (e2: @dnnrc_base _ A plug_type) : (@dnnrc_base _ A plug_type) :=
    let (x, e1) := f in
    DNNRCLet annot
            x e2
            (nnrc_to_dnnrc_base annot nil ((x, Vlocal)::nil) e1).

  (* Generates the DNNRC code corresponding to "(fun (x1, ..., xn) => e) (e1, ..., en)" that is:
       let x1 = e1 in
       ...
       let xn = en in
       e
   *)
  Fixpoint gen_apply_fun_n (annot:A) (f: list var * nnrc)  (eff: list (var * dlocalization)) : option (@dnnrc_base _ A plug_type) :=
    let (form, e) := f in
    match zip form eff with
    | Some l =>
      let form_loc :=
          List.map
            (fun t =>
               let '(x, (y, loc)) := t in
               (x, loc))
            l
      in
      Some
        (List.fold_right
           (fun t k =>
              let '(x, (y, loc)) := t in
              DNNRCLet annot
                      x (DNNRCVar annot y)
                      k)
           (nnrc_to_dnnrc_base annot form_loc nil e)
           l)
    | None => None
    end.


  Definition dnnrc_base_distr_of_mr_map (annot:A) (input: var) (mr_map: map_fun) : (@dnnrc_base _ A plug_type) :=
    match mr_map with
    | MapDist (x, n) =>
      DNNRCFor annot x (DNNRCVar annot input) (nnrc_to_dnnrc_base annot nil ((x, Vlocal)::nil) n)
    | MapDistFlatten (x, n) =>
      let res_map :=
          DNNRCFor annot x (DNNRCVar annot input) (nnrc_to_dnnrc_base annot nil ((x, Vlocal)::nil) n)
      in
      DNNRCUnop annot OpFlatten res_map
    | MapScalar (x, n) =>
      let distr_input := DNNRCDispatch annot (DNNRCVar annot input) in
      DNNRCFor annot x distr_input (nnrc_to_dnnrc_base annot nil ((x, Vlocal)::nil) n)
    end.

  Definition dnnrc_base_local_of_mr_map (annot:A) (input: var) (mr_map: map_fun) : (@dnnrc_base _ A plug_type) :=
    match mr_map with
    | MapDist (x, n) =>
      let res_map := DNNRCFor annot x (DNNRCVar annot input) (nnrc_to_dnnrc_base annot nil ((x, Vlocal)::nil) n) in
      DNNRCCollect annot res_map
    | MapDistFlatten (x, n) =>
      let res_map := DNNRCFor annot x (DNNRCVar annot input) (nnrc_to_dnnrc_base annot nil ((x, Vlocal)::nil) n) in
      DNNRCCollect annot (DNNRCUnop annot OpFlatten res_map)
    | MapScalar (x, n) =>
      DNNRCFor annot x (DNNRCVar annot input) (nnrc_to_dnnrc_base annot nil ((x, Vlocal)::nil) n)
    end.

  Definition dnnrc_base_of_mr (annot:A) (m:mr) : option (@dnnrc_base _ A plug_type) :=
    match (m.(mr_map), m.(mr_reduce)) with
    | (MapScalar (x, NNRCUnop OpBag n), RedSingleton) =>
      Some (gen_apply_fun annot (x, n) (DNNRCVar annot m.(mr_input)))
    | (_, RedSingleton) =>
      None
    | (map, RedId) =>
      Some (dnnrc_base_distr_of_mr_map annot (mr_input m) map)
    | (map, RedCollect red_fun) =>
      let map_expr := dnnrc_base_local_of_mr_map annot (mr_input m) map in
      Some (gen_apply_fun annot red_fun map_expr)
    | (map, RedOp op) =>
      match op with
      | RedOpForeign frop =>
        let map_expr := dnnrc_base_distr_of_mr_map annot (mr_input m) map in
        lift (fun op => DNNRCUnop annot op map_expr) (foreign_to_reduce_op_to_unary_op op)
      end
    end.

  Fixpoint dnnrc_base_of_mr_chain (annot: A) (outputs: list var) (l: list mr) (k: @dnnrc_base _ A plug_type) : option (@dnnrc_base _ A plug_type) :=
    match l with
    | nil => Some k
    | mr :: l =>
      match (dnnrc_base_of_mr annot mr, dnnrc_base_of_mr_chain annot (mr_output mr :: outputs) l k) with
      | (Some n, Some k) =>
        Some (DNNRCLet annot
                      (mr_output mr)
                      (if in_dec equiv_dec (mr_output mr) outputs then
                         DNNRCBinop annot OpBagUnion (DNNRCVar annot (mr_output mr)) n
                       else n)
                      k)
      | _ => None
      end
    end.

  Definition dnnrc_base_of_nnrcmr_top (annot: A) (l: nnrcmr) : option (@dnnrc_base _ A plug_type) :=
    let constants := map fst (mr_inputs_loc l) in
    let (last_fun, last_args) :=  mr_last l in
    let k := gen_apply_fun_n annot last_fun last_args in
    lift (dnnrc_base_subst_var_to_const constants)
         (olift (dnnrc_base_of_mr_chain annot nil (mr_chain l)) k).

End NNRCMRtoDNNRC.

