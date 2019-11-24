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
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCRuntime.
Require Import NNRCMRRuntime.
Require Import ForeignToReduceOps.

Local Open Scope list_scope.

Section NNRCMRtoNNRC.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {ftoredop:foreign_to_reduce_op}.

  Context (h:brand_relation_t).

  (* Generates the DNNRC code corresponding to "(fun x => e1) e2" that is:
       let x = e2 in e1
   *)
  Definition gen_apply_fun (f: var * nnrc) (e2: nnrc) : nnrc :=
    let (x, e1) := f in
    NNRCLet x e2
           e1.

  (* Generates the DNNRC code corresponding to "(fun (x1, ..., xn) => e) (e1, ..., en)" that is:
       let x1 = e1 in
       ...
       let xn = en in
       e
   *)
  Fixpoint gen_apply_fun_n (f: list var * nnrc)  (eff: list (var * dlocalization)) : option nnrc :=
    let (form, e) := f in
    lift (List.fold_right
            (fun t k =>
               let '(x, (y, loc)) := t in
               NNRCLet x (NNRCVar y)
                      k)
            e)
         (zip form eff).


  Definition nnrc_of_mr_map (input: var) (mr_map: map_fun) : nnrc :=
    match mr_map with
    | MapDist (x, n) =>
      NNRCFor x (NNRCVar input) n
    | MapDistFlatten (x, n) =>
      let res_map :=
          NNRCFor x (NNRCVar input) n
      in
      NNRCUnop OpFlatten res_map
    | MapScalar (x, n) =>
      NNRCFor x (NNRCVar input) n
    end.

  Definition nnrc_of_mr (m:mr) : option nnrc :=
    match (m.(mr_map), m.(mr_reduce)) with
    | (MapScalar (x, NNRCUnop OpBag n), RedSingleton) =>
      Some (gen_apply_fun (x, n) (NNRCVar m.(mr_input)))
    | (_, RedSingleton) =>
      None
    | (map, RedId) =>
      Some (nnrc_of_mr_map (mr_input m) map)
    | (map, RedCollect red_fun) =>
      let map_expr := nnrc_of_mr_map (mr_input m) map in
      Some (gen_apply_fun red_fun map_expr)
    | (map, RedOp op) =>
      match op with
      | RedOpForeign frop =>
        let map_expr := nnrc_of_mr_map (mr_input m) map in
        lift (fun op => NNRCUnop op map_expr) (foreign_to_reduce_op_to_unary_op op)
      end
    end.

  Fixpoint nnrc_of_mr_chain (outputs: list var) (l: list mr) (k: nnrc) : option nnrc :=
    match l with
    | nil => Some k
    | mr :: l =>
      match (nnrc_of_mr mr, nnrc_of_mr_chain (mr_output mr :: outputs) l k) with
      | (Some n, Some k) =>
        Some (NNRCLet
                (mr_output mr)
                (if in_dec equiv_dec (mr_output mr) outputs then
                   NNRCBinop OpBagUnion (NNRCVar (mr_output mr)) n
                 else n)
                k)
      | _ => None
      end
    end.

  Definition nnrc_of_nnrcmr_top (l: nnrcmr) : option nnrc :=
    let constants := map fst (mr_inputs_loc l) in
    let (last_fun, last_args) :=  mr_last l in
    let k := (gen_apply_fun_n last_fun last_args) in
    lift (nnrc_subst_var_to_const constants)
         (olift (nnrc_of_mr_chain nil (mr_chain l)) k).

End NNRCMRtoNNRC.

