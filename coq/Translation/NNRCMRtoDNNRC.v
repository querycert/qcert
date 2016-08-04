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

Section NNRCMRToDNNRC.
  Require Import String.
  Require Import List.
  Require Import Sorting.Mergesort.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import NNRC NNRCMR ForeignReduceOps DNNRC NNRCtoDNNRC.
  Local Open Scope string_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.

  Context (h:list(string*string)).

  Context {A plug_type:Set}.

  Definition map_res_id (mr_id: string) :=
    "mapRes_"++mr_id.

  (* Generates the DNNRC code corresponding to "(fun x => e1) e2" that is:
       let x = e2 in e1
   *)
  Definition gen_apply_fun (annot:A) (f: var * nrc) (e2: @dnrc _ A plug_type) : (@dnrc _ A plug_type) :=
    let (x, e1) := f in
    DNRCLet annot
            x e2
            (nrc_to_dnrc annot ((x, Vlocal)::nil) e1).

  (* Generates the DNNRC code corresponding to "(fun (x1, ..., xn) => e) (e1, ..., en)" that is:
       let x1 = e1 in
       ...
       let xn = en in
       e
   *)
  Fixpoint gen_apply_fun_n (annot:A) (f: list var * nrc)  (eff: list (var * dlocalization)) : option (@dnrc _ A plug_type) :=
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
              DNRCLet annot
                      x (DNRCVar annot y)
                      k)
           (nrc_to_dnrc annot form_loc e)
           l)
    | None => None
    end.

  Definition dnnrc_distr_of_mr_map (annot:A) (input: var) (mr_map: map_fun) : (@dnrc _ A plug_type) :=
    match mr_map with
    | MapDist (x, n) =>
      DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n)
    | MapDistFlatten (x, n) =>
      let res_map :=
          DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n)
      in
      DNRCUnop annot AFlatten res_map
    | MapScalar (x, n) =>
      let distr_input := DNRCDispatch annot (DNRCVar annot input) in
      DNRCFor annot x distr_input (nrc_to_dnrc annot ((x, Vlocal)::nil) n)
    end.

  Definition dnnrc_local_of_mr_map (annot:A) (input: var) (mr_map: map_fun) : (@dnrc _ A plug_type) :=
    match mr_map with
    | MapDist (x, n) =>
      let res_map := DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n) in
      DNRCCollect annot res_map
    | MapDistFlatten (x, n) =>
      let res_map := DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n) in
      DNRCCollect annot (DNRCUnop annot AFlatten res_map)
    | MapScalar (x, n) =>
      DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n)
    end.

  Definition dnnrc_of_mr (annot:A) (m:mr) : option (@dnrc _ A plug_type) :=
    match (m.(mr_map), m.(mr_reduce)) with
    | (MapScalar (x, NRCUnop AColl n), RedSingleton) =>
      Some (gen_apply_fun annot (x, n) (DNRCVar annot m.(mr_input)))
    | (_, RedSingleton) =>
      None
    | (map, RedId) =>
      Some (dnnrc_distr_of_mr_map annot (mr_input m) map)
    | (map, RedCollect red_fun) =>
      let map_expr := dnnrc_local_of_mr_map annot (mr_input m) map in
      Some (gen_apply_fun annot red_fun map_expr)
    | (map, RedOp _) => None (* XXXXXXXX TODO XXXXXXXXXXXXX *)
    end.

  Fixpoint dnnrc_of_mr_chain (annot: A) (outputs: list var) (l: list mr) (k: @dnrc _ A plug_type) : option (@dnrc _ A plug_type) :=
    match l with
    | nil => Some k
    | mr :: l =>
      match (dnnrc_of_mr annot mr, dnnrc_of_mr_chain annot (mr_output mr :: outputs) l k) with
      | (Some n, Some k) =>
        Some (DNRCLet annot
                      (mr_output mr)
                      (if in_dec equiv_dec (mr_output mr) outputs then
                         DNRCBinop annot AUnion (DNRCVar annot (mr_output mr)) n
                       else n)
                      k)
      | _ => None
      end
    end.

  Definition dnnrc_of_nrcmr (annot: A) (l: nrcmr) : option (@dnrc _ A plug_type) :=
    let (last_fun, last_args) :=  mr_last l in
    let k := gen_apply_fun_n annot last_fun last_args in
    olift (dnnrc_of_mr_chain annot nil (mr_chain l)) k.

End NNRCMRToDNNRC.

Section NNRCMRToSequentialDNNRC.

  (** Translate NNRCMR to DNNRC without parallel opterations. *)

  Require Import String.
  Require Import List.
  Require Import Sorting.Mergesort.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import NNRC NNRCMR ForeignReduceOps DNNRC.
  Local Open Scope string_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.

  Context (h:list(string*string)).

  Context {A plug_type:Set}.

  Definition seq_dnnrc_of_mr_map (annot:A) (input: var) (mr_map: map_fun) : (@dnrc _ A plug_type) :=
    match mr_map with
    | MapDist (x, n) =>
      DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n)
    | MapDistFlatten (x, n) =>
      let res_map :=
          DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n)
      in
      DNRCUnop annot AFlatten res_map
    | MapScalar (x, n) =>
      DNRCFor annot x (DNRCVar annot input) (nrc_to_dnrc annot ((x, Vlocal)::nil) n)
    end.

  Definition seq_dnnrc_of_mr (annot:A) (m:mr) : option (@dnrc _ A plug_type) :=
    match (m.(mr_map), m.(mr_reduce)) with
    | (MapScalar (x, NRCUnop AColl n), RedSingleton) =>
      Some (gen_apply_fun annot (x, n) (DNRCVar annot m.(mr_input)))
    | (_, RedSingleton) =>
      None
    | (map, RedId) =>
      Some (seq_dnnrc_of_mr_map annot (mr_input m) map)
    | (map, RedCollect red_fun) =>
      let map_expr := seq_dnnrc_of_mr_map annot (mr_input m) map in
      Some (gen_apply_fun annot red_fun map_expr)
    | (map, RedOp _) => None (* XXXXXXXX TODO XXXXXXXXXXXXX *)
    end.

  Fixpoint seq_dnnrc_of_mr_chain (annot: A) (outputs: list var) (l: list mr) (k: @dnrc _ A plug_type) : option (@dnrc _ A plug_type) :=
    match l with
    | nil => Some k
    | mr :: l =>
      match (seq_dnnrc_of_mr annot mr, seq_dnnrc_of_mr_chain annot (mr_output mr :: outputs) l k) with
      | (Some n, Some k) =>
        Some (DNRCLet annot
                      (mr_output mr)
                      (if in_dec equiv_dec (mr_output mr) outputs then
                         DNRCBinop annot AUnion (DNRCVar annot (mr_output mr)) n
                       else n)
                      k)
      | _ => None
      end
    end.

  Definition seq_dnnrc_of_nrcmr (annot: A) (l: nrcmr) : option (@dnrc _ A plug_type) :=
    let (last_fun, last_args) :=  mr_last l in
    let last_args_local :=
        List.map
          (fun (x_loc: var * dlocalization) => let (x, loc) := x_loc in (x, Vlocal))
          last_args
    in
    let k := gen_apply_fun_n annot last_fun last_args_local in
    List.fold_right
      (fun x_loc k =>
         match x_loc with
         | (x, Vdistr) => lift (DNRCLet annot x (DNRCCollect annot (DNRCVar annot x))) k
         | (x, Vlocal) => k
         end)
      (olift (seq_dnnrc_of_mr_chain annot nil (mr_chain l)) k)
      last_args.

End NNRCMRToSequentialDNNRC.


(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
