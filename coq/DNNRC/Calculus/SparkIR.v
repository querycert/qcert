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

Section SparkIR.

  Require Import Basics.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import ZArith.
  Require Import EquivDec.
  Require Import Morphisms.

  Require Import Utils BasicSystem.
  Require Import DData.
  Require Import RAlgEnv.
  Require Import ForeignToJavascript.

  Require Import RType.


  Context {fruntime:foreign_runtime}.
  Context {ftype: ForeignType.foreign_type}.
  Context {fttojs : ForeignToJavascript.foreign_to_javascript}.
  Context {m : TBrandModel.brand_model}.

  Definition var := string.

  Inductive column :=
  | CCol   : string -> column
  | CDot   : string -> column -> column
  | CLit   : data * rtype₀ -> column
  | CPlus  : column -> column -> column
  | CEq    : column -> column -> column
  | CNeg   : column -> column
  | CToString : column -> column
  | CSConcat : column -> column -> column
  | CUDFCast : list string -> column -> column
  | CUDFUnbrand : rtype₀ -> column -> column.

  Inductive dataset :=
  | DSVar : string -> dataset
  | DSSelect : list (string * column) -> dataset -> dataset
  | DSFilter : column -> dataset -> dataset
  | DSCartesian : dataset -> dataset -> dataset
  | DSExplode : string -> dataset -> dataset.


  Section eval.
    (** Evaluate a column expression in an environment of toplevel columns
     * i.e. a row in a dataset. *)
    Fixpoint fun_of_column (c: column) (row: list (string * data)) : option data :=
      let fc := flip fun_of_column row in
      match c with
      | CCol n =>
        lookup string_eqdec row n
      | CNeg c1 =>
        olift (unudbool negb) (fc c1)
      | CDot n c1 =>
        match fc c1 with
        | Some (drec fs) => edot fs n
        | _ => None
        end
      | CLit (d, _) => Some d
      | CPlus c1 c2 =>
        match fc c1, fc c2 with
        | Some (dnat l), Some (dnat r) => Some (dnat (Z.add l r))
        | _, _ => None
        end
      | CEq c1 c2 =>
        (* TODO We use QCert equality here, but we should define and use Spark equality. *)
        lift2 (fun x y => dbool (if data_eq_dec x y then true else false)) (fc c1) (fc c2)
      | CToString c1 =>
        lift (compose dstring dataToString) (fc c1)
      | CSConcat c1 c2 =>
        match fc c1, fc c2 with
        | Some (dstring l), Some (dstring r) => Some (dstring (l ++ r))
        | _, _ => None
        end
      | CUDFCast _ _ => None (* TODO *)
      | CUDFUnbrand _ _ => None (* TODO *)
      end.

    (** On some option ddata of the form (Some (Ddistr x)) perform some action f. *)
    Definition unuddistr (od : option ddata) (f: list data -> list data) :=
      match od with
      | Some (Ddistr x) => Some (Ddistr (f x))
      | _ => None
      end.

    Fixpoint dataset_eval (dsenv : list (string * ddata)) (e: dataset) : option ddata :=
      match e with
      | DSVar s => lookup equiv_dec dsenv s
      | DSSelect cs d =>
        match dataset_eval dsenv d with
        | Some (Ddistr rows) =>
          (* List of column names paired with their functions. *)
          let cfuns: list (string * (list (string * data) -> option data)) :=
              map (fun p => (fst p, fun_of_column (snd p))) cs in
          (* Call this function on every row in the input dataset.
           * It calls every column function in the context of the row. *)
          let rfun: data -> option (list (string * data)) :=
              fun row =>
                match row with
                | drec fs =>
                  listo_to_olist (map (fun p => lift (fun r => (fst p, r)) ((snd p) fs)) cfuns)
                | _ => None
                end
          in
          (* Call the row function on every row, and wrap the result in a record.
           * For the result to be a legal record in the QCert data model,
           * the field names must be in order and not contain duplicates. *)
          let results := map (compose (lift drec) rfun) rows in
          lift Ddistr (listo_to_olist results)
        | _ => None
        end
      | DSFilter c d =>
        let cfun := fun_of_column c in
        unuddistr (dataset_eval dsenv d)
                  (* TODO This silently swallows eval errors. Don't do that. *)
                  (filter (fun row =>
                             match row with
                             | drec fs =>
                               match cfun fs with
                               | Some (dbool true) => true
                               | _ => false
                               end
                             | _ => false
                             end))
      (* NOTE Spark / QCert semantics mismatch
       * Sparks join operation just appends the columns from the left side to the right,
       * and this is what the semantics model. For the result to be legal in QCert, great
       * care must be taken to ensure that this results in unique and sorted column names. *)
      | DSCartesian d1 d2 =>
        match dataset_eval dsenv d1, dataset_eval dsenv d2 with
        | Some (Ddistr rs1), Some (Ddistr rs2) =>
          let data :=
              flat_map (fun r1 => map (fun r2 =>
                                         match r1, r2 with
                                         | drec a, drec b => Some (drec (a ++ b))
                                         | _, _ => None
                                         end)
                                      rs2)
                       rs1 in
          lift Ddistr (listo_to_olist data)
        | _, _ => None
        end
      | DSExplode s d1 =>
        match dataset_eval dsenv d1 with
        | Some (Ddistr l) =>
          let data :=
              flat_map (fun row =>
                          match row with
                          | drec fields =>
                            match edot fields s with
                            | Some (dcoll inners) =>
                              map (fun inner =>
                                     orecconcat (drec fields) (drec ((s, inner)::nil)))
                                  inners
                            | _ => None::nil
                            end
                          | _ => None::nil
                          end)
                       l in
          lift Ddistr (listo_to_olist data)
        | _ => None
        end
      end.
  End eval.

End SparkIR.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
