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

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import ZArith.
  Require Import EquivDec.
  Require Import Morphisms.

  Require Import Utils BasicRuntime.
  Require Import DData.
  Require Import RAlgEnv.

  Require Import RType.

  Context {fruntime:foreign_runtime}.
  Context {ftype: ForeignType.foreign_type}.

  Definition var := string.

  Inductive column :=
  | CCol   : string                     -> column (* column("name") *)
  | CAs    : string -> column           -> column (* .as("new_name") *)
  | CPlus0 : string -> data   -> column -> column (* .plus(5).as("first") *)
  | CPlus1 : string -> column -> column -> column (* $column1.plus($column2) *)
  | CEq0   : string -> data   -> column -> column
  | CEq1   : string -> column -> column -> column
  | CNeg   : string -> column ->           column
  | CUDFCast : string -> list string -> column -> column (* TODO might want to factor UDFs out *)
  | CUDFUnbrand : string -> rtype₀ -> column -> column
  .

  Inductive spark_aggregate :=
  | SACount : spark_aggregate
  | SASum : spark_aggregate
  | SACollectList : spark_aggregate (* collect values into nested array *)
  .

  Inductive dataset :=
  | DSVar : string -> dataset (* ds *)
  | DSSelect : list column -> dataset -> dataset (* ds.select( ... ) *)
  | DSFilter : column -> dataset -> dataset (* ds.filter( ... ) *)
  (* ds.groupBy( grouping columns ).agg( aggregate expressions ) *)
  | DSGroupBy : list column -> list (string * spark_aggregate * column) -> dataset -> dataset
  | DSCartesian : dataset -> dataset -> dataset
  (* Rename DSUnnest? *)
  | DSExplode : string -> dataset -> dataset
  (* We might want to move CollectList from the aggregate functions to a toplevel operation here *)
  .

  Definition quote_string (s: string) : string :=
    """" ++ s ++ """".

  Require Import SparkData.

  Fixpoint code_of_column (c: column) : string :=
    match c with
    | CCol s => "column(""" ++ s ++ """)"
    | CAs new c => code_of_column c ++ ".as(""" ++ new ++ """)"
    | CEq1 new c1 c2 => code_of_column c1 ++ ".equalTo(" ++ code_of_column c2 ++ ").as(""" ++ new ++ """)"
    | CEq0 new d c => code_of_column c ++ ".equalTo(" ++ "32/*TODO_LITERAL_DATA*/" ++ ").as(""" ++ new ++ """)"
    | CUDFCast new bs c =>
      "QCertRuntime.castUDF(" ++ joinStrings ", " ("brandHierarchy"%string :: map quote_string bs) ++ ")(" ++ code_of_column c ++ ").as(""" ++ new ++ """)"
    | CUDFUnbrand new t c =>
      "QCertRuntime.unbrandUDF(" ++ rtype_to_scala t ++ ")(" ++ code_of_column c ++ ").as(""" ++ new ++ """)"
    | _ => "UNIMPLEMENTED_COLUMN"
    end.

  Definition code_of_aggregate (a : (string * spark_aggregate * column)) : string :=
    match a with
      (n, a, c) =>
      let c := code_of_column c in
      let f := match a with
               | SACount => "count"%string
               | SASum => "sum"%string
               | SACollectList => "collect_list"%string
               end
      in f ++ "(" ++ c ++ ").as(""" ++ n ++ """)"
    end.

  Fixpoint code_of_dataset (e: dataset) : string :=
    match e with
    | DSVar s => s
    | DSSelect cs d => code_of_dataset d ++ ".select(" ++ joinStrings ", " (map code_of_column cs) ++ ")"
    | DSFilter c d => code_of_dataset d ++ ".filter(" ++ code_of_column c ++ ")"
    | DSCartesian d1 d2 => code_of_dataset d1 ++ ".join(" ++ (code_of_dataset d2) ++ ")"
    | DSGroupBy gcs acs d => code_of_dataset d ++ ".groupBy(" ++ joinStrings ", " (map code_of_column gcs) ++ ").agg(" ++ joinStrings ", " (map code_of_aggregate acs) ++ ")"
    | DSExplode s d1 => code_of_dataset d1 ++ ".select(explode(" ++ code_of_column (CCol s) ++ ").as(""" ++ s ++ """))"
    end.

  Example ex1 :=
    DSFilter (CEq0 "f" (dnat 25) (CCol "age")) (DSVar "CONST$WORLD").

  Eval vm_compute in code_of_dataset ex1.
  
  Section eval.

    Definition srec n v :=
      drec ((n, v)::nil).

    Definition unsrec (d : option data) : option (string * data) :=
      match d with
      | Some (drec ((n, v)::nil)) => Some (n, v)
      | _ => None
      end.

    Definition fold_left1 {A} (op:A->A->A) (l:list A) (e:A) : A :=
      match l with
      | nil => e
      | x::xs => fold_left op xs x
      end.

    (** Take a list of singleton records and merge them together into one record. *)
    Definition merge_spark_columns (l: list (option data)) : option data :=
      fold_left1 (fun x a =>
                    match unsrec x, a with
                    | Some f, Some (drec fs) => Some (drec (rec_sort (f::fs)))
                    | _, _ => None
                    end)
                 l (Some (drec nil)).

    (** Given a column expression, return a function that takes a row of the input relation
        and produces a singleton record with the result value. *)
    Fixpoint fun_of_column (c : column) : data -> option data :=
      fun x =>
        match c with
        | CCol n =>
          match x with
          | drec fields => lift (srec n) (edot fields n)
          | _ => None
          end
        | CAs s c1 =>
          match unsrec (fun_of_column c1 x) with
          | Some (_, d) => Some (srec s d)
          | _ => None
          end
        | CEq0 n d c1 =>
          match unsrec (fun_of_column c1 x) with
          | Some (_, x) => Some (srec n (dbool (equiv_decb x d)))
          | _ => None
          end
        | CEq1 n c1 c2 =>
          match unsrec (fun_of_column c1 x), unsrec (fun_of_column c2 x) with
          | Some (n1, v1), Some (n2, v2) => Some (srec n (dbool (equiv_decb v1 v2)))
          | _, _ => None
          end
        | CPlus0 n d c1 =>
          match d, unsrec (fun_of_column c1 x) with
          | dnat d, Some (_, (dnat x)) => Some (srec n (dnat (Z.add x d)))
          | _, _ => None
          end
        | CPlus1 n c1 c2 =>
          match unsrec (fun_of_column c1 x), unsrec (fun_of_column c2 x) with
          | Some (_, (dnat v1)), Some (_, (dnat v2)) => Some (srec n (dnat (Z.add v1 v2)))
          | _, _ => None
          end
        | CNeg n c1 =>
          match unsrec (fun_of_column c1 x) with
          | Some (_, (dbool x)) => Some (srec n (dbool (negb x)))
          | _ => None
          end
        | _ => None (* TODO at least UDFs are unimplemented *)
        end.

    (* Used in selection *)
    Definition fun_of_columns (cs : list column) : data -> option data :=
      fun x =>
        let individual_columns := map (fun c => (fun_of_column c) x) cs in
        merge_spark_columns individual_columns.

    (** Value of an aggregation over an empty set. *)
    Definition empty_aggregate (a : spark_aggregate) : data :=
      match a with
      | SACount => dnat 0
      | SASum => dnat 0
      | SACollectList => dcoll nil
      end.


    (** Interpretation of a Spark aggregation function.
      * Should be suitable for folding over a list of data. *)
    Definition fun_of_aggregate (a : spark_aggregate) : option data -> data -> option data :=
      fun acc => fun x =>
                   match acc with
                   | Some acc =>
                     match a with
                     | SACount => match acc, x with
                                  | dnat acc, dnat x => Some (dnat (Z.add acc 1))
                                  | _, _ => None
                                  end
                     | SASum => match acc, x with
                                | dnat acc, dnat x => Some (dnat (Z.add acc x))
                                | _, _ => None
                                end
                     | SACollectList => match acc with
                                        | dcoll acc => Some (dcoll (acc ++ (x::nil)))
                                        | _ => None
                                        end
                     end
                   | None => None
                   end.

    (** Interpretation of one aggregation column.
     * Takes a list of records as input and reduces to a singleton record. *)
    Definition fun_of_aggregation (agg: string * spark_aggregate * column) : list data -> option data :=
      let extract_values c l :=
          let cfun := fun_of_column c in
          listo_to_olist (map (fun x => match unsrec (cfun x) with
                                              | Some (_, v) => Some v
                                              | _ => None
                                              end)
                              l) in
      match agg with
      | (n, a, c) =>
        fun l =>
          match extract_values c l with
          | Some values =>
            match fold_left (fun_of_aggregate a) values (Some (empty_aggregate a)) with
            | Some v => Some (srec n v)
            | None => None
            end
          | None => None
          end
      end.

    (** Interpretation of aggregate columns. *)
    Definition fun_of_aggregations (aggs: list (string * spark_aggregate * column)) : list data -> option data :=
      fun l =>
        merge_spark_columns (map (fun a => fun_of_aggregation a l) aggs).

    (** On some option ddata of the form (Some (Ddistr x)) perform some action f. *)
    Definition on_ddistr (od : option ddata) (f: list data -> list data) :=
      match od with
      | Some (Ddistr x) => Some (Ddistr (f x))
      | _ => None
      end.

    Context (dsenv : list (string * ddata)).

    Fixpoint dataset_eval (e: dataset) : option ddata :=
      match e with
      | DSVar s => lookup equiv_dec dsenv s
      | DSSelect cs d =>
        match dataset_eval d with
        | Some (Ddistr rows) =>
          lift Ddistr (listo_to_olist (map (fun_of_columns cs) rows))
        | _ => None
        end
      | DSFilter c d =>
        let fc := fun_of_column c in
        on_ddistr (dataset_eval d)
                  (filter (fun row => match unsrec (fc row) with
                                      | Some (_, (dbool true)) => true
                                      | _ => false
                                      end))
      | DSGroupBy gcs ags d =>
        let gfun := fun_of_columns gcs in
        let afun := fun_of_aggregations ags in
        match dataset_eval d with
        | Some (Ddistr rows) =>
          match group_by_nested_eval gfun rows with
          | Some grouped =>
            match listo_to_olist (map (fun g => match afun (snd g) with
                                                | Some v => Some ((fst g), v)
                                                | None => None
                                                end)
                                      grouped) with
            | Some aggregated =>
              let records := map (fun a => match a with
                                               | (drec group, drec agg) =>
                                                 Some (drec (group ++ agg))
                                               | _ => None
                                           end) aggregated in
              lift Ddistr (listo_to_olist records)
            | _ => None
            end
          | None => None
          end
        | _ => None
        end
      | DSCartesian d1 d2 =>
        match dataset_eval d1, dataset_eval d2 with
        | Some (Ddistr rs1), Some (Ddistr rs2) =>
          let data := flat_map (fun r1 => map (fun r2 =>
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
        match dataset_eval d1 with
        | Some (Ddistr l) =>
          let data :=
              flat_map (fun row =>
                          match row with
                          | drec fields =>
                            match edot fields s with
                            | Some (dcoll inners) =>
                              map (fun inner =>
                                     orecconcat (drec fields) (srec s inner))
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
