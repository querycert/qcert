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
Require Import NRARuntime.
Require Import NRAEnvRuntime.
Require Import NNRCRuntime.
Require Import NNRCMRRuntime.
Require Import CloudantMR.
Require Import DNNRC Dataset.
Require Import CAMPRuntime.
Require Import ODMGRuntime.
Require Import TOptimEnvFunc.

Require Import CompilerRuntime.
Module CompEval(runtime:CompilerRuntime).
  Require Import BasicSystem.
  Require Import TypingRuntime.

  Require CompDriver.
  Module CD := CompDriver.CompDriver(runtime).
  Require EvalTop.
  Module ET := EvalTop.EvalTop(runtime).
  
  Context {bm:brand_model}.
  Context {ftyping: foreign_typing}.

  Definition world := list data.
  (* Definition pdata := presult data. *)
  Definition odata := option data.
  Definition oldata := option (list data).
  Definition oddata := option ddata.
  
  Inductive eval_input :=
  | I_world : world -> eval_input
  .

  Inductive eval_output :=
  | O_coll : oldata -> eval_output
  | O_data : option data -> eval_output
  | O_ddata : option ddata -> eval_output
  | O_error : string -> eval_output
  .

  Definition eval_query (h:list (string*string)) (q: CD.query) (i: eval_input) : eval_output :=
    match q, i with
    | CD.Q_rule q, I_world world => O_coll (ET.rule_eval_top h q world)
    | CD.Q_camp q, I_world world => O_coll (ET.pattern_eval_top h q world)
(* XXX No Eval for NRA? XXX *)
(*  | CD.Q_nra q, I_world world => O_data (ET.algenv_eval_top h q world) *)
    | CD.Q_nraenv q, I_world world => O_data (ET.algenv_eval_top h q world)
    | _,_ => O_error "Input does not match query"
    end.

(*
  Definition eval_input_of_rbindings (env:dbindings) : eval_input.
  Definition query_eval (q:query) : dbindings -> option data :=
    match q with
    | Q_rule q => Rule.Top.rule_eval (localize env)
    | Q_camp q => None
    | Q_oql q => None
    | Q_nra q => None
    | Q_nraenv q => None
    | Q_nnrc q => None
    | Q_nnrcmr q => None
    | Q_cldmr q => None
    | Q_dnnrc_dataset q => None
    | Q_dnnrc_typed_dataset q => None
    | Q_javascript _ => None
    | Q_java _ => None
    | Q_spark _ => None
    | Q_spark2 _ => None
    | Q_cloudant _ => None
    | Q_error _ => None
    end.
    *)
End CompEval.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
