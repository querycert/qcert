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
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.

Require Import Utils.
Require Import CommonRuntime.

Require Import LambdaNRA.
Require Import LambdaNRAEq.
Require Import LambdaNRAtoNRAEnv.
Require Import TrivialCompiler.
Require Import LambdaNRATest.

Import TrivialCompiler.
Require Import CompDriver.
Require Import CAMPTest.
Require Import CommonSystem.
Require Import TrivialModel.
Require Import TDataTest.

Require Import Program.

Require Import TCAMPTest.

Require Import CompEval.

Require Import NRATest.

Section tDNNRCTests.
 
  (* A4 : Persons.map{p => p.name} *)

  Definition A4 :=
    LNRAMap (LNRALambda "p" (LNRAUnop (OpDot "name") (LNRAVar "p"))) (LNRATable "Persons").

  (* LambdaNRA to DNNRC *)
  Definition a := lambda_nra_to_nraenv A4.
  Definition b := nraenv_to_nnrc a.
  Definition c := nnrc_to_dnnrc (("Persons"%string,Vdistr)::nil) b.

  (* Typing stuffs for then next steps *)
  Existing Instance CPModel.
  Definition PersonsType := Tdistr CustomerType.
  Definition tdenv :tdbindings := (("Persons"%string,PersonsType)::nil).

  (* Eval vm_compute in c. *)
  
  Definition d := dnnrc_to_dnnrc_typed c tdenv.

  Definition e:= lift dnnrc_typed_optim d.
  
  (* Eval stuffs *)
  Definition env :=
    mkDistConstants (("Persons"%string,Vdistr)::nil) (("Persons"%string,persons)::nil).
  Definition ev :=
    match env with
    | Some denv => lift (fun x => @eval_dnnrc_typed _ _ _ [] x denv) e
    | None => None
    end.

  (* Eval vm_compute in e. *)

End tDNNRCTests.

