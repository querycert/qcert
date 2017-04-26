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

Require Import CompilerRuntime.
Require String BrandRelation.
Require CAMPRuntime.

Require QOperators QData.

Module QCAMP(runtime:CompilerRuntime).

  Module Data := QData.QData(runtime).
  Module Ops := QOperators.QOperators(runtime).

  Definition expr : Set 
    := CAMP.camp.
  Definition camp : Set 
    := expr.
  Definition t : Set 
    := expr.
  
  Definition pconst : Data.t -> expr 
    := CAMP.pconst.
  Definition punop : Ops.Unary.op -> expr -> expr 
    := CAMP.punop.
  Definition pbinop : Ops.Binary.op -> expr -> expr -> expr 
    := CAMP.pbinop.
  Definition pmap : expr -> expr 
    := CAMP.pmap.
  Definition passert : expr -> expr 
    := CAMP.passert.
  Definition porelse : expr -> expr -> expr 
    := CAMP.porElse.
  Definition pit : expr 
    := CAMP.pit.
  Definition pletit : expr -> expr -> expr 
    := CAMP.pletIt.
  Definition pgetconstant : String.string -> expr 
    := CAMP.pgetconstant.
  Definition penv : expr 
    := CAMP.penv.
  Definition pletenv : expr -> expr -> expr 
    := CAMP.pletEnv.
  Definition pleft : expr 
    := CAMP.pleft.
  Definition pright : expr 
    := CAMP.pright.

  Definition pnow : expr
    := CAMPSugar.pnow.

  Definition pnull : expr
    := CAMPSugar.pnull.

  Definition pbdot : String.string -> expr -> expr
    := CAMPSugar.pbdot.

  Definition pbsomedot : String.string -> expr -> expr
    := CAMPSugar.pbsomedot.

  Definition returnVariables : list String.string -> expr
    := CAMPSugar.returnVariables.

  Definition stringConcat : expr -> expr -> expr
    := CAMPSugar.stringConcat.

  Definition toString : expr -> expr 
    := CAMPSugar.toString.

  Definition camp_binop_reduce : Ops.Binary.op -> list expr -> expr
    := CAMPSugar.camp_binop_reduce.

  Definition pvarwith : String.string -> expr -> expr
    := CAMPSugar.pvarwith.

  Definition withVar : String.string -> expr -> expr
    := CAMPSugar.withVar.

  Definition pIS : String.string -> expr -> expr
    := CAMPSugar.pIS.

  Definition lookup : String.string -> expr 
    := CAMPSugar.lookup.
  
End QCAMP.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
