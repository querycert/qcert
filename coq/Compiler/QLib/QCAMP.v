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

  Definition camp : Set 
    := CAMP.camp.
  Definition t : Set 
    := camp.
  
  Definition pconst : Data.t -> camp 
    := CAMP.pconst.
  Definition punop : Ops.Unary.op -> camp -> camp 
    := CAMP.punop.
  Definition pbinop : Ops.Binary.op -> camp -> camp -> camp 
    := CAMP.pbinop.
  Definition pmap : camp -> camp 
    := CAMP.pmap.
  Definition passert : camp -> camp 
    := CAMP.passert.
  Definition porelse : camp -> camp -> camp 
    := CAMP.porElse.
  Definition pit : camp 
    := CAMP.pit.
  Definition pletit : camp -> camp -> camp 
    := CAMP.pletIt.
  Definition pgetConstant : String.string -> camp 
    := CAMP.pgetConstant.
  Definition penv : camp 
    := CAMP.penv.
  Definition pletenv : camp -> camp -> camp 
    := CAMP.pletEnv.
  Definition pleft : camp 
    := CAMP.pleft.
  Definition pright : camp 
    := CAMP.pright.

  Definition pnow : camp
    := CAMPSugar.pnow.

  Definition pnull : camp
    := CAMPSugar.pnull.

  Definition pbdot : String.string -> camp -> camp
    := CAMPSugar.pbdot.

  Definition pbsomedot : String.string -> camp -> camp
    := CAMPSugar.pbsomedot.

  Definition returnVariables : list String.string -> camp
    := CAMPSugar.returnVariables.

  Definition stringConcat : camp -> camp -> camp
    := CAMPSugar.stringConcat.

  Definition toString : camp -> camp 
    := CAMPSugar.toString.

  Definition camp_binop_reduce : Ops.Binary.op -> list camp -> camp
    := CAMPSugar.camp_binop_reduce.

  Definition pvarwith : String.string -> camp -> camp
    := CAMPSugar.pvarwith.

  Definition withVar : String.string -> camp -> camp
    := CAMPSugar.withVar.

  Definition pIS : String.string -> camp -> camp
    := CAMPSugar.pIS.

  Definition lookup : String.string -> camp 
    := CAMPSugar.lookup.
  
End QCAMP.

