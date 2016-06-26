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
Module CompPattern(runtime:CompilerRuntime).
  Require String BrandRelation.
  Require CompOperators CompData.
  Require Pattern PatternSugar RuleSugar.

  Module Data := CompData.CompData(runtime).
  Module Ops := CompOperators.CompOperators(runtime).

  Definition expr : Set 
    := Pattern.pat.
  Definition pat : Set 
    := expr.
  Definition t : Set 
    := expr.
  
  Definition pconst : Data.t -> expr 
    := Pattern.pconst.
  Definition punop : Ops.Unary.op -> expr -> expr 
    := Pattern.punop.
  Definition pbinop : Ops.Binary.op -> expr -> expr -> expr 
    := Pattern.pbinop.
  Definition pmap : expr -> expr 
    := Pattern.pmap.
  Definition passert : expr -> expr 
    := Pattern.passert.
  Definition porelse : expr -> expr -> expr 
    := Pattern.porElse.
  Definition pit : expr 
    := Pattern.pit.
  Definition pletit : expr -> expr -> expr 
    := Pattern.pletIt.
  Definition pgetconstant : String.string -> expr 
    := Pattern.pgetconstant.
  Definition penv : expr 
    := Pattern.penv.
  Definition pletenv : expr -> expr -> expr 
    := Pattern.pletEnv.
  Definition pleft : expr 
    := Pattern.pleft.
  Definition pright : expr 
    := Pattern.pright.

  Definition pnow : expr
    := PatternSugar.pnow.

  Definition pnull : expr
    := PatternSugar.pnull.

  Definition pbdot : String.string -> expr -> expr
    := PatternSugar.pbdot.

  Definition pbsomedot : String.string -> expr -> expr
    := PatternSugar.pbsomedot.

  Definition returnVariables : list String.string -> expr
    := PatternSugar.returnVariables.

  Definition instanceOf : String.string -> BrandRelation.brands -> expr -> expr
    := RuleSugar.instanceOf.

  Definition matches : BrandRelation.brands -> expr -> expr
    := RuleSugar.matches.

  Definition fetchRef : BrandRelation.brands -> String.string -> String.string -> expr -> expr -> expr
    := RuleSugar.fetchRef.

  Definition stringConcat : expr -> expr -> expr
    := PatternSugar.stringConcat.

  Definition toString : expr -> expr 
    := PatternSugar.toString.

  Definition pat_binop_reduce : Ops.Binary.op -> list expr -> expr
    := PatternSugar.pat_binop_reduce.

  Definition pvarwith : String.string -> expr -> expr
    := PatternSugar.pvarwith.

  Definition withVar : String.string -> expr -> expr
    := PatternSugar.withVar.

  Definition pIS : String.string -> expr -> expr
    := PatternSugar.pIS.

  Definition lookup : String.string -> expr 
    := PatternSugar.lookup.
  
End CompPattern.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
