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
Require String Ascii.
Require BrandRelation.
Require Import ZArith.
Require RBinaryOps.

Module QOperators(runtime:CompilerRuntime).
  
  Module Unary.

    Definition op : Set  
      := RUnaryOps.unaryOp.
    Definition t : Set 
      := op.

    Definition aidop : op 
      := RUnaryOps.AIdOp.

    Module ZArith.
      Definition aabs : op 
        := RUnaryOps.AUArith RUnaryOps.ArithAbs.
      Definition alog2 : op 
        := RUnaryOps.AUArith RUnaryOps.ArithLog2.
      Definition asqrt : op 
        := RUnaryOps.AUArith RUnaryOps.ArithSqrt.
    End ZArith.

    Definition aneg : op 
      := RUnaryOps.ANeg.
    Definition acoll : op 
      := RUnaryOps.AColl.
    Definition acount : op 
      := RUnaryOps.ACount.
    Definition aflatten : op 
      := RUnaryOps.AFlatten.
    Definition aleft : op 
      := RUnaryOps.ALeft.
    Definition aright : op 
      := RUnaryOps.ARight.
    Definition abrand b : op 
      := RUnaryOps.ABrand b.
    Definition arec : String.string -> op 
      := RUnaryOps.ARec.
    Definition adot : String.string -> op 
      := RUnaryOps.ADot.
    Definition arecremove : String.string -> op 
      := RUnaryOps.ARecRemove.
    Definition arecproject : list String.string -> op 
      := RUnaryOps.ARecProject.
    Definition adistinct : op 
      := RUnaryOps.ADistinct.
    Definition asum : op 
      := RUnaryOps.ASum.
    Definition aarithmean : op 
      := RUnaryOps.AArithMean.
    Definition atostring : op 
      := RUnaryOps.AToString.
    Definition asubstring : Z -> option Z -> op 
      := RUnaryOps.ASubstring.
    Definition alike : String.string -> option Ascii.ascii -> op 
      := RUnaryOps.ALike.
    Definition acast : BrandRelation.brands -> op 
      := RUnaryOps.ACast.
    Definition aunbrand : op 
      := RUnaryOps.AUnbrand.
    Definition asingleton : op 
      := RUnaryOps.ASingleton.
    Definition anummin : op 
      := RUnaryOps.ANumMin.
    Definition anummax : op 
      := RUnaryOps.ANumMax.

  (* Note that foreign operators should be encapuslated and 
     exported as part of the model *)
  End Unary.

  Module Binary.

    Definition op : Set 
      := RBinaryOps.binOp.
    Definition t : Set 
      := op.

    Definition aeq : op 
      := RBinaryOps.AEq.
    
    Definition aunion : op 
      := RBinaryOps.AUnion.
    Definition aconcat : op 
      := RBinaryOps.AConcat.
    Definition amergeconcat : op 
      := RBinaryOps.AMergeConcat.
    Definition aand : op 
      := RBinaryOps.AAnd.
    Definition aor : op 
      := RBinaryOps.AOr.

    Module ZArith.
      Definition aplus : op 
        := RBinaryOps.ABArith RBinaryOps.ArithPlus.
      Definition aminus : op 
        := RBinaryOps.ABArith RBinaryOps.ArithMinus.
      Definition amult : op 
        := RBinaryOps.ABArith RBinaryOps.ArithMult.
      Definition amin : op 
        := RBinaryOps.ABArith RBinaryOps.ArithMin.
      Definition amax : op 
        := RBinaryOps.ABArith RBinaryOps.ArithMax.
      Definition adiv : op 
        := RBinaryOps.ABArith RBinaryOps.ArithDivide.
      Definition arem : op 
        := RBinaryOps.ABArith RBinaryOps.ArithRem.
    End ZArith.
    
    Definition alt : op 
      := RBinaryOps.ALt.
    Definition ale : op 
      := RBinaryOps.ALe.
    Definition aminus : op 
      := RBinaryOps.AMinus.
    Definition amin : op 
      := RBinaryOps.AMin.
    Definition amax : op 
      := RBinaryOps.AMax.
    Definition acontains : op 
      := RBinaryOps.AContains.
    Definition asconcat : op 
      := RBinaryOps.ASConcat.

    (* Note that foreign operators should be encapuslated and 
       exported as part of the model *)
  End Binary.
End QOperators.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
