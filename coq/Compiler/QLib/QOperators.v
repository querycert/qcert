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
Require String.
Require Ascii.
Require Import ZArith.
Require BrandRelation.

Module QOperators(runtime:CompilerRuntime).
  
  Module Unary.

    Definition op : Set  
      := UnaryOperators.unary_op.
    Definition t : Set 
      := op.

    Module ZArith.
      Definition opabs : op 
        := UnaryOperators.OpNatUnary UnaryOperators.NatAbs.
      Definition oplog2 : op 
        := UnaryOperators.OpNatUnary UnaryOperators.NatLog2.
      Definition opsqrt : op 
        := UnaryOperators.OpNatUnary UnaryOperators.NatSqrt.
    End ZArith.

    Module NumberArith.
     Definition opnumberneg : op 
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberNeg.
     Definition opnumbersqrt : op 
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberSqrt.
     Definition opnumberexp : op 
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberExp.
     Definition opnumberlog : op 
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberLog.
     Definition opnumberlog10 : op 
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberLog10.
     Definition opnumberceil : op 
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberCeil.
     Definition opnumberfloor : op 
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberFloor.
     Definition opnumberabs : op
       := UnaryOperators.OpNumberUnary UnaryOperators.NumberAbs.
    End NumberArith.

    Definition opidentity : op 
      := UnaryOperators.OpIdentity.
    Definition opneg : op 
      := UnaryOperators.OpNeg.
    Definition oprec : String.string -> op 
      := UnaryOperators.OpRec.
    Definition opdot : String.string -> op 
      := UnaryOperators.OpDot.
    Definition oprecremove : String.string -> op 
      := UnaryOperators.OpRecRemove.
    Definition oprecproject : list String.string -> op 
      := UnaryOperators.OpRecProject.
    Definition opbag : op 
      := UnaryOperators.OpBag.
    Definition opsingleton : op 
      := UnaryOperators.OpSingleton.
    Definition opflatten : op 
      := UnaryOperators.OpFlatten.
    Definition opdistinct : op 
      := UnaryOperators.OpDistinct.
    Definition opcount : op 
      := UnaryOperators.OpCount.
    Definition optostring : op 
      := UnaryOperators.OpToString.
    Definition opsubstring : Z -> option Z -> op 
      := UnaryOperators.OpSubstring.
    Definition oplike : String.string -> option Ascii.ascii -> op 
      := UnaryOperators.OpLike.
    Definition opleft : op 
      := UnaryOperators.OpLeft.
    Definition opright : op 
      := UnaryOperators.OpRight.
    Definition opbrand b : op 
      := UnaryOperators.OpBrand b.
    Definition opunbrand : op 
      := UnaryOperators.OpUnbrand.
    Definition opcast : BrandRelation.brands -> op 
      := UnaryOperators.OpCast.
    Definition opnatsum : op 
      := UnaryOperators.OpNatSum.
    Definition opnatmin : op 
      := UnaryOperators.OpNatMin.
    Definition opnatmax : op 
      := UnaryOperators.OpNatMax.
    Definition opnatmean : op 
      := UnaryOperators.OpNatMean.
    Definition opnumberofnat : op 
      := UnaryOperators.OpNumberOfNat.
    Definition opnumbertruncate : op 
      := UnaryOperators.OpNumberTruncate.
    Definition opnumbersum : op 
      := UnaryOperators.OpNumberSum.
    Definition opnumbermin : op 
      := UnaryOperators.OpNumberBagMin.
    Definition opnumbermax : op 
      := UnaryOperators.OpNumberBagMax.
    Definition opnumbermean : op 
      := UnaryOperators.OpNumberMean.

  (* Note that foreign operators should be encapuslated and 
     exported as part of the model *)
  End Unary.

  Module Binary.

    Definition op : Set 
      := BinaryOperators.binary_op.
    Definition t : Set 
      := op.

    Module ZArith.
      Definition opplus : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatPlus.
      Definition opminus : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatMinus.
      Definition opmult : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatMult.
      Definition opmin : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatMin.
      Definition opmax : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatMax.
      Definition opdiv : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatDiv.
      Definition oprem : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatRem.
    End ZArith.
    
    Module NumberArith.
      Definition opnumberplus : op 
        := BinaryOperators.OpNumberBinary BinaryOperators.NumberPlus.
      Definition opnumberminus : op 
        := BinaryOperators.OpNumberBinary BinaryOperators.NumberMinus.
      Definition opnumbermult : op 
        := BinaryOperators.OpNumberBinary BinaryOperators.NumberMult.
      Definition opnumbermin : op 
        := BinaryOperators.OpNumberBinary BinaryOperators.NumberMin.
      Definition opnumbermax : op 
        := BinaryOperators.OpNumberBinary BinaryOperators.NumberMax.
      Definition opnumberdiv : op 
        := BinaryOperators.OpNumberBinary BinaryOperators.NumberDiv.
      Definition opnumberpow : op 
        := BinaryOperators.OpNumberBinary BinaryOperators.NumberPow.
    End NumberArith.
    
    Definition opequal : op 
      := BinaryOperators.OpEqual.
    Definition oprecconcat : op 
      := BinaryOperators.OpRecConcat.
    Definition oprecmerge : op 
      := BinaryOperators.OpRecMerge.
    Definition opand : op
      := BinaryOperators.OpAnd.
    Definition opor : op 
      := BinaryOperators.OpOr.
    Definition oplt : op 
      := BinaryOperators.OpLt.
    Definition ople : op 
      := BinaryOperators.OpLe.
    Definition opbagunion : op 
      := BinaryOperators.OpBagUnion.
    Definition opbagdiff : op 
      := BinaryOperators.OpBagDiff.
    Definition opbagmin : op 
      := BinaryOperators.OpBagMin.
    Definition opbagmax : op 
      := BinaryOperators.OpBagMax.
    Definition opcontains : op 
      := BinaryOperators.OpContains.
    Definition opstringconcat : op 
      := BinaryOperators.OpStringConcat.

    (* Note that foreign operators should be encapuslated and 
       exported as part of the model *)
  End Binary.
End QOperators.

