(*
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

    Module FloatArith.
     Definition opfloatneg : op 
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatNeg.
     Definition opfloatsqrt : op 
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatSqrt.
     Definition opfloatexp : op 
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatExp.
     Definition opfloatlog : op 
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatLog.
     Definition opfloatlog10 : op 
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatLog10.
     Definition opfloatceil : op 
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatCeil.
     Definition opfloatfloor : op 
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatFloor.
     Definition opfloatabs : op
       := UnaryOperators.OpFloatUnary UnaryOperators.FloatAbs.
    End FloatArith.

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
    Definition oplength : op 
      := UnaryOperators.OpLength.
    Definition opsubstring : Z -> option Z -> op 
      := UnaryOperators.OpSubstring.
    Definition oplike : String.string -> op 
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
    Definition opfloatofnat : op 
      := UnaryOperators.OpFloatOfNat.
    Definition opfloattruncate : op 
      := UnaryOperators.OpFloatTruncate.
    Definition opfloatsum : op 
      := UnaryOperators.OpFloatSum.
    Definition opfloatmin : op 
      := UnaryOperators.OpFloatBagMin.
    Definition opfloatmax : op 
      := UnaryOperators.OpFloatBagMax.
    Definition opfloatmean : op 
      := UnaryOperators.OpFloatMean.

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
    
    Module FloatArith.
      Definition opfloatlt : op 
        := BinaryOperators.OpFloatCompare BinaryOperators.FloatLt.
      Definition opfloatle : op 
        := BinaryOperators.OpFloatCompare BinaryOperators.FloatLe.

      Definition opfloatplus : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatPlus.
      Definition opfloatminus : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMinus.
      Definition opfloatmult : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMult.
      Definition opfloatmin : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMin.
      Definition opfloatmax : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMax.
      Definition opfloatdiv : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatDiv.
      Definition opfloatpow : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatPow.
    End FloatArith.
    
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
    Definition opbagnth : op 
      := BinaryOperators.OpBagNth.
    Definition opcontains : op 
      := BinaryOperators.OpContains.
    Definition opstringconcat : op 
      := BinaryOperators.OpStringConcat.
    Definition opstringjoin : op 
      := BinaryOperators.OpStringJoin.

    (* Note that foreign operators should be encapuslated and 
       exported as part of the model *)
  End Binary.
End QOperators.

