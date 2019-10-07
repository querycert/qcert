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
Require Import Compare_dec.
Require Import Program.
Require Import Eqdep_dec.
Require Import Bool.
Require Import EquivDec.
Require Import Utils.
Require Import Types.
Require Import CommonData.
Require Import ForeignData.
Require Import ForeignOperators.
Require Import ForeignDataTyping.
Require Import ForeignOperatorsTyping.
Require Import Operators.
Require Import TUtil.
Require Import TData.
Require Import TSortBy.
Require Import TUnaryOperators.
Require Import TBinaryOperators.
Require Import TOperatorsInfer.

Section TOperatorsInferSub.
  (* Lemma/definitions over types involved in the inference *)
  
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Section b.

    Context {fbop:foreign_binary_op}.
    Context {fboptyping:foreign_binary_op_typing}.

    (* returns an optional tuple containing:
       1) the inferred type of the binary operation
       2) the required type of the first argument (will be a non-proper supertype of τ₁)
       3) the required type of the second argument (will be a non-proper supertype of τ₂)      
     *)

    Definition infer_binary_op_type_sub
               (b:binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
      match b with
      | OpEqual =>
        let τcommon := τ₁ ⊔ τ₂ in
        Some (Bool, τcommon, τcommon)
      | OpRecConcat =>
        match τ₁ ==b ⊥, τ₂ ==b ⊥ with
        | true, true => Some (⊥, ⊥, ⊥)
        | true, false =>
           lift (fun _ => (τ₂, ⊥, τ₂)) (tunrec τ₂)
        | false, true =>
           lift (fun _ => (τ₁, τ₁, ⊥)) (tunrec τ₁)
        | false, false =>
          lift (fun τ => (τ, τ₁, τ₂)) (trecConcatRight τ₁ τ₂)
        end
      | OpRecMerge =>
        match τ₁ ==b ⊥, τ₂ ==b ⊥ with
        | true, true => Some (Coll ⊥, ⊥, ⊥)
        | true, false =>
           lift (fun _ => (Coll τ₂, ⊥, τ₂)) (tunrec τ₂)
        | false, true =>
           lift (fun _ => (Coll τ₁, τ₁, ⊥)) (tunrec τ₁)
        | false, false =>
          lift (fun τ => (Coll τ, τ₁, τ₂)) (tmergeConcat τ₁ τ₂)
        end
      | OpAnd =>
        match subtype_dec τ₁ Bool, subtype_dec τ₂ Bool with
        | left _, left _ => Some (Bool, Bool, Bool)
        | _, _ => None
      end
      | OpOr =>
        match subtype_dec τ₁ Bool, subtype_dec τ₂ Bool with
        | left _, left _ => Some (Bool, Bool, Bool)
        | _, _ => None
        end
      | OpLt
      | OpLe =>
        match subtype_dec τ₁ Nat, subtype_dec τ₂ Nat with
        | left _, left _ => Some (Bool, Nat, Nat)
        | _, _ => None
        end
      | OpBagNth =>
        match subtype_dec τ₂ Nat with
        | left _ =>
          let τ₁' := τ₁ ⊔ (Coll ⊥) in
          lift (fun τ => (τ, τ₁', Nat)) (tsingleton τ₁')
        | _ => None
        end
      | OpBagUnion | OpBagDiff | OpBagMin | OpBagMax =>
        let τcommon := τ₁ ⊔ τ₂ in
        if (tuncoll τcommon)
        then Some (τcommon, τcommon, τcommon)
        else None
      (* Note: this may be too permisive.
         We could be more restrictive by enforcing that the element 
         type is a subtype of the collection type *)
      | OpContains =>
        if τ₂ ==b ⊥
        then Some (Bool, τ₁, τ₂)
        else lift (fun τ₂' =>
                     let τ := τ₁ ⊔ τ₂' in
                     (Bool, τ, Coll τ))
                  (tuncoll τ₂)
      | OpStringConcat =>
        match subtype_dec τ₁ String, subtype_dec τ₂ String with
        | left _, left _ => Some (String, String, String)
        | _, _ => None
        end
      | OpStringJoin =>
        match subtype_dec τ₁ String with
        | left _ =>
          if subtype_dec τ₂ (Coll String)
          then Some (String, String, Coll String)
          else None
        | _ => None
        end
      | OpNatBinary _ =>
        match subtype_dec τ₁ Nat, subtype_dec τ₂ Nat with
        | left _, left _ => Some (Nat, Nat, Nat)
        | _, _ => None
        end
      | OpFloatBinary _ =>
        match subtype_dec τ₁ Float, subtype_dec τ₂ Float with
        | left _, left _ => Some (Float, Float, Float)
        | _, _ => None
        end
      | OpFloatCompare _ =>
        match subtype_dec τ₁ Float, subtype_dec τ₂ Float with
        | left _, left _ => Some (Bool, Float, Float)
        | _, _ => None
        end
      | OpForeignBinary fb =>
        foreign_binary_op_typing_infer_sub fb τ₁ τ₂
      end.

  End b.

  Section u.
    Context {fuop:foreign_unary_op}.
    Context {fuoptyping:foreign_unary_op_typing}.

    (* returns an optional tuple containing:
       1) the inferred type of the binary operation
       2) the required type of the argument (will be a non-proper supertype of τ₁)
     *)

    Definition infer_unary_op_type_sub (u:unary_op) (τ₁:rtype) : option (rtype*rtype) :=
      match u with
      | OpIdentity => Some (τ₁,τ₁)
      | OpNeg =>
        if subtype_dec τ₁ Bool
        then Some (Bool, Bool)
        else None
      | OpRec s => Some (Rec Closed ((s, τ₁)::nil) eq_refl, τ₁)
        (* Note that ⊥ does not get further constrained by these *)
      | OpDot s =>
        if τ₁ == ⊥
        then Some (⊥, ⊥)
        else lift (fun τ => (τ, τ₁)) (tunrecdot s τ₁)
      | OpRecRemove s =>
        if τ₁ == ⊥
        then Some (⊥, ⊥)
        else lift (fun τ => (τ, τ₁)) (tunrecremove s τ₁)
      | OpRecProject sl =>
        if τ₁ == ⊥
        then Some (⊥, ⊥)
        else lift (fun τ => (τ, τ₁)) (tunrecproject sl τ₁)
      | OpBag => Some (Coll τ₁,τ₁)
      | OpSingleton =>
        let τ₁' := τ₁ ⊔ (Coll ⊥) in
        lift (fun τ => (τ, τ₁')) (tsingleton τ₁')
      | OpFlatten =>
        let τ₁' := τ₁ ⊔ (Coll (Coll ⊥)) in
        bind (tuncoll τ₁')
             (fun τ₁in =>
                lift (fun _ => (τ₁in, τ₁'))
                     (tuncoll τ₁in))
      | OpDistinct =>
        let τ₁' := τ₁ ⊔ (Coll ⊥) in
        lift (fun τ => (Coll τ, τ₁')) (tuncoll τ₁')
      | OpOrderBy sl =>
        let τ₁' := τ₁ ⊔ (Coll ⊥) in
        match (tuncoll τ₁') with
        | Some τ₁₀ =>
          match tunrecsortable (List.map fst sl) τ₁₀ with
          | Some _ => Some (τ₁', τ₁')
          | None => None
          end
        | None => None
        end
      | OpCount =>
        let τ₁' := τ₁ ⊔ (Coll ⊥) in
        lift (fun τ => (Nat, τ₁')) (tuncoll τ₁')
      | OpToString
      | OpToText =>
        Some (String, τ₁)
      | OpLength =>
        if (subtype_dec τ₁ String)
        then Some (Nat, String)
        else None
      | OpSubstring _ _ =>
        if (subtype_dec τ₁ String)
        then Some (String, String)
        else None
      | OpLike _ _ =>
        if (subtype_dec τ₁ String)
        then Some (Bool, String)
        else None
      | OpLeft =>
        Some (Either τ₁ ⊥, τ₁)
      | OpRight =>
        Some (Either ⊥ τ₁, τ₁)
      | OpBrand b =>
        if (subtype_dec τ₁ (brands_type b))
        then Some (Brand b, τ₁)
        else None
      | OpUnbrand =>
        if τ₁ == ⊥
        then
          Some (⊥, ⊥)
        else
          match `τ₁ with
          | Brand₀ b => Some (brands_type b, τ₁)
          | _ => None
          end
      | OpCast b =>
        if τ₁ == ⊥
        then
          Some (⊥, ⊥)
        else
          match `τ₁ with
          | Brand₀ _ => Some (Option (Brand b), τ₁)
          | _ => None
          end
      | OpNatUnary op =>
        if subtype_dec τ₁ Nat
        then Some (Nat, Nat)
        else None
      | OpNatSum
      | OpNatMin
      | OpNatMax
      | OpNatMean =>
        if subtype_dec τ₁ (Coll Nat)
        then Some (Nat, Coll Nat)
        else None
      | OpFloatOfNat =>
        if subtype_dec τ₁ Nat
        then Some (Float, Nat)
        else None
      | OpFloatUnary op =>
        if subtype_dec τ₁ Float
        then Some (Float, Float)
        else None
      | OpFloatTruncate =>
        if subtype_dec τ₁ Float
        then Some (Nat, Float)
        else None
      | OpFloatSum
      | OpFloatBagMin
      | OpFloatBagMax
      | OpFloatMean =>
        if subtype_dec τ₁ (Coll Float)
        then Some (Float, Coll Float)
        else None
      | OpForeignUnary fu =>
        foreign_unary_op_typing_infer_sub fu τ₁
      end.

  End u.
End TOperatorsInferSub.

