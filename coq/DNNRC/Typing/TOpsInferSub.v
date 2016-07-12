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

Section TOpsInferSub.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import Program.
  Require Import Eqdep_dec.
  Require Import Bool.
  Require Import EquivDec.
  
  Require Import Utils Types BasicRuntime.
  Require Import ForeignDataTyping ForeignOpsTyping TData TOps TOpsInfer.

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

    Definition infer_binop_type_sub
               (b:binOp) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
      match b with
      | AEq =>
        let τcommon := τ₁ ⊔ τ₂ in
        Some (Bool, τcommon, τcommon)
      | AConcat =>
        match τ₁ ==b ⊥, τ₂ ==b ⊥ with
        | true, true => Some (⊥, ⊥, ⊥)
        | true, false =>
           lift (fun _ => (τ₂, ⊥, τ₂)) (tunrec τ₂)
        | false, true =>
           lift (fun _ => (τ₁, ⊥, τ₂)) (tunrec τ₁)
        | false, false =>
          lift (fun τ => (τ, τ₁, τ₂)) (trecConcat τ₁ τ₂)
        end
      | AMergeConcat =>
        match τ₁ ==b ⊥, τ₂ ==b ⊥ with
        | true, true => Some (Coll ⊥, ⊥, ⊥)
        | true, false =>
           lift (fun _ => (Coll τ₂, ⊥, τ₂)) (tunrec τ₂)
        | false, true =>
           lift (fun _ => (Coll τ₁, ⊥, τ₂)) (tunrec τ₁)
        | false, false =>
          lift (fun τ => (Coll τ, τ₁, τ₂)) (tmergeConcat τ₁ τ₂)
        end
      | AAnd =>
        match subtype_dec τ₁ Bool, subtype_dec τ₂ Bool with
        | left _, left _ => Some (Bool, Bool, Bool)
        | _, _ => None
      end
      | AOr =>
        match subtype_dec τ₁ Bool, subtype_dec τ₂ Bool with
        | left _, left _ => Some (Bool, Bool, Bool)
        | _, _ => None
        end
      | ABArith _ =>
        match subtype_dec τ₁ Nat, subtype_dec τ₂ Nat with
        | left _, left _ => Some (Nat, Nat, Nat)
        | _, _ => None
        end
      | ALt
      | ALe =>
        match subtype_dec τ₁ Nat, subtype_dec τ₂ Nat with
        | left _, left _ => Some (Bool, Nat, Nat)
        | _, _ => None
        end
      | AUnion | AMinus | AMin | AMax =>
        let τcommon := τ₁ ⊔ τ₂ in
        if (tuncoll τcommon)
        then Some (τcommon, τcommon, τcommon)
        else None
      (* Note: this may be too permisive.
         We could be more restrictive by enforcing that the element 
         type is a subtype of the collection type *)
      | AContains =>
        if τ₂ ==b ⊥
        then Some (Bool, τ₁, τ₂)
        else lift (fun τ₂' =>
                     let τ := τ₁ ⊔ τ₂' in
                     (Bool, τ, Coll τ))
                  (tuncoll τ₂)
      | ASConcat =>
        match subtype_dec τ₁ String, subtype_dec τ₂ String with
        | left _, left _ => Some (String, String, String)
        | _, _ => None
        end
      | AForeignBinaryOp fb =>
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

    Definition infer_unop_type_sub (u:unaryOp) (τ₁:rtype) : option (rtype*rtype) :=
      match u with
      | AIdOp => Some (τ₁,τ₁)
      | ANeg =>
        if subtype_dec τ₁ Bool
        then Some (Bool, Bool)
        else None
      | AColl => Some (Coll τ₁,τ₁)
      | ASingleton =>
        let τ₁' := τ₁ ⊔ (Coll ⊥) in
        lift (fun τ => (τ, τ₁')) (tsingleton τ₁')
      | AFlatten =>
        let τ₁' := τ₁ ⊔ (Coll (Coll ⊥)) in
        bind (tuncoll τ₁')
             (fun τ₁in =>
                lift (fun _ => (τ₁in, τ₁'))
                     (tuncoll τ₁in))
      | ADistinct =>
        let τ₁' := τ₁ ⊔ (Coll ⊥) in
        lift (fun τ => (Coll τ, τ₁')) (tuncoll τ₁')
      | ARec s => Some (Rec Closed ((s, τ₁)::nil) eq_refl, τ₁)
        (* Note that ⊥ does not get further constrained by these *)
      | ADot s =>
        if τ₁ == ⊥
        then Some (⊥, ⊥)
        else lift (fun τ => (τ, τ₁)) (tunrecdot s τ₁)
      | ARecRemove s =>
        if τ₁ == ⊥
        then Some (⊥, ⊥)
        else lift (fun τ => (τ, τ₁)) (tunrecremove s τ₁)
      | ARecProject sl =>
        if τ₁ == ⊥
        then Some (⊥, ⊥)
        else lift (fun τ => (τ, τ₁)) (tunrecproject sl τ₁)
      | ACount =>
        let τ₁' := τ₁ ⊔ (Coll ⊥) in
        lift (fun τ => (Nat, τ₁')) (tuncoll τ₁')
      | ASum
      | ANumMin
      | ANumMax
      | AArithMean =>
        if subtype_dec τ₁ (Coll Nat)
        then Some (Nat, Coll Nat)
        else None
      | AToString =>
        Some (String, τ₁)
      | ALeft =>
        Some (Either τ₁ ⊥, τ₁)
      | ARight =>
        Some (Either ⊥ τ₁, τ₁)
      | ABrand b =>
        if (subtype_dec τ₁ (brands_type b))
        then Some (Brand b, τ₁)
        else None
    | AUnbrand =>
        if τ₁ == ⊥
        then
          Some (⊥, ⊥)
        else
          match `τ₁ with
          | Brand₀ b => Some (brands_type b, τ₁)
          | _ => None
          end
    | ACast b =>
      if τ₁ == ⊥
      then
        Some (⊥, ⊥)
      else
        match `τ₁ with
        | Brand₀ _ => Some (Option (Brand b), τ₁)
        | _ => None
        end
    | AUArith op =>
      if subtype_dec τ₁ Nat
      then Some (Nat, Nat)
      else None
    | AForeignUnaryOp fu =>
        foreign_unary_op_typing_infer_sub fu τ₁
      end.

  End u.
End TOpsInferSub.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
