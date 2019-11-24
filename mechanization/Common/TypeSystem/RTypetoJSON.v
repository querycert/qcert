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

Require Import List.
Require Import String.
Require Import ZArith.
Require Import Utils.
Require Import JSON.
Require Import BrandRelation.
Require Import RType.
Require Import RTypeNorm.
Require Import ForeignType.
Require Import ForeignTypeToJSON.

Section RTypeToJSON.

  Fixpoint json_brands (d:list json) : option (list string) :=
    match d with
    | nil => Some nil
    | (jstring s1) :: d' =>
      match json_brands d' with
      | Some s' => Some (s1::s')
      | None => None
      end
    | _ => None
    end.

  Context {ftype:foreign_type}.
  Context {ftypeToJSON:foreign_type_to_JSON}.

  (* JSON to RType *)
  Section toRType.
    Fixpoint json_to_rtype₀ (j:json) : rtype₀ :=
      match j with
      | jnull => Unit₀
      | jnumber _ => Unit₀
      | jbool _ => Unit₀
      | jarray _ => Unit₀
      | jstring "Top" => Top₀
      | jstring "Bottom" => Bottom₀
      | jstring "String" => String₀
      | jstring "Nat" => Nat₀
      | jstring "Float" => Float₀
      | jstring "Bool" => Bool₀
      | jstring _ => Unit₀
      | jobject nil => Rec₀ Open nil
      | jobject (("$brand"%string,jarray jl)::nil) =>
        match json_brands jl with
        | Some brs => Brand₀ brs
        | None => Unit₀
        end
      | jobject (("$coll"%string,j')::nil) => Coll₀ (json_to_rtype₀ j')
      | jobject (("$option"%string,j')::nil) => Either₀ (json_to_rtype₀ j') Unit₀
      | jobject jl => Rec₀ Open (map (fun kj => ((fst kj), (json_to_rtype₀ (snd kj)))) jl)
      end.

    Definition json_to_rtype {br:brand_relation} (j:json) :=
      normalize_rtype₀_to_rtype (json_to_rtype₀ j).

    Fixpoint json_to_rtype₀_with_fail (j:json) : option rtype₀ :=
      match j with
      | jnull => Some Unit₀
      | jnumber _ => None
      | jbool _ => None
      | jarray _ => None
      | jstring "Top" => Some Top₀
      | jstring "Bottom" => Some Bottom₀
      | jstring "String" => Some String₀
      | jstring "Nat" => Some Nat₀
      | jstring "Float" => Some Float₀
      | jstring "Bool" => Some Bool₀
      | jstring s => lift Foreign₀ (foreign_to_string_to_type s)
      | jobject nil => Some (Rec₀ Open nil)
      | jobject (("$brand"%string,jarray jl)::nil) =>
        match json_brands jl with
        | Some brs => Some (Brand₀ brs)
        | None => None
        end
      | jobject (("$coll"%string,j')::nil) => lift Coll₀ (json_to_rtype₀_with_fail j')
      | jobject (("$option"%string,j')::nil) => lift (fun x => Either₀ x Unit₀) (json_to_rtype₀_with_fail j')
      | jobject jl =>
        lift (fun x => Rec₀ Open x)
             ((fix rmap_rec (l: list (string * json)) : option (list (string * rtype₀)) :=
                 match l with
                 | nil => Some nil
                 | (x,y)::l' =>
                   match rmap_rec l' with
                   | None => None
                   | Some l'' =>
                     match json_to_rtype₀_with_fail y with
                     | None => None
                     | Some y'' => Some ((x,y'') :: l'')
                     end
                   end
                 end) jl)
      end.

    Definition json_to_rtype_with_fail {br:brand_relation} (j:json) : option rtype :=
      lift normalize_rtype₀_to_rtype (json_to_rtype₀_with_fail j).

  End toRType.

  (* JSON to VType *)
  Section toVType.
    Definition json_to_vrtype_with_fail {br:brand_relation} (j:json) : option (string * rtype) :=
      match j with
      | jobject (("dist"%string,jstring s)::("type"%string,j')::nil) =>
        lift (fun x => (s,x)) (json_to_rtype_with_fail j')
      | jobject (("type"%string,j')::("dist"%string,jstring s)::nil) =>
        lift (fun x => (s,x)) (json_to_rtype_with_fail j')
      | _ => None
      end.

  End toVType.
End RTypeToJSON.

