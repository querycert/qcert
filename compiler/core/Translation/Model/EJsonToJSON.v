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

Require Import List.
Require Import Ascii.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import FloatAdd.
Require Import ToString.
Require Import CoqLibAdd.
Require Import StringAdd.
Require Import Digits.
Require Import EquivDec.
Require Import ForeignEJson.
Require Import Utils.
Require Import JSONRuntime.
Require Import EJsonRuntime.
Require Import ForeignEJsonToJSON.

Section EJsontoJSON.
  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {ftojson:foreign_to_json}.

  Fixpoint json_to_ejson (j:json) : ejson :=
    match j with
    | jnull => ejnull
    | jnumber n => ejnumber n
    | jbool b => ejbool b
    | jstring s => ejstring s
    | jarray c => ejarray (map json_to_ejson c)
    | jobject nil => ejobject nil
    | jobject ((s1,j')::nil) =>
      if (string_dec s1 "$nat") then
        match j' with
        | jnumber n => ejbigint (float_truncate n)
        | _ => ejobject ((key_decode s1, json_to_ejson j')::nil)
        end
      else
        if (string_dec s1 "$foreign") then
          match foreign_to_json_to_ejson j' with
          | Some fd => ejforeign fd
          | None => ejobject ((key_decode s1, json_to_ejson j')::nil)
          end
        else ejobject ((s1, json_to_ejson j')::nil)
    | jobject r => ejobject (map (fun x => (fst x, json_to_ejson (snd x))) r)
    end.

  Fixpoint ejson_to_json (j:ejson) : json :=
    match j with
    | ejnull => jnull
    | ejnumber n => jnumber n
    | ejbigint n => jobject (("$nat"%string,jnumber (float_of_int n))::nil)
    | ejbool b => jbool b
    | ejstring s => jstring s
    | ejarray c => jarray (map ejson_to_json c)
    | ejobject r => jobject (map (fun x => (fst x, ejson_to_json (snd x))) r)
    | ejforeign fd => jobject (("$foreign"%string, foreign_to_json_from_ejson fd)::nil)
    end.

End EJsontoJSON.
