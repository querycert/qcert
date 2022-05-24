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

Require Import Orders.
Require Import Equivalence.
Require Import EquivDec.
Require Import Compare_dec.
Require Import Lia.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import Utils.
Require Import ForeignEJson.
Require Import EJson.

Section EJsonSortBy.
  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.

  Definition ejson_get_criteria (sc:@ejson foreign_ejson_model) (r:list (string * @ejson foreign_ejson_model)) : option sdata :=
    match sc with
    | ejobject (("asc"%string, ejstring att)::nil)
    | ejobject (("desc"%string, ejstring att)::nil) => (* XXX IGNORES sort kind (asc|desc) XXX *)
      match edot r att with
      | Some (ejbigint n) => Some (sdnat n)
      | Some (ejstring s) => Some (sdstring s)
      | Some _ => None
      | None => None
      end
    | _ => None
    end.

  Definition table_of_ejson (d:@ejson foreign_ejson_model) : option (list (list (string * ejson))):=
    match d with
    | ejarray coll => lift_map ejson_is_record coll
    | _ => None
    end.

  Definition ejson_of_table (t: list (list (string * @ejson foreign_ejson_model))) : ejson :=
    ejarray (map ejobject t).
  
  Definition ejson_sort
             (scl:list (list (string * @ejson foreign_ejson_model) -> option sdata))
             (j:ejson) : option ejson :=
    lift ejson_of_table (olift (table_sort scl) (table_of_ejson j)).

End EJsonSortBy.

