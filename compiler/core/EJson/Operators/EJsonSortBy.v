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
  Context {fejson:foreign_ejson}.

  Definition ejson_get_criteria (j:ejson) (sc:ejson) : option sdata :=
    match sc with
    | ejobject (("asc"%string, ejstring att)::nil)
    | ejobject (("desc"%string, ejstring att)::nil) => (* XXX IGNORES sort kind (asc|desc) XXX *)
      match ejson_is_record j with
      | Some r =>
        match edot r att with
        | Some (ejbigint n) => Some (sdnat n)
        | Some (ejstring s) => Some (sdstring s)
        | Some _ => None
        | None => None
        end
      | None => None
      end
    | _ => None
    end.

  Definition ejson_get_criterias (j:ejson) (scl:list ejson) : option (list sdata) :=
    lift_map (ejson_get_criteria j) scl.

  Definition ejson_sortable_data_of_ejson (j:ejson) (scl:list ejson) : option sortable_data :=
    lift (fun c => (c,j)) (ejson_get_criterias j scl).

  Definition ejson_sortable_coll_of_coll (scl:list ejson) (coll:list ejson) :
    option (list sortable_data)
    := lift_map (fun j => ejson_sortable_data_of_ejson j scl) coll.
  
  Definition ejson_sort (scl:list ejson) (j:ejson) : option ejson :=
    match j with
    | ejarray coll =>
      lift ejarray
           (lift coll_of_sortable_coll
                 (lift sort_sortable_coll
                       (ejson_sortable_coll_of_coll scl coll)))
    | _ => None
    end.

  (* Example *)
  Definition mkperson (name:string) (age:Z) (zip:Z) (company:string) :=
    ejobject (("name", ejstring name)
                :: ("age", ejbigint age)
                :: ("zip", ejbigint zip)
                :: ("company", ejstring company)
                :: nil)%string.
  Definition mkpersons_aux l :=
    map (fun x =>
           match x with (name, age, zip, company) => mkperson name age zip company
           end) l.
  Definition mkpersons l :=
    ejarray (mkpersons_aux l).

  Open Scope Z_scope.
  Definition persons :=
    mkpersons
      (("John",23,1008,"ACME")
         :: ("Jane",24,1009,"AIGO")
         :: ("Jill",25,1010,"ACME")
         :: ("Jack",27,1010,"CMUD")
         :: nil)%string.

  (*
  Eval vm_compute in persons.
  Eval vm_compute in (ejson_sort ((ejobject (("asc"%string,ejstring "name"%string)::nil)::nil)) persons).
  Eval vm_compute in (ejson_sort ((ejobject (("asc"%string,ejstring "zip"%string)::nil))::(ejobject (("asc"%string, ejstring "name"%string)::nil))::nil) persons).
  *)

End EJsonSortBy.

