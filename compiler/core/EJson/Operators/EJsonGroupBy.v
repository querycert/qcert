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
Require Import String.
Require Import Utils.
Require Import Bindings.
Require Import ForeignEJson.
Require Import EJson.

Section EJsonGroupBy.
  Context {fejson:foreign_ejson}.
  Import ListNotations.

  (* Alternate semantics, using nested loop -- closer to NRC encoding of group by *)

  (* Note: split the proof in two:
       - define a nested-loop based group-by
       - prove that nested-loop based group-by is equivalent to Louis' group-by
       - prove that nested NRC group-by is same as nested-loop group-by
   *)

  (* key eval. there are really two forms. one form is symmetric,
     while the other works when the key computation has been split in two
     phases. which one to use depends on the group-by algorithm *)

  Definition ejson_key_is_eq_r (eval_key: ejson -> option ejson) (d1 d2:ejson) : option bool :=
    olift2 (fun x y => if ejson_eq_dec x y then Some true else Some false)
           (eval_key d1)
           (Some d2).

  Definition ejson_group_of_key (eval_key: ejson -> option ejson) (k:ejson) (l: list ejson) :=
    (lift_filter (fun d => ejson_key_is_eq_r eval_key d k) l).

  Definition ejson_group_by_nested_eval (eval_key: ejson -> option ejson) (l: list ejson) : option (list (ejson * (list ejson))) :=
    let dupkeys := lift_map (fun d => eval_key d) l in
    let keys := lift bdistinct dupkeys in
    olift (lift_map (fun k => olift (fun group => Some (k, group)) (ejson_group_of_key eval_key k l))) keys.

  Definition ejson_group_to_partitions (g:string) (group: ejson * list ejson) : option ejson :=
    match ejson_is_record (fst group) with
    | Some keys =>
      Some (ejobject (rec_concat_sort keys [(g, ejarray (snd group))]))
    | _ => None
    end.

  Definition ejson_to_partitions (g:string) (l: list (ejson * list ejson)) :=
    lift_map (ejson_group_to_partitions g) l.

  Definition ejson_group_by_nested_eval_keys_partition
             (g:string) (eval_keys:ejson -> option ejson) (l: list ejson) : option (list ejson) :=
    olift (ejson_to_partitions g) (ejson_group_by_nested_eval eval_keys l).

  Section tableform.
    Definition ejson_group_by_nested_eval_table
               (g:string) (sl:list string) (l:list ejson) : option (list ejson) :=
      ejson_group_by_nested_eval_keys_partition
        g
        (fun j =>
           match ejson_is_record j with
           | Some r => Some (ejobject (rproject r sl))
           | _ => None
           end) l.

  End tableform.

End EJsonGroupBy.

