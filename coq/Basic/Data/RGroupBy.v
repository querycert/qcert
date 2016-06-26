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

Section RGroupBy.
  Require Import List.

  Require Import Utils.
  Require Import RBag.
  Require Import RDomain.
  Require Import RData.
  Require Import ForeignData.
  Require Import RRelation.

  Context {fdata:foreign_data}.

  Fixpoint add_in_groups (key: data) (d: data) (l: list (data * (list data))) : list (data * (list data)) :=
    match l with
    | nil =>  (key, (d :: nil)) :: nil
    | (key', group) :: l' =>
      if data_eq_dec key key'
      then
        (key', d::group) :: l'
      else
        let l'' := add_in_groups key d l' in
        (key', group) :: l''
    end.

  (* Primary semantics from Louis *)

  Definition group_by_iter_eval (get_key: data -> option data) (l: list data) : option (list (data * (list data))) :=
    fold_right
      (fun d acc =>
         match acc with
         | Some acc' => lift (fun k => add_in_groups k d acc') (get_key d)
         | None => None
         end)
      (Some nil) l.

  Definition group_by_iter_eval_alt (l: list (data * data)) : list (data * (list data)) :=
    fold_right
      (fun (d:data*data) acc => add_in_groups (fst d) (snd d) acc)
      nil l.

  (* Alternate semantics, using nested loop -- closer to NRC encoding of group by *)

  (* Note: split the proof in two:
       - define a nested-loop based group-by
       - prove that nested-loop based group-by is equivalent to Louis' group-by
       - prove that nested NRC group-by is same as nested-loop group-by
   *)

  (* key eval. there are really two forms. one form is symmetric,
     while the other works when the key computation has been split in two
     phases. which one to use depends on the group-by algorithm *)

  Definition key_is_eq (eval_key: data -> option data) (d1 d2:data) : option bool :=
    olift2 (fun x y => if data_eq_dec x y then Some true else Some false)
           (eval_key d1)
           (eval_key d2).

  Definition key_is_eq_r (eval_key: data -> option data) (d1 d2:data) : option bool :=
    olift2 (fun x y => if data_eq_dec x y then Some true else Some false)
           (eval_key d1)
           (Some d2).

  Require Import String.
  
  Definition group_of_key (eval_key: data -> option data) (k:data) (l: list data) :=
    (lift_filter (fun d => key_is_eq_r eval_key d k) l).

  Definition group_by_nested_eval (eval_key: data -> option data) (l: list data) : option (list (data * (list data))) :=
    let is_eq := key_is_eq eval_key in
    let dupkeys := rmap (fun d => eval_key d) l in
    let keys := lift bdistinct dupkeys in
    olift (rmap (fun k => olift (fun group => Some (k, group)) (group_of_key eval_key k l))) keys.

  Definition to_kv (l: list (data * list data)) :=
    map (fun x => drec (("key"%string,(fst x))::("value"%string,dcoll (snd x)) :: nil)) l.
  
  Definition group_by_nested_eval_kv (eval_key:data -> option data) (l: list data) : option (list data) :=
    lift to_kv (group_by_nested_eval eval_key l).

  (* This will be the harder lemma ... both group-by algorithms are equivalent *)
  (*
  Lemma add_group_same_as_nested_group_by ck l:
    group_by_nested_eval ck l = group_by_iter_eval ck l.
  Proof.
    unfold group_by_nested_eval, group_by_iter_eval.
    induction l; try reflexivity; simpl.
    ...
  Qed.
  *)

End RGroupBy.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)