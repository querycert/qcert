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

Section TGroupBy.
  Require Import List.

  Require Import Utils RBag.
  Require Import RDomain RData RRelation RGroupBy.

  Require Import TData.

  (** Main type-soundness lemma for group by *)
  Lemma typed_unop_yields_typed_data {τ₁ τout} (d1:data) (u:unaryOp) :
    (d1 ▹ τ₁) -> (unaryOp_type u τ₁ τout) ->
    (exists x, fun_of_unaryop brand_relation_brands u d1 = Some x /\ x ▹ τout).
  
  Fixpoint add_in_groups (is_eq: data -> data -> option bool) (d: data) (l: list (list data)) :=
    match l with
    | nil =>  Some ((d :: nil) :: nil)
    | group :: l' =>
      match group with
      | nil => None
      | d' :: _ =>
        match is_eq d d' with
        | Some true =>  Some ((d :: group) :: l')
        | Some false =>
          match add_in_groups is_eq d l' with
          | Some l'' => Some (group :: l'')
          | None => None
          end
        | None => None
        end
      end
    end.

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

  (* Primary semantics from Louis *)
  
  Definition group_by_iter_eval (get_key: data -> option data) (l: list data) : option (list (list data)) :=
    let is_eq := key_is_eq get_key in
    fold_right
      (fun d acc =>
         match acc with
         | Some acc' => add_in_groups is_eq d acc'
         | None => None
         end)
      (Some nil) l.

  Definition dgroup_by_iter_eval (get_key: data -> option data) (l: list data) : option data :=
    lift (fun x => dcoll (map dcoll x)) (group_by_iter_eval get_key l).
  
  (* Alternate semantics, using nested loop -- closer to NRC encoding of group by *)
  
  (* Note: split the proof in two:
       - define a nested-loop based group-by
       - prove that nested-loop based group-by is equivalent to Louis' group-by
       - prove that nested NRC group-by is same as nested-loop group-by
   *)

  Definition group_of_key (eval_key: data -> option data) (k:data) (l: list data) :=
    orfilter (fun d => key_is_eq_r eval_key d k) (Some l).

  Definition group_by_nested_eval (eval_key: data -> option data) (l: list data) : option (list (list data)) :=
    let is_eq := key_is_eq eval_key in
    let dupkeys := rmap (fun d => eval_key d) l in
    let keys := lift bdistinct dupkeys in
    olift (rmap (fun k => group_of_key eval_key k l)) keys.

  Definition dgroup_by_nested_eval (get_key: data -> option data) (l: list data) : option data :=
    lift (fun x => dcoll (map dcoll x)) (group_by_nested_eval get_key l).
  
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

End TGroupBy.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
