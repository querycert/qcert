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
Require Import Utils.
Require Import ForeignData.
Require Import Data.
Require Import DataLift.
Require Import Iterators.
Require Import RecOperators.
Require Import BrandRelation.
Require Import DataNorm.

Section GroupBy.
  Context {fdata:foreign_data}.
  Import ListNotations.

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

  Lemma key_is_eq_with_project_eq sl d l :
    key_is_eq_r
      (fun d0 : data =>
         match d0 with
         | dunit => None
         | dnat _ => None
         | dfloat _ => None
         | dbool _ => None
         | dstring _ => None
         | dcoll _ => None
         | drec r => Some (drec (rproject r sl))
         | dleft _ => None
         | dright _ => None
         | dbrand _ _ => None
         | dforeign _ => None
         end) (drec l) d =
    Some (if data_eq_dec (drec (rproject l sl)) d then true else false).
  Proof.
    unfold key_is_eq_r.
    Opaque data_eq_dec.
    simpl.
    destruct (data_eq_dec (drec (rproject l sl)) d); reflexivity.
  Qed.

  Definition group_of_key (eval_key: data -> option data) (k:data) (l: list data) :=
    (lift_filter (fun d => key_is_eq_r eval_key d k) l).

  Definition group_by_nested_eval (eval_key: data -> option data) (l: list data) : option (list (data * (list data))) :=
    let dupkeys := lift_map (fun d => eval_key d) l in
    let keys := lift bdistinct dupkeys in
    olift (lift_map (fun k => olift (fun group => Some (k, group)) (group_of_key eval_key k l))) keys.

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

  Definition group_to_partitions (g:string) (group: data * list data) : option data :=
    match (fst group) with
    | drec keys =>
      Some (drec (rec_concat_sort keys [(g, dcoll (snd group))]))
    | _ => None
    end.

  Definition to_partitions (g:string) (l: list (data * list data)) :=
    lift_map (group_to_partitions g) l.
  
  Definition group_by_nested_eval_keys_partition
             (g:string) (eval_keys:data -> option data) (l: list data) : option (list data) :=
    olift (to_partitions g) (group_by_nested_eval eval_keys l).

  Section tableform.
    Definition group_by_nested_eval_table
               (g:string) (sl:list string) (l:list data) : option (list data) :=
      group_by_nested_eval_keys_partition
        g
        (fun d =>
           match d with
           | drec r => Some (drec (rproject r sl))
           | _ => None
           end) l.

    Lemma group_of_key_over_table_correct sl d incoll :
      olift (fun group : list data => Some (dcoll group))
            (group_of_key
               (fun d : data =>
                  match d with
                  | dunit => None
                  | dnat _ => None
                  | dfloat _ => None
                  | dbool _ => None
                  | dstring _ => None
                  | dcoll _ => None
                  | drec r => Some (drec (rproject r sl))
                  | dleft _ => None
                  | dright _ => None
                  | dbrand _ _ => None
                  | dforeign _ => None
                  end) d incoll)
      =
      (olift
         (fun d1 : data =>
            lift_oncoll
              (fun l2 : list data => lift dcoll (oflatten l2)) d1)
         (lift dcoll
               (lift_map
                  (fun d1 : data =>
                     olift
                       (fun d0 : data =>
                          match d0 with
                          | dunit => None
                          | dnat _ => None
                          | dfloat _ => None
                          | dbool true => Some (dcoll (d1 :: nil))
                          | dbool false => Some (dcoll nil)
                          | dstring _ => None
                          | dcoll _ => None
                          | drec _ => None
                          | dleft _ => None
                          | dright _ => None
                          | dbrand _ _ => None
                          | dforeign _ => None
                          end)
                       (olift2
                          (fun d0 d2 : data =>
                             unbdata
                               (fun x y : data =>
                                  if data_eq_dec x y then true else false) d0
                               d2)
                          match d1 with
                          | dunit => None
                          | dnat _ => None
                          | dfloat _ => None
                          | dbool _ => None
                          | dstring _ => None
                          | dcoll _ => None
                          | drec r => Some (drec (rproject r sl))
                          | dleft _ => None
                          | dright _ => None
                          | dbrand _ _ => None
                          | dforeign _ => None
                          end (Some d))) incoll))).
    Proof.
      induction incoll; simpl in *; [reflexivity| ].
      unfold group_of_key in *.
      simpl in *.
      destruct a; simpl in *; try congruence.
      rewrite key_is_eq_with_project_eq.
      destruct (data_eq_dec (drec (rproject l sl)) d); simpl.
      - destruct (lift_filter
                    (fun d0 : data =>
                       key_is_eq_r
                         (fun d1 : data =>
                            match d1 with
                            | dunit => None
                            | dnat _ => None
                            | dfloat _ => None
                            | dbool _ => None
                            | dstring _ => None
                            | dcoll _ => None
                            | drec r => Some (drec (rproject r sl))
                            | dleft _ => None
                            | dright _ => None
                            | dbrand _ _ => None
                            | dforeign _ => None
                            end) d0 d) incoll);
          destruct ((lift_map
                       (fun d1 : data =>
                          olift
                            (fun d0 : data =>
                               match d0 with
                               | dunit => None
                               | dnat _ => None
                               | dfloat _ => None
                               | dbool true => Some (dcoll (d1 :: nil))
                               | dbool false => Some (dcoll nil)
                               | dstring _ => None
                               | dcoll _ => None
                               | drec _ => None
                               | dleft _ => None
                               | dright _ => None
                               | dbrand _ _ => None
                               | dforeign _ => None
                               end)
                            (olift2
                               (fun d0 d2 : data =>
                                  unbdata
                                    (fun x y : data =>
                                       if data_eq_dec x y then true else false) d0 d2)
                               match d1 with
                               | dunit => None
                               | dnat _ => None
                               | dfloat _ => None
                               | dbool _ => None
                               | dstring _ => None
                               | dcoll _ => None
                               | drec r => Some (drec (rproject r sl))
                               | dleft _ => None
                               | dright _ => None
                               | dbrand _ _ => None
                               | dforeign _ => None
                               end (Some d))) incoll)); simpl in *; try congruence.
        case_eq (oflatten l1); intros.
        subst.
        rewrite H in IHincoll; simpl in *.
        inversion IHincoll; subst.
        rewrite (oflatten_cons _ _ l2); try assumption. reflexivity.
        rewrite H in IHincoll; simpl in *; congruence.
        case_eq (oflatten l0); intros; subst; simpl in *; try congruence.
        rewrite H in IHincoll; simpl in *; congruence.
        rewrite H in IHincoll; simpl in *.
        rewrite oflatten_cons_none; [reflexivity|assumption].
      - destruct (lift_filter
                    (fun d0 : data =>
                       key_is_eq_r
                         (fun d1 : data =>
                            match d1 with
                            | dunit => None
                            | dnat _ => None
                            | dfloat _ => None
                            | dbool _ => None
                            | dstring _ => None
                            | dcoll _ => None
                            | drec r => Some (drec (rproject r sl))
                            | dleft _ => None
                            | dright _ => None
                            | dbrand _ _ => None
                            | dforeign _ => None
                            end) d0 d) incoll);
          destruct ((lift_map
                       (fun d1 : data =>
                          olift
                            (fun d0 : data =>
                               match d0 with
                               | dunit => None
                               | dnat _ => None
                               | dfloat _ => None
                               | dbool true => Some (dcoll (d1 :: nil))
                               | dbool false => Some (dcoll nil)
                               | dstring _ => None
                               | dcoll _ => None
                               | drec _ => None
                               | dleft _ => None
                               | dright _ => None
                               | dbrand _ _ => None
                               | dforeign _ => None
                               end)
                            (olift2
                               (fun d0 d2 : data =>
                                  unbdata
                                    (fun x y : data =>
                                       if data_eq_dec x y then true else false) d0 d2)
                               match d1 with
                               | dunit => None
                               | dnat _ => None
                               | dfloat _ => None
                               | dbool _ => None
                               | dstring _ => None
                               | dcoll _ => None
                               | drec r => Some (drec (rproject r sl))
                               | dleft _ => None
                               | dright _ => None
                               | dbrand _ _ => None
                               | dforeign _ => None
                               end (Some d))) incoll)); simpl in *; try congruence.
        case_eq (oflatten l1); intros.
        subst.
        rewrite H in IHincoll; simpl in *.
        inversion IHincoll; subst.
        rewrite (oflatten_cons _ _ l2); try assumption.
        rewrite H in IHincoll; simpl in *; congruence.
        case_eq (oflatten l0); intros; subst; simpl in *; try congruence.
        rewrite H in IHincoll; simpl in *; congruence.
        rewrite H in IHincoll; simpl in *.
        rewrite oflatten_cons_none; [reflexivity|assumption].
    Qed.

    Lemma group_of_key_destruct_drec_inv g sl d l0 l1 incoll:
      match d with
      | dunit => None
      | dnat _ => None
      | dfloat _ => None
      | dbool _ => None
      | dstring _ => None
      | dcoll _ => None
      | drec r2 =>
        Some
          (drec
             (rec_concat_sort r2 [(g, dcoll l1)]))
      | dleft _ => None
      | dright _ => None
      | dbrand _ _ => None
      | dforeign _ => None
      end = None ->
      olift (to_partitions g)
            (lift (fun t' : list (data * list data) => (d, l1) :: t')
                  (lift_map
                     (fun k : data =>
                        olift (fun group : list data => Some (k, group))
                              (group_of_key
                                 (fun d : data =>
                                    match d with
                                    | dunit => None
                                    | dnat _ => None
                                    | dfloat _ => None
                                    | dbool _ => None
                                    | dstring _ => None
                                    | dcoll _ => None
                                    | drec r => Some (drec (rproject r sl))
                                    | dleft _ => None
                                    | dright _ => None
                                    | dbrand _ _ => None
                                    | dforeign _ => None
                                    end) k incoll)) l0)) = None.
    Proof.
      intros.
      case_eq d; intros; subst; simpl in *; try congruence;
        destruct (lift_map
                    (fun k : data =>
                       olift (fun group : list data => Some (k, group))
                             (group_of_key
                                (fun d : data =>
                                   match d with
                                   | dunit => None
                                   | dnat _ => None
                                   | dfloat _ => None
                                   | dbool _ => None
                                   | dstring _ => None
                                   | dcoll _ => None
                                   | drec r => Some (drec (rproject r sl))
                                   | dleft _ => None
                                   | dright _ => None
                                   | dbrand _ _ => None
                                   | dforeign _ => None
                                   end) k incoll)) l0); simpl;
          unfold to_partitions; simpl; try reflexivity.
    Qed.

    Lemma groupby_test_lemma l0 g sl l1 l2 incoll :
      olift (to_partitions g)
            (lift (fun t' : list (data * list data) => (drec l2, l1) :: t')
                  (lift_map
                     (fun k : data =>
                        olift (fun group : list data => Some (k, group))
                              (group_of_key
                                 (fun d : data =>
                                    match d with
                                    | dunit => None
                                    | dnat _ => None
                                    | dfloat _ => None
                                    | dbool _ => None
                                    | dstring _ => None
                                    | dcoll _ => None
                                    | drec r => Some (drec (rproject r sl))
                                    | dleft _ => None
                                    | dright _ => None
                                    | dbrand _ _ => None
                                    | dforeign _ => None
                                    end) k incoll)) l0))
      =
      lift
        (fun t' : list data =>
           drec
             (rec_concat_sort l2 [(g, dcoll l1)]) :: t')
        (lift_map
           (fun d1 : data =>
              olift2
                (fun d0 d2 : data =>
                   match d0 with
                   | dunit => None
                   | dnat _ => None
                   | dfloat _ => None
                   | dbool _ => None
                   | dstring _ => None
                   | dcoll _ => None
                   | drec r1 =>
                     match d2 with
                     | dunit => None
                     | dnat _ => None
                     | dfloat _ => None
                     | dbool _ => None
                     | dstring _ => None
                     | dcoll _ => None
                     | drec r2 => Some (drec (rec_concat_sort r1 r2))
                     | dleft _ => None
                     | dright _ => None
                     | dbrand _ _ => None
                     | dforeign _ => None
                     end
                   | dleft _ => None
                   | dright _ => None
                   | dbrand _ _ => None
                   | dforeign _ => None
                   end)
                (Some d1) 
                (olift (fun d0 : data => Some (drec ((g, d0) :: nil)))
                       (olift
                          (fun d0 : data =>
                             lift_oncoll
                               (fun l3 : list data => lift dcoll (oflatten l3)) d0)
                          (lift dcoll
                                (lift_map
                                   (fun d0 : data =>
                                      olift
                                        (fun d2 : data =>
                                           match d2 with
                                           | dunit => None
                                           | dnat _ => None
                                           | dfloat _ => None
                                           | dbool true => Some (dcoll (d0 :: nil))
                                           | dbool false => Some (dcoll nil)
                                           | dstring _ => None
                                           | dcoll _ => None
                                           | drec _ => None
                                           | dleft _ => None
                                           | dright _ => None
                                           | dbrand _ _ => None
                                           | dforeign _ => None
                                           end)
                                        (olift2
                                           (fun d2 d3 : data =>
                                              unbdata
                                                (fun x y : data =>
                                                   if data_eq_dec x y then true else false)
                                                d2 d3)
                                           match d0 with
                                           | dunit => None
                                           | dnat _ => None
                                           | dfloat _ => None
                                           | dbool _ => None
                                           | dstring _ => None
                                           | dcoll _ => None
                                           | drec r => Some (drec (rproject r sl))
                                           | dleft _ => None
                                           | dright _ => None
                                           | dbrand _ _ => None
                                           | dforeign _ => None
                                           end (Some d1))) incoll))))) l0).
    Proof.
      intros.
      induction l0; simpl.
      - unfold to_partitions, group_to_partitions.
        reflexivity.
      - rewrite <- group_of_key_over_table_correct.
        destruct (group_of_key
                    (fun d : data =>
                       match d with
                       | drec r => Some (drec (rproject r sl))
                       | _ => None
                       end) a incoll); intros; simpl; try reflexivity.
        case_eq (match a with
                 | drec r2 =>
                   Some
                     (drec
                        (rec_concat_sort r2 [(g, dcoll l)]))
                 | _ => None
                 end); intros.
        + simpl in *.
          destruct (lift_map
                      (fun k : data =>
                         olift (fun group : list data => Some (k, group))
                               (group_of_key
                                  (fun d0 : data =>
                                     match d0 with
                                     | drec r => Some (drec (rproject r sl))
                                     | _ => None
                                     end) k incoll)) l0); simpl in *
          ; destruct ((lift_map
          (fun d1 : data =>
           match
             olift (fun d0 : data => Some (drec [(g, d0)]))
               (olift
                  (fun d0 : data =>
                   lift_oncoll (fun l4 : list data => lift dcoll (oflatten l4)) d0)
                  (lift dcoll
                     (lift_map
                        (fun d0 : data =>
                         olift
                           (fun d2 : data =>
                            match d2 with
                            | dbool true => Some (dcoll [d0])
                            | dbool false => Some (dcoll [])
                            | _ => None
                            end)
                           (olift2
                              (fun d2 d3 : data =>
                               unbdata
                                 (fun x y : data => if data_eq_dec x y then true else false)
                                 d2 d3)
                              match d0 with
                              | drec r => Some (drec (rproject r sl))
                              | _ => None
                              end (Some d1))) incoll)))
           with
           | Some d2 =>
               match d1 with
               | drec r1 =>
                   match d2 with
                   | drec r2 => Some (drec (rec_concat_sort r1 r2))
                   | _ => None
                   end
               | _ => None
               end
           | None => None
           end) l0)); simpl in *
          ; unfold to_partitions in *; simpl in *; trivial; try discriminate.
          * destruct (lift_map (group_to_partitions g) l3); simpl in *; try discriminate.
            invcs IHl0.
            destruct a; try discriminate; invcs H.
            simpl; trivial.
          * destruct (lift_map (group_to_partitions g) l3); simpl in *; try discriminate.
            destruct a; simpl; try discriminate; trivial.
+ generalize (group_of_key_destruct_drec_inv g sl a l0 l incoll H); intros.
          auto.
          destruct (lift_map
                      (fun k : data =>
                         olift (fun group : list data => Some (k, group))
                               (group_of_key
                                  (fun d : data =>
                                     match d with
                                     | dunit => None
                                     | dnat _ => None
                                     | dfloat _ => None
                                     | dbool _ => None
                                     | dstring _ => None
                                     | dcoll _ => None
                                     | drec r => Some (drec (rproject r sl))
                                     | dleft _ => None
                                     | dright _ => None
                                     | dbrand _ _ => None
                                     | dforeign _ => None
                                     end) k incoll)) l0); simpl in *.
          unfold to_partitions in *.
          simpl in *.
          destruct (group_to_partitions g (a, l)); simpl in *; try congruence.
          destruct (lift_map (group_to_partitions g) l3); simpl in *; try congruence.
          reflexivity.
    Qed.

    Lemma group_by_table_correct
          (g:string) (sl:list string)
          (incoll :list data):
      match
        olift (fun d1 : data => rondcoll bdistinct d1)
              (lift dcoll
                    (lift_map
                       (fun d1 : data =>
                          match d1 with
                          | dunit => None
                          | dnat _ => None
                          | dfloat _ => None
                          | dbool _ => None
                          | dstring _ => None
                          | dcoll _ => None
                          | drec r => Some (drec (rproject r sl))
                          | dleft _ => None
                          | dright _ => None
                          | dbrand _ _ => None
                          | dforeign _ => None
                          end) incoll))
      with
      | Some dunit => None
      | Some (dnat _) => None
      | Some (dfloat _) => None
      | Some (dbool _) => None
      | Some (dstring _) => None
      | Some (dcoll c1) =>
        lift dcoll
             (lift_map
                (fun d1 : data =>
                   olift2
                     (fun d0 d2 : data =>
                        match d0 with
                        | dunit => None
                        | dnat _ => None
                        | dfloat _ => None
                        | dbool _ => None
                        | dstring _ => None
                        | dcoll _ => None
                        | drec r1 =>
                          match d2 with
                          | dunit => None
                          | dnat _ => None
                          | dfloat _ => None
                          | dbool _ => None
                          | dstring _ => None
                          | dcoll _ => None
                          | drec r2 => Some (drec (rec_concat_sort r1 r2))
                          | dleft _ => None
                          | dright _ => None
                          | dbrand _ _ => None
                          | dforeign _ => None
                          end
                        | dleft _ => None
                        | dright _ => None
                        | dbrand _ _ => None
                        | dforeign _ => None
                        end)
                     (Some d1) 
                     (olift (fun d0 : data => Some (drec ((g, d0) :: nil)))
                            (olift
                               (fun d0 : data =>
                                  lift_oncoll
                                    (fun l : list data => lift dcoll (oflatten l)) d0)
                               (lift dcoll
                                     (lift_map
                                        (fun d0 : data =>
                                           olift
                                             (fun d2 : data =>
                                                match d2 with
                                                | dunit => None
                                                | dnat _ => None
                                                | dfloat _ => None
                                                | dbool true => Some (dcoll (d0 :: nil))
                                                | dbool false => Some (dcoll nil)
                                                | dstring _ => None
                                                | dcoll _ => None
                                                | drec _ => None
                                                | dleft _ => None
                                                | dright _ => None
                                                | dbrand _ _ => None
                                                | dforeign _ => None
                                                end)
                                             (olift2
                                                (fun d2 d3 : data =>
                                                   unbdata
                                                     (fun x y : data =>
                                                        if data_eq_dec x y
                                                        then true
                                                        else false) d2 d3)
                                                match d0 with
                                                | dunit => None
                                                | dnat _ => None
                                                | dfloat _ => None
                                                | dbool _ => None
                                                | dstring _ => None
                                                | dcoll _ => None
                                                | drec r => Some (drec (rproject r sl))
                                                | dleft _ => None
                                                | dright _ => None
                                                | dbrand _ _ => None
                                                | dforeign _ => None
                                                end (Some d1))) incoll))))) c1)
      | Some (drec _) => None
      | Some (dleft _) => None
      | Some (dright _) => None
      | Some (dbrand _ _) => None
      | Some (dforeign _) => None
      | None => None
      end = lift dcoll (group_by_nested_eval_table g sl incoll).
    Proof.
      intros.
      unfold group_by_nested_eval_table.
      unfold group_by_nested_eval_keys_partition.
      unfold group_by_nested_eval.
      destruct ((lift_map
                   (fun d : data =>
                      match d with
                      | dunit => None
                      | dnat _ => None
                      | dfloat _ => None
                      | dbool _ => None
                      | dstring _ => None
                      | dcoll _ => None
                      | drec r => Some (drec (rproject r sl))
                      | dleft _ => None
                      | dright _ => None
                      | dbrand _ _ => None
                      | dforeign _ => None
                      end) incoll)); simpl in *; try congruence.
      destruct (bdistinct l); simpl in *; trivial.
      generalize (group_of_key_over_table_correct sl d incoll); intros Htest.
      case_eq (group_of_key
                 (fun d : data =>
                    match d with
                    | dunit => None
                    | dnat _ => None
                    | dfloat _ => None
                    | dbool _ => None
                    | dstring _ => None
                    | dcoll _ => None
                    | drec r => Some (drec (rproject r sl))
                    | dleft _ => None
                    | dright _ => None
                    | dbrand _ _ => None
                    | dforeign _ => None
                    end) d incoll); intros;
        rewrite H in *; simpl in *; try congruence.
      rewrite <- Htest. 
      simpl.
      case_eq (match d with
               | dunit => None
               | dnat _ => None
               | dfloat _ => None
               | dbool _ => None
               | dstring _ => None
               | dcoll _ => None
               | drec r2 =>
                 Some
                   (drec
                      (rec_concat_sort r2 [(g, dcoll l1)]))
               | dleft _ => None
               | dright _ => None
               | dbrand _ _ => None
               | dforeign _ => None
               end); intros.
      - destruct d; simpl in *; try congruence.
        invcs H0.
        clear Htest H.
        rewrite (groupby_test_lemma l0 g sl l1 l2 incoll).
        unfold lift.
        destruct (lift_map
                    (fun k : data =>
                       olift (fun group : list data => Some (k, group))
                             (group_of_key
                                (fun d : data =>
                                   match d with
                                   | dunit => None
                                   | dnat _ => None
                                   | dfloat _ => None
                                   | dbool _ => None
                                   | dstring _ => None
                                   | dcoll _ => None
                                   | drec r => Some (drec (rproject r sl))
                                   | dleft _ => None
                                   | dright _ => None
                                   | dbrand _ _ => None
                                   | dforeign _ => None
                                   end) k incoll)) l0); simpl in *; trivial.
      - generalize (group_of_key_destruct_drec_inv g sl d l0 l1 incoll H0); intros.
        rewrite H1; trivial.
      - rewrite <- Htest; simpl; trivial.
    Qed.
    
    Lemma group_by_table_correct_some
          (g:string) (sl:list string)
          (incoll outcoll:list data):
      group_by_nested_eval_table g sl incoll = Some outcoll -> 
      match
        olift (fun d1 : data => rondcoll bdistinct d1)
              (lift dcoll
                    (lift_map
                       (fun d1 : data =>
                          match d1 with
                          | dunit => None
                          | dnat _ => None
                          | dfloat _ => None
                          | dbool _ => None
                          | dstring _ => None
                          | dcoll _ => None
                          | drec r => Some (drec (rproject r sl))
                          | dleft _ => None
                          | dright _ => None
                          | dbrand _ _ => None
                          | dforeign _ => None
                          end) incoll))
      with
      | Some dunit => None
      | Some (dnat _) => None
      | Some (dfloat _) => None
      | Some (dbool _) => None
      | Some (dstring _) => None
      | Some (dcoll c1) =>
        lift dcoll
             (lift_map
                (fun d1 : data =>
                   olift2
                     (fun d0 d2 : data =>
                        match d0 with
                        | dunit => None
                        | dnat _ => None
                        | dfloat _ => None
                        | dbool _ => None
                        | dstring _ => None
                        | dcoll _ => None
                        | drec r1 =>
                          match d2 with
                          | dunit => None
                          | dnat _ => None
                          | dfloat _ => None
                          | dbool _ => None
                          | dstring _ => None
                          | dcoll _ => None
                          | drec r2 => Some (drec (rec_concat_sort r1 r2))
                          | dleft _ => None
                          | dright _ => None
                          | dbrand _ _ => None
                          | dforeign _ => None
                          end
                        | dleft _ => None
                        | dright _ => None
                        | dbrand _ _ => None
                        | dforeign _ => None
                        end)
                     (Some d1) 
                     (olift (fun d0 : data => Some (drec ((g, d0) :: nil)))
                            (olift
                               (fun d0 : data =>
                                  lift_oncoll
                                    (fun l : list data => lift dcoll (oflatten l)) d0)
                               (lift dcoll
                                     (lift_map
                                        (fun d0 : data =>
                                           olift
                                             (fun d2 : data =>
                                                match d2 with
                                                | dunit => None
                                                | dnat _ => None
                                                | dfloat _ => None
                                                | dbool true => Some (dcoll (d0 :: nil))
                                                | dbool false => Some (dcoll nil)
                                                | dstring _ => None
                                                | dcoll _ => None
                                                | drec _ => None
                                                | dleft _ => None
                                                | dright _ => None
                                                | dbrand _ _ => None
                                                | dforeign _ => None
                                                end)
                                             (olift2
                                                (fun d2 d3 : data =>
                                                   unbdata
                                                     (fun x y : data =>
                                                        if data_eq_dec x y
                                                        then true
                                                        else false) d2 d3)
                                                match d0 with
                                                | dunit => None
                                                | dnat _ => None
                                                | dfloat _ => None
                                                | dbool _ => None
                                                | dstring _ => None
                                                | dcoll _ => None
                                                | drec r => Some (drec (rproject r sl))
                                                | dleft _ => None
                                                | dright _ => None
                                                | dbrand _ _ => None
                                                | dforeign _ => None
                                                end (Some d1))) incoll))))) c1)
      | Some (drec _) => None
      | Some (dleft _) => None
      | Some (dright _) => None
      | Some (dbrand _ _) => None
      | Some (dforeign _) => None
      | None => None
      end = Some (dcoll outcoll).
    Proof.
      intros eqq1.
      generalize (group_by_table_correct g sl incoll).
      rewrite eqq1; simpl.
      trivial.
    Qed.

  End tableform.
  
  Section normalized.
    Context (h:brand_relation_t).

    Lemma bdistinct_normalized l :
      Forall (data_normalized h) l ->
      Forall (data_normalized h) (bdistinct l).
    Proof.
      intros dn.
      rewrite bdistinct_sublist; trivial.
    Qed.

    Lemma lift_map_rproject_normalized l l0 o :
      Forall (data_normalized h) l0 ->
      (lift_map
         (fun d : data =>
            match d with
            | dunit => None
            | dnat _ => None
            | dfloat _ => None
            | dbool _ => None
            | dstring _ => None
            | dcoll _ => None
            | drec r => Some (drec (rproject r l))
            | dleft _ => None
            | dright _ => None
            | dbrand _ _ => None
            | dforeign _ => None
            end) l0) = Some o ->
      Forall (data_normalized h) o.
    Proof.
      intros.
      eapply lift_map_Forall; eauto; intros.
      simpl in *.
      match_destr_in H1.
      invcs H1.
      invcs H2.
      constructor.
      - rewrite sublist_rproject; trivial.
      - eapply is_list_sorted_sublist; try apply H4.
        apply sublist_domain.
        apply sublist_rproject; trivial.
    Qed.

    Lemma group_of_key_normalized a l l1 l2 :
      Forall (data_normalized h) l1 ->
      group_of_key
        (fun d : data =>
           match d with
           | dunit => None
           | dnat _ => None
           | dfloat _ => None
           | dbool _ => None
           | dstring _ => None
           | dcoll _ => None
           | drec r => Some (drec (rproject r l))
           | dleft _ => None
           | dright _ => None
           | dbrand _ _ => None
           | dforeign _ => None
           end) a l1 = Some l2 ->
      Forall (data_normalized h) l2.
    Proof.
      intros dn eqq.
      unfold group_of_key.
      eapply lift_filter_Forall; eauto.
    Qed.      

    Lemma group_by_nested_eval_normalized l0 l o :
      Forall (data_normalized h) l0 ->
      (group_by_nested_eval
         (fun d : data =>
            match d with
            | dunit => None
            | dnat _ => None
            | dfloat _ => None
            | dbool _ => None
            | dstring _ => None
            | dcoll _ => None
            | drec r => Some (drec (rproject r l))
            | dleft _ => None
            | dright _ => None
            | dbrand _ _ => None
            | dforeign _ => None
            end) l0) = Some o ->
      Forall (fun dd => data_normalized h (fst dd)
                        /\ Forall (data_normalized h) (snd dd)) o.
    Proof.
      unfold group_by_nested_eval.
      intros dn eqq.
      unfold olift in eqq.
      match_case_in eqq; [intros ? eqq2 | intros eqq2]
      ; rewrite eqq2 in eqq; try discriminate.
      apply some_lift in eqq2
      ; destruct eqq2 as [d1 eqq2 d2].
      assert (dn1:Forall (data_normalized h) l1).
      { subst.
        apply bdistinct_Forall.
        eapply lift_map_rproject_normalized; eauto.
      } 
      clear d1 d2 eqq2.
      revert dn1 o eqq.
      induction l1; simpl; intros dn1 o eqq.
      - invcs eqq; constructor.
      - invcs dn1.
        match_case_in eqq; [intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqq; try discriminate.
        apply some_lift in eqq
        ; destruct eqq as [d1 eqq ?]; subst.
        specialize(IHl1 H2 _ eqq); clear eqq.
        constructor; trivial.
        match_case_in eqq2; [intros ? eqq3 | intros eqq3]
        ; rewrite eqq3 in eqq2; try discriminate.
        invcs eqq2.
        simpl.
        split; trivial.
        eapply group_of_key_normalized; try eapply eqq3.
        trivial.
    Qed.
    
    Lemma group_to_partitions_normalized s a d : 
      data_normalized h (fst a) ->
      Forall (data_normalized h) (snd a) ->
      group_to_partitions s a = Some d ->
      data_normalized h d.
    Proof.
      unfold group_to_partitions.
      intros dn1 dn2 eqq.
      destruct a as [d1 dl1]; unfold fst in *.
      destruct d1; try discriminate.
      simpl in eqq.
      invcs eqq.
      apply dnrec_sort.
      simpl in *.
      apply Forall_app; trivial.
      - invcs dn1; trivial.
      - constructor; simpl; trivial.
        constructor; trivial.
    Qed.

    Lemma group_by_nested_eval_keys_partition_normalized l0 s l o :
      data_normalized h (dcoll l0) ->
      lift dcoll
           (group_by_nested_eval_keys_partition
              s
              (fun d : data =>
                 match d with
                 | dunit => None
                 | dnat _ => None
                 | dfloat _ => None
                 | dbool _ => None
                 | dstring _ => None
                 | dcoll _ => None
                 | drec r => Some (drec (rproject r l))
                 | dleft _ => None
                 | dright _ => None
                 | dbrand _ _ => None
                 | dforeign _ => None
                 end) l0) = Some o
      -> data_normalized h o.
    Proof.
      unfold group_by_nested_eval_keys_partition, to_partitions.
      intros dn eqq.
      apply some_lift in eqq.
      destruct eqq as [d eqq ?]; subst.
      unfold olift in eqq.
      match_case_in eqq; [intros ? eqq2 | intros eqq2]
      ; rewrite eqq2 in eqq; try discriminate.
      invcs dn.
      generalize (group_by_nested_eval_normalized _ _ _ H0 eqq2); intros dn2.
      clear l0 eqq2 H0.
      revert dn2 d eqq.
      induction l1; intros dn2 d eqq.
      - invcs eqq.
        repeat constructor.
      - invcs dn2.
        specialize (IHl1 H2).
        simpl in *.
        match_case_in eqq; [intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqq; try discriminate.
        unfold lift in eqq.
        match_case_in eqq; [intros ? eqq3 | intros eqq3]
        ; rewrite eqq3 in eqq; try discriminate.
        invcs eqq.
        specialize (IHl1 _ eqq3).
        apply data_normalized_dcoll; split; trivial.
        destruct H1.
        eapply group_to_partitions_normalized; eauto.
    Qed.

    Lemma to_partitions_normalized g l o :
      Forall (fun l' => data_normalized h (fst l') /\ data_normalized h (dcoll (snd l'))) l ->
      to_partitions g l = Some o ->
      data_normalized h (dcoll o).
    Proof.
      unfold to_partitions; simpl.
      intros.
      constructor.
      eapply lift_map_Forall; try eassumption.
      intros.
      simpl in *.
      eapply group_to_partitions_normalized; eauto; intuition.
      invcs H4.
      rewrite Forall_forall in *; intuition.
    Qed.
    
    Lemma group_by_nested_eval_table_normalized s l l0 x :
      group_by_nested_eval_table s l l0 = Some x ->
      Forall (data_normalized h) l0 -> 
      data_normalized h (dcoll x).
    Proof.
      intros eqq dnl0.
      unfold group_by_nested_eval_table in eqq.
      unfold group_by_nested_eval_keys_partition in eqq.
      apply some_olift in eqq.
      destruct eqq as [?? eqq1].
      symmetry in eqq1.
      eapply to_partitions_normalized; try eassumption.
      generalize (group_by_nested_eval_normalized _ _ _ dnl0 e).
      repeat rewrite Forall_forall; intros.
      specialize (H _ H0); intuition.
      constructor; eauto.
    Qed.

  End normalized.

End GroupBy.

