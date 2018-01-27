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

(* Utils: key/value manipulation *)
Section CldMRUtil.
  Require Import String.
  Require Import List.
  Require Import Sorting.Mergesort.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.
  Require Import ZArith.
  Require Import Zdigits.
  Require Import Znat.

  Context {fruntime:foreign_runtime}.

  Definition pack_kv (k v:data) : data :=
    drec (("key"%string, k)::("value"%string, v)::nil).

  Definition pre_pack_kvl (kvl: list (data*data)) : list data :=
    List.map (fun x => pack_kv (fst x) (snd x)) kvl.
  
  Definition pack_kvl (kvl: list (data*data)) : data :=
    dcoll (pre_pack_kvl kvl).
  
  Definition pack_kv_id (v:data) : data :=
    pack_kv v v.
  
  Definition pack_kv_id_coll (v:data) : (data * list data) :=
    (v, (pack_kv v v)::nil).
  
  Definition pack_kv_const (index:string) (v:data) : data :=
    (pack_kv (dstring index) v).
  
  Definition pack_kvl_id (coll: list data) : list data :=
    List.map pack_kv_id coll.

  Definition pack_kvl_id_coll (coll:list data) : list (data * list data) :=
    List.map pack_kv_id_coll coll.
  
  Definition pack_kv_const_coll (index:string) (coll:list data) : list data :=
    List.map (pack_kv_const index) coll.
  
  Definition pack_kvl_const_coll (index:string) (coll: list data) : list (data * list data) :=
    (dstring index, List.map (pack_kv_const index) coll)::nil.
  
  Definition unpack_k (d:data) : option data :=
    match d with
    | drec r => edot r "key"%string
    | _ => None
    end.
  
  Definition unpack_v (d:data) : option data :=
    match d with
    | drec r => edot r "value"%string
    | _ => None
    end.

  Definition unpack_vl (coll: list data) : option (list data) :=
    lift_map unpack_v coll.

  Definition unpack_v_keep (d:data) : option (data * data) :=
    lift (fun x => (x,d)) (unpack_v d).

  Definition unpack_vl_keep (coll: list data) : option (list (data * data)) :=
    lift_map unpack_v_keep coll.

  Lemma pack_unpack_vl (coll: list data) :
    unpack_vl (pack_kvl_id coll) = Some coll.
  Proof.
    induction coll; try reflexivity; simpl.
    unfold unpack_vl in *.
    unfold pack_kv_id; simpl.
    rewrite IHcoll.
    reflexivity.
  Qed.
  
  Definition unpack_kv (d:data) : option (data * data) :=
    match unpack_k d with
    | None => None
    | Some k =>
      match unpack_v d with
      | None => None
      | Some v => Some (k,v)
      end
    end.

  Definition pre_unpack_kvl (coll: list data) : option (list (data * data)) :=
    lift_map unpack_kv coll.

  Definition unpack_kvl (d: data) : option (list (data * data)) :=
    match d with
    | dcoll coll => pre_unpack_kvl coll
    | _ => None
    end.

  Lemma pre_pack_pack_unpack_kvl_id (l: list (data*data)) :
    pre_unpack_kvl (pre_pack_kvl l) = Some l.
  Proof.
    induction l; simpl in *; try reflexivity.
    unfold pre_unpack_kvl in *; simpl in *.
    rewrite IHl.
    simpl.
    destruct a; reflexivity.
  Qed.
  
  Lemma pack_unpack_kvl_id (l: list (data*data)) :
    unpack_kvl (pack_kvl l) = Some l.
  Proof.
    simpl.
    apply pre_pack_pack_unpack_kvl_id.
  Qed.
  
  Definition cld_get_values (kvs: list (data * data)) : list data :=
    List.map snd kvs.

  Definition unbox_nat (d:data) : option nat :=
    match d with
    | dnat z => Some (Z.to_nat z)
    | _ => None
    end.

  Definition unbox_key (key: data) : option (list nat) :=
    match key with
    | dcoll coll => lift_map unbox_nat coll
    | _ => None
    end.

  Definition box_nat (n:nat) : data := (dnat (Z.of_nat n)).

  Lemma map_unbox_box_nat (nl:list nat) :
    lift_map unbox_nat (map box_nat nl) = Some nl.
  Proof.
    induction nl; simpl.
    - reflexivity.
    - rewrite IHnl; simpl.
      rewrite Nat2Z.id.
      reflexivity.
  Qed.
  
  Definition box_key (nl:list nat) : data := (dcoll (List.map box_nat nl)).

  Lemma box_unbox_key (nl: list nat) : (unbox_key (box_key nl)) = Some nl.
  Proof.
    induction nl.
    reflexivity.
    simpl in *.
    rewrite IHnl; simpl.
    rewrite Nat2Z.id.
    reflexivity.
  Qed.

  Definition make_invent_key (index:nat) (d:data) : option data :=
    match unbox_key d with
    | None => None
    | Some nl => Some (box_key (index::nl))
    end.

  Definition key_fun : Type := nat -> data -> option data.
  Definition map_id_key : key_fun := fun (i:nat) (d:data) => Some d.
  Definition map_const_key (n:nat) : key_fun := fun (i:nat) (d:data) => Some (box_key (n::nil)).
  Definition map_invent_key : key_fun := fun (i:nat) (d:data) => make_invent_key i d.
  
  Fixpoint lift_map_index_rec {A B} (i:nat) (f: nat -> A -> option B) (l:list A) : option (list B) :=
    match l with
      | nil => Some nil
      | x :: t =>
        match f i x with
          | None => None
          | Some x' =>
            lift (fun t' => x' :: t') (lift_map_index_rec (S i) f t)
        end
    end.

  Definition lift_map_index {A B} (f: nat -> A -> option B) (l:list A) : option (list B) :=
    lift_map_index_rec O f l.

  Definition keys_one_map_kv
             (compute_key:key_fun) (i:nat) (k:data) (x:data) : option (data * data) :=
    match compute_key i k with
    | None => None
    | Some newk => Some (newk, x)
    end.
  
  Fixpoint map_without_key (compute_key:key_fun) (coll:list data) : option (list (data * data)) :=
    lift_map_index (fun i x => keys_one_map_kv compute_key i (box_key nil) x) coll.

  Fixpoint flat_map_with_key (compute_key:key_fun) (coll:list (data * data)) : option (list (data * data)) :=
    lift_flat_map (fun x =>
                     match x with
                     | (k, dcoll y) => lift_map_index (fun i x => keys_one_map_kv compute_key i k x) y
                     | _ => None
                     end) coll.

  Fixpoint flat_map_without_key (coll:list data) : option (list data) :=
    oflatten coll.

  (* Used to initialize the keys on the input collection *)
  
  Fixpoint init_keys_aux (prefix:list nat) (index:nat) (coll: list data) : (list (data*data)) :=
    match coll with
    | nil => nil
    | d :: coll' =>
      (box_key (index::prefix), d) :: (init_keys_aux prefix (S index) coll')
    end.

  Definition init_keys (coll:list data) : list (data*data) := init_keys_aux nil O coll.

  Definition prefixed_init_keys (prefix:list nat) (coll:list data) : list (data*data) := init_keys_aux prefix O coll.

  Lemma init_like_first_map_index (prefix:nat) (coll : list data) :
    lift_map_index
      (fun (i : nat) (x : data) => keys_one_map_kv map_invent_key i (box_key (prefix::nil)) x)
      coll
    = Some (prefixed_init_keys (prefix::nil) coll).
  Proof.
    unfold lift_map_index; simpl.
    unfold prefixed_init_keys; simpl.
    generalize 0;
      induction coll; intros; try reflexivity; simpl.
    rewrite Nat2Z.id; simpl.
    rewrite (IHcoll (S n)); simpl; clear IHcoll.
    reflexivity.
  Qed.
  
  (* Removing the keys on the initialized input yields the input *)
  
  Lemma get_values_of_init_aux_same (prefix:list nat) (n:nat) (coll:list data) :
    cld_get_values (init_keys_aux prefix n coll) = coll.
  Proof.
    revert n; induction coll; try reflexivity; intros.
    simpl in *.
    unfold init_keys in *.
    rewrite (IHcoll (S n)).
    reflexivity.
  Qed.

  Lemma get_values_of_init_same (coll:list data) :
    cld_get_values (init_keys coll) = coll.
  Proof.
    unfold init_keys.
    apply get_values_of_init_aux_same.
  Qed.

  Lemma get_values_of_prefixed_init_same (prefix:list nat) (coll:list data) :
    cld_get_values (prefixed_init_keys prefix coll) = coll.
  Proof.
    unfold prefixed_init_keys.
    apply get_values_of_init_aux_same.
  Qed.
    
End CldMRUtil.

