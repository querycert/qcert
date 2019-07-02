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

Require Import ZArith.
Require Import String.
Require Import List.
Require Import Utils.
Require Import ForeignData.
Require Import Data.

Section DataLift.

  Context {fdata:foreign_data}.

  Definition unbdbool (f:bool -> bool -> bool) (d1 d2:data) : option data :=
    match d1 with
    | dbool b1 =>
      match d2 with
      | dbool b2 => Some (dbool (f b1 b2))
      | _ => None
      end
    | _ => None
    end.

  Definition unudbool (f:bool -> bool) (d:data) : option data :=
    match d with
    | dbool b =>Some (dbool (f b))
    | _ => None
    end.

  Definition unbdnat (f:Z -> Z -> bool) (d1 d2:data) : option data :=
    match d1 with
    | dnat n1 =>
      match d2 with
      | dnat n2 => Some (dbool (f n1 n2))
      | _ => None
      end
    | _ => None
    end.

  Definition unbdata (f:data -> data -> bool) (d1 d2:data) : option data :=
    Some (dbool (f d1 d2)).

  Definition unndstring (f:string -> Z) (d1:data) : option data :=
    match d1 with
    | dstring s1 => (Some (dnat (f s1)))
    | _ => None
    end.

  Lemma unndstring_is_nat f d1 d2:
    unndstring f d1 = Some d2 -> exists z:Z, d2 = dnat z.
  Proof.
    intros.
    destruct d1; simpl in *; try congruence.
    exists (f s); inversion H; reflexivity.
  Qed.

  Definition unsdstring (f:string -> string -> string) (d1 d2:data) : option data :=
    match d1 with
    | dstring s1 =>
      match d2 with
      | dstring s2 => Some (dstring (f s1 s2))
      | _ => None
      end
    | _ => None
    end.

  Lemma unsdstring_is_string f d1 d2 d3:
    unsdstring f d1 d2 = Some d3 -> exists s:string, d3 = dstring s.
  Proof.
    intros.
    destruct d1; destruct d2; simpl in *; try congruence.
    exists (f s s0); inversion H; reflexivity.
  Qed.

  Definition ondcoll2 {A} : (list data -> list data -> A) -> data -> data -> option A.
  Proof.
    intros f d1 d2.
    destruct d1.
    exact None. exact None. exact None. exact None. exact None.
    2: exact None. 2: exact None.
    2: exact None. 2: exact None.
    destruct d2.
    exact None. exact None. exact None.
    exact None. exact None. 2: exact None. 2: exact None. 2: exact None. 2: exact None.
    exact (Some (f l l0)).
    exact None.
    exact None.
  Defined.

  Definition rondcoll2 (f:(list data -> list data -> list data)) (d1 d2:data) : option data :=
    lift dcoll (ondcoll2 f d1 d2).

  Definition ondstring {A} (f : string -> A) (d : data) :=
    match d with
    | dstring n => Some (f n)
    | _ => None
    end.

  Definition ondnat {A} (f : Z -> A) (d : data) :=
    match d with
    | dnat n => Some (f n)
    | _ => None
    end.

  Definition ondfloat {A} (f : float -> A) (d : data) :=
    match d with
    | dfloat n => Some (f n)
    | _ => None
    end.

  Definition ondcoll {A} (f : list data -> A) (d : data) :=
    match d with
    | dcoll l => Some (f l)
    | _ => None
    end.

    Definition lift_oncoll {A} (f : list data -> option A) (d : data) :=
      match d with
      | dcoll l => f l
      | _ => None
      end.

    Definition lift_ondcoll2 (f:list data -> list data -> option (list data)) (d1 d2:data) : option data :=
      match d1,d2 with
      | dcoll l1, dcoll l2 => lift dcoll (f l1 l2)
      | _,_ => None
      end.

    Lemma lift_oncoll_dcoll {A} (f : list data -> option A) (dl : list data) :
      lift_oncoll f (dcoll dl) = f dl.
    Proof.
      reflexivity.
    Qed.

    Lemma olift_on_lift_dcoll (f:list data->option data) (d1:option (list data)):
      olift (lift_oncoll f) (lift dcoll d1) =
      olift f d1.
    Proof.
      destruct d1; reflexivity.
    Qed.

    Lemma olift_lift_dcoll (f:list data -> option (list data)) (d1:option (list data)):
      olift (fun c1 : list data => lift dcoll (f c1)) d1 =
      lift dcoll (olift f d1).
    Proof.
      destruct d1; reflexivity.
    Qed.

    Lemma lift_dcoll_inversion d1 d2:
      d1 = d2 -> lift dcoll d1 = lift dcoll d2.
    Proof.
      intros; rewrite H; reflexivity.
    Qed.

    Definition rondcoll (f:list data -> list data) (d:data) : option data :=
      lift dcoll (ondcoll f d).

    Lemma lift_dcoll_cons d l1 l2 :
      lift dcoll l1 = lift dcoll l2 ->
      lift dcoll (lift (fun t => d :: t) l1) = lift dcoll (lift (fun t => d :: t) l2).
    Proof.
      intros.
      unfold lift in *.
      destruct l1; destruct l2; congruence.
    Qed.

    Lemma rondcoll2_dcoll f (l1 l2:list data):
      rondcoll2 f (dcoll l1) (dcoll l2) = Some (dcoll (f l1 l2)).
    Proof. reflexivity. Qed.
  
    Lemma rondcoll_dcoll f (l:list data):
      rondcoll f (dcoll l) = Some (dcoll (f l)).
    Proof. reflexivity. Qed.
  
    Lemma ondcoll_dcoll {A} (f:list data -> A) (l:list data):
      ondcoll f (dcoll l) = Some (f l).
    Proof. reflexivity. Qed.

    Lemma dcoll_map_app {A} (f:A -> data) (l1 l2:list A) :
      Some (dcoll (map f l1 ++ map f l2)) =
      rondcoll2 bunion (dcoll (map f l1)) (dcoll (map f l2)).
    Proof. reflexivity. Qed.

    Lemma lift_oncoll_ext {A : Type} (f g : list data -> option A) (d : data) :
      (forall a, d = dcoll a -> f a = g a) ->
      lift_oncoll f d = lift_oncoll g d.
    Proof.
      destruct d; simpl; auto.
    Qed.

End DataLift.

Hint Rewrite @rondcoll2_dcoll : alg.
Hint Rewrite @rondcoll_dcoll : alg.
Hint Rewrite @ondcoll_dcoll : alg.
Hint Rewrite @lift_oncoll_dcoll : alg.
Hint Rewrite @olift_on_lift_dcoll : alg.
Hint Rewrite @olift_lift_dcoll : alg.
Hint Rewrite @lift_map_id : alg.
Hint Rewrite @lift_map_map : alg.
Hint Rewrite @lift_dcoll_cons : alg.

