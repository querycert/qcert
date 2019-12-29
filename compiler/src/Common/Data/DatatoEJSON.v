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
Require Import Ascii.
Require Import ZArith.
Require Import Utils.
Require Import ForeignEJson.
Require Import EJson.
Require Import EJsonNorm.
Require Import ForeignData.
Require Import ForeignDataToEJson.
Require Import Data.

Section DatatoEJson.
  Context {fdata:foreign_data}.
  Context {ftoejson:foreign_ejson}.
  Context {fdatatoejson:foreign_to_ejson}.

  Section toData.
    (* EJson to Data *)

    Fixpoint ejson_brands (d:list ejson) : option (list string) :=
      match d with
      | nil => Some nil
      | (ejstring s1) :: d' =>
        match ejson_brands d' with
        | Some s' => Some (s1::s')
        | None => None
        end
      | _ => None
      end.

    Fixpoint ejson_bigints (d:list ejson) : option (list Z) :=
      match d with
      | nil => Some nil
      | (ejbigint z1) :: d' =>
        match ejson_bigints d' with
        | Some s' => Some (z1::s')
        | None => None
        end
      | _ => None
      end.

    Fixpoint ejson_to_data (j:ejson) : data :=
      match j with
      | ejnull => dunit
      | ejnumber n => dfloat n
      | ejbigint n => dnat n
      | ejbool b => dbool b
      | ejstring s => dstring s
      | ejarray c => dcoll (map ejson_to_data c)
      | ejobject nil => drec nil
      | ejobject ((s1,j')::nil) =>
        if (string_dec s1 "$left") then dleft (ejson_to_data j')
        else if (string_dec s1 "$right") then dright (ejson_to_data j')
             else drec ((json_key_decode s1, ejson_to_data j')::nil)
      | ejobject ((s1,ejarray j1)::(s2,j2)::nil) =>
        if (string_dec s1 "$class") then
          if (string_dec s2 "$data") then
            match (ejson_brands j1) with
            | Some br => dbrand br (ejson_to_data j2)
            | None => drec ((json_key_decode s1, dcoll (map ejson_to_data j1))::(json_key_decode s2, ejson_to_data j2)::nil)
            end
          else drec ((json_key_decode s1, dcoll (map ejson_to_data j1))::(json_key_decode s2, ejson_to_data j2)::nil)
        else drec ((json_key_decode s1, dcoll (map ejson_to_data j1))::(json_key_decode s2, ejson_to_data j2)::nil)
      | ejobject r => (drec (map (fun x => (json_key_decode (fst x), ejson_to_data (snd x))) r))
      | ejforeign fd => dforeign (foreign_to_ejson_to_data fd)
      end.

  End toData.

  Section toEJson.

    Definition Z_to_json (n: Z) : ejson :=
      ejbigint n.

    Fixpoint data_to_ejson (d:data) : ejson :=
      match d with
      | dunit => ejnull
      | dnat n => ejbigint n
      | dfloat n => ejnumber n
      | dbool b => ejbool b
      | dstring s => ejstring s
      | dcoll c => ejarray (map data_to_ejson c)
      | drec r => ejobject (map (fun x => (json_key_encode (fst x), data_to_ejson (snd x))) r)
      | dleft d' => ejobject (("$left"%string, data_to_ejson d')::nil)
      | dright d' => ejobject (("$right"%string, data_to_ejson d')::nil)
      | dbrand b d' =>
        ejobject (("$class"%string, ejarray (map ejstring b))::("$data"%string, (data_to_ejson d'))::nil)
      | dforeign fd => ejforeign (foreign_to_ejson_from_data fd)
      end.

  End toEJson.

End DatatoEJson.

Section ModelRoundTrip.
  Context {fdata:foreign_data}.
  Context {ftoejson:foreign_ejson}.
  Context {fdatatoejson:foreign_to_ejson}.

  Lemma ejson_brands_map_ejstring b : ejson_brands (map ejstring b) = Some b.
  Proof.
    induction b; simpl; trivial.
    now rewrite IHb.
  Qed.

  Lemma string_dec_from_neq {a b} (pf:a <> b) : exists pf2, string_dec a b = right pf2.
  Proof.
    destruct (string_dec a b); try congruence.
    eauto.
  Qed.

  Ltac rewrite_string_dec_from_neq H
    :=  let d := fresh "d" in
        let neq := fresh "neq" in
        destruct (string_dec_from_neq H) as [d neq]
        ; repeat rewrite neq in *
        ; clear d neq.

  Lemma json_to_data_to_json_idempotent d:
    ejson_to_data (data_to_ejson d) = d.
  Proof.
    induction d; simpl; trivial.
    - f_equal.
      repeat rewrite map_map.
      now apply map_eq_id.
    - destruct r; simpl; trivial.
      destruct p; simpl.
      rewrite_string_dec_from_neq (json_key_encode_not_data s).
      rewrite_string_dec_from_neq (json_key_encode_not_class s).
      rewrite_string_dec_from_neq (json_key_encode_not_left s).
      rewrite_string_dec_from_neq (json_key_encode_not_right s).
      assert (eq_simpl:
                (match data_to_ejson d with
                 | ejarray j1 =>
                   match map (fun x : string * data => (json_key_encode (fst x), data_to_ejson (snd x))) r with
                   | nil => drec ((json_key_decode (json_key_encode s), ejson_to_data (data_to_ejson d)) :: nil)
                   | (s2, j2) :: nil =>
                     drec
                       ((json_key_decode (json_key_encode s), dcoll (map ejson_to_data j1))
                          :: (json_key_decode s2, ejson_to_data j2) :: nil)
                   | (s2, j2) :: _ :: _ =>
                     drec
                       ((json_key_decode (json_key_encode s), ejson_to_data (data_to_ejson d))
                          :: map (fun x : string * ejson => (json_key_decode (fst x), ejson_to_data (snd x)))
                          (map (fun x : string * data => (json_key_encode (fst x), data_to_ejson (snd x))) r))
                   end
                 | _ =>
                   match map (fun x : string * data => (json_key_encode (fst x), data_to_ejson (snd x))) r with
                   | nil => drec ((json_key_decode (json_key_encode s), ejson_to_data (data_to_ejson d)) :: nil)
                   | _ :: _ =>
                     drec
                       ((json_key_decode (json_key_encode s), ejson_to_data (data_to_ejson d))
                          :: map (fun x : string * ejson => (json_key_decode (fst x), ejson_to_data (snd x)))
                          (map (fun x : string * data => (json_key_encode (fst x), data_to_ejson (snd x))) r))
                   end
                 end= drec ((json_key_decode (json_key_encode s), ejson_to_data (data_to_ejson d))::(map (fun x : string * ejson => (json_key_decode (fst x), ejson_to_data (snd x))) (map (fun x : string * data => (json_key_encode (fst x), data_to_ejson (snd x))) r))))).
      {
        destruct (data_to_ejson d); simpl
        ; destruct (map (fun x : string * data => (json_key_encode (fst x), data_to_ejson (snd x))) r      ); simpl; trivial
        ; destruct p
        ; destruct l; simpl; trivial
        ; destruct e; simpl; trivial
        ; destruct l0; simpl; trivial.
      }
      rewrite eq_simpl; clear eq_simpl.
      rewrite json_key_encode_decode.
      invcs H.
      simpl in *.
      rewrite H2.
      f_equal.
      f_equal.
      repeat rewrite map_map; simpl.
      f_equal.
      apply map_eq_id.
      revert H3.
      apply Forall_impl; intros.
      rewrite json_key_encode_decode.
      rewrite H; trivial.
      destruct a; reflexivity.
    - rewrite IHd.
      now destruct (data_to_ejson d).
    - rewrite IHd.
      now destruct (data_to_ejson d).
    - rewrite ejson_brands_map_ejstring.
      rewrite IHd.
      reflexivity.
    - rewrite foreign_to_ejson_to_data_to_ejson.
      reflexivity.
  Qed.

  Section RuntimeLemmas.
    Lemma ejson_to_data_jobj_nbool l b : (ejson_to_data (ejobject l)) <> dbool b.
    Proof.
      destruct l; simpl; try congruence.
      destruct p.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_jobj_nnat l n : (ejson_to_data (ejobject l)) <> dnat n.
    Proof.
      destruct l; simpl; try congruence.
      destruct p.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_jobj_nstring l s : (ejson_to_data (ejobject l)) <> dstring s.
    Proof.
      destruct l; simpl; try congruence.
      destruct p.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_jobj_ncoll l c : (ejson_to_data (ejobject l)) <> dcoll c.
    Proof.
      destruct l; simpl; try congruence.
      destruct p.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_object_not_boolean l b:
      ~(ejson_to_data (ejobject l) = dbool b).
    Proof.
      unfold ejson_to_data.
      apply ejson_to_data_jobj_nbool.
    Qed.

    Lemma ejson_to_data_object_not_nat l n:
      ~(ejson_to_data (ejobject l) = dnat n).
    Proof.
      unfold ejson_to_data.
      apply ejson_to_data_jobj_nnat.
    Qed.

    Lemma ejson_to_data_object_not_string l b:
      ~(ejson_to_data (ejobject l) = dstring b).
    Proof.
      unfold ejson_to_data.
      apply ejson_to_data_jobj_nstring.
    Qed.

    Lemma ejson_to_data_object_not_coll l j:
      ~(ejson_to_data (ejobject l) = dcoll j).
    Proof.
      unfold ejson_to_data.
      apply ejson_to_data_jobj_ncoll.
    Qed.

    Lemma rec_ejson_key_encode_roundtrip s i0:
      drec ((s, ejson_to_data i0)::nil) = ejson_to_data (ejobject ((json_key_encode s, i0)::nil)).
    Proof.
      unfold ejson_to_data; simpl.
      rewrite_string_dec_from_neq (json_key_encode_not_left s).
      rewrite_string_dec_from_neq (json_key_encode_not_right s).
      rewrite_string_dec_from_neq (json_key_encode_not_foreign s).
      rewrite json_key_encode_decode.
      now destruct i0.
    Qed.

    (* XXX Is this true? *)

    Lemma bdistinct_ejson_to_data_comm l:
      bdistinct (map ejson_to_data l) = map ejson_to_data (bdistinct l).
    Proof.
      admit.
    Admitted.

    (* XXX Some assumptions for the correctness of operators translation -- they do not hold as-is *)

    Lemma assoc_lookupr_json_key_encode_roundtrip l s:
      match ejson_to_data (ejobject l) with
      | drec r => assoc_lookupr ODT_eqdec r s
      | _ => None
      end =
      match assoc_lookupr ODT_eqdec l (json_key_encode s) with
      | Some a' => Some (ejson_to_data a')
      | None => None
      end.
    Proof.
      admit.
    Admitted.

    Lemma rremove_json_key_encode_roundtrip l s:
      match ejson_to_data (ejobject l) with
      | drec r => Some (drec (rremove r s))
      | _ => None
      end = Some (ejson_to_data (ejobject (rremove l (json_key_encode s)))).
    Proof.
      admit.
    Admitted.

  End RuntimeLemmas.
End ModelRoundTrip.
