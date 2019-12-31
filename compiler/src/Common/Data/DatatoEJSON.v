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

  Section toData.
    (* EJson to Data *)
    Fixpoint ejson_to_data (j:ejson) : data :=
      match j with
      | ejnull => dunit
      | ejnumber n => dfloat n
      | ejbigint n => dnat n
      | ejbool b => dbool b
      | ejstring s => dstring s
      | ejarray c => dcoll (map ejson_to_data c)
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

    Definition ejson_is_record (j:ejson) : option (list (string * ejson)) :=
      match j with
      | ejobject ((s1,j')::nil) =>
        if (string_dec s1 "$left") then None
        else if (string_dec s1 "$right") then None
             else Some ((s1,j')::nil)
      | ejobject ((s1,ejarray j1)::(s2,j2)::nil) =>
        if (string_dec s1 "$class") then
          if (string_dec s2 "$data") then
            match (ejson_brands j1) with
            | Some br => None
            | None => Some ((s1,ejarray j1)::(s2,j2)::nil)
            end
          else Some ((s1,ejarray j1)::(s2,j2)::nil)
        else Some ((s1,ejarray j1)::(s2,j2)::nil)
      | ejobject r => Some r
      | _ => None
      end.

    Lemma ejson_is_record_some (j:ejson) r :
      ejson_is_record j = Some r ->
      ejson_to_data j = drec (map (fun x => (json_key_decode (fst x), ejson_to_data (snd x))) r).
    Proof.
      intros.
      destruct j; simpl in *; try congruence.
      destruct l; simpl in *; try congruence; [inversion H; subst; reflexivity|].
      destruct p; simpl in *; try congruence.
      destruct e; simpl in *; try congruence;
      destruct l; simpl in *; try congruence;
        try (try (destruct (string_dec s "$left"); simpl in *; try congruence;
                  destruct (string_dec s "$right"); simpl in *; try congruence);
             inversion H; subst; reflexivity).
      destruct p; simpl in *; try congruence;
      destruct (string_dec s "$class"); simpl in *; try congruence;
      destruct (string_dec s0 "$data"); simpl in *; try congruence;
      destruct l; simpl in *; try congruence;
      destruct (ejson_brands l0); simpl in *; try congruence;
      inversion H; subst; try reflexivity.
    Qed.

    Lemma ejson_is_record_none (j:ejson) r :
      ejson_is_record j = None ->
      ejson_to_data j <> drec r.
    Proof.
      intros.
      destruct j; simpl in *; try congruence.
      destruct l; simpl in *; try congruence.
      destruct p; simpl in *; try congruence.
      destruct e; simpl in *; try congruence;
      destruct l; simpl in *; try congruence;
        try (try (destruct (string_dec s "$left"); simpl in *; try congruence;
                  destruct (string_dec s "$right"); simpl in *; try congruence);
             inversion H; subst; reflexivity).
      destruct p; simpl in *; try congruence;
      destruct (string_dec s "$class"); simpl in *; try congruence;
      destruct (string_dec s0 "$data"); simpl in *; try congruence;
      destruct l; simpl in *; try congruence;
      destruct (ejson_brands l0); simpl in *; try congruence;
      inversion H; subst; try reflexivity.
    Qed.

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

    Lemma ejson_record_of_record r :
      ejson_is_record (data_to_ejson (drec r)) =
      Some (map (fun x => (json_key_encode (fst x), data_to_ejson (snd x))) r).
    Proof.
      simpl.
      destruct r; simpl; try reflexivity.
      destruct p; simpl; try reflexivity.
      rewrite_string_dec_from_neq (json_key_encode_not_data s).
      rewrite_string_dec_from_neq (json_key_encode_not_class s).
      rewrite_string_dec_from_neq (json_key_encode_not_left s).
      rewrite_string_dec_from_neq (json_key_encode_not_right s).
      destruct d; simpl; try reflexivity; destruct r; simpl; try reflexivity.
      destruct r; simpl; try reflexivity.
    Qed.

  End toEJson.

  Section ModelRoundTrip.
    Lemma ejson_brands_map_ejstring b : ejson_brands (map ejstring b) = Some b.
    Proof.
      induction b; simpl; trivial.
      now rewrite IHb.
    Qed.

    Lemma data_to_ejson_idempotent d:
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

    Definition ejson_normalized j : Prop :=
      exists d, j = data_to_ejson d.
    Definition ejson_idempotent j : Prop :=
      data_to_ejson (ejson_to_data j) = j.

    Definition ejson_object_normalized (jl:list (string * ejson)) : Prop :=
      Forall (fun x => ejson_normalized (snd x)) jl.

    Lemma ejson_normalized_idempotent j:
      ejson_normalized j ->
      ejson_idempotent j.
    Proof.
      unfold ejson_normalized, ejson_idempotent.
      intros. elim H; intros; subst.
      rewrite data_to_ejson_idempotent; trivial.
    Qed.

  End ModelRoundTrip.

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

    Lemma ejson_to_data_jobj_nfloat l f : (ejson_to_data (ejobject l)) <> dfloat f.
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

    Lemma ejson_to_data_object_not_float l n:
      ~(ejson_to_data (ejobject l) = dfloat n).
    Proof.
      unfold ejson_to_data.
      apply ejson_to_data_jobj_nfloat.
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

    Lemma assoc_lookupr_json_key_encode_comm d s:
      match match d with
            | drec r => assoc_lookupr ODT_eqdec r s
            | _ => None
            end with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_is_record (data_to_ejson d) with
      | Some r => assoc_lookupr ODT_eqdec r (json_key_encode s)
      | None => None
      end.
    Proof.
      destruct d; try reflexivity.
      - rewrite ejson_record_of_record; simpl.
        induction l; simpl; [reflexivity|];
          destruct a; simpl.
        rewrite <- IHl; simpl; clear IHl.
        destruct (assoc_lookupr string_eqdec l s); try reflexivity.
        destruct (string_eqdec s s0);
          destruct (string_eqdec (json_key_encode s) (json_key_encode s0)); try reflexivity.
        + congruence.
        + destruct (string_eqdec (json_key_encode s) (json_key_encode s0)); try reflexivity;
          apply json_key_encode_diff in c; congruence.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl. rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    Lemma rremove_json_key_encode_comm d s:
      match
        match d with
        | drec r => Some (drec (rremove r s))
        | _ => None
        end
      with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_is_record (data_to_ejson d) with
      | Some r => Some (ejobject (rremove r (json_key_encode s)))
      | None => None
      end.
    Proof.
      destruct d; try reflexivity.
      - rewrite ejson_record_of_record; simpl; f_equal; f_equal.
        induction l; simpl; [reflexivity|];
          destruct a; simpl.
        destruct (string_dec s s0);
          destruct (string_dec (json_key_encode s) (json_key_encode s0)); subst.
        + assumption.
        + congruence.
        + apply json_key_encode_diff in n; congruence.
        + simpl; rewrite IHl; reflexivity.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl. rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    Lemma in_map_json_key_encode s pl:
      In s pl -> In (json_key_encode s) (map json_key_encode pl).
    Proof.
      apply in_map.
    Qed.

    Lemma in_map_json_key_encode_inv s pl:
      In (json_key_encode s) (map json_key_encode pl) -> In s pl.
    Proof.
      intros.
      induction pl; simpl in *; trivial.
      simpl in *.
      elim H; intros; clear H.
      - left; apply json_key_encode_inv; assumption.
      - auto.
    Qed.

    Lemma rproject_json_key_encode_comm d pl:
      match match d with
            | drec r => Some (drec (rproject r pl))
            | _ => None
            end with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_is_record (data_to_ejson d) with
      | Some r =>
        match match of_string_list (map ejstring (map json_key_encode pl)) with
              | Some a' => Some (rproject r a')
              | None => None
              end with
        | Some a' => Some (ejobject a')
        | None => None
        end
      | None => None
      end.
    Proof.
      destruct d; try reflexivity.
      - rewrite of_string_list_map_ejstring.
        rewrite ejson_record_of_record; simpl; f_equal; f_equal.
        induction l; simpl; [try reflexivity|];
          destruct a; simpl.
        destruct (in_dec string_dec s pl);
          destruct (in_dec string_dec (json_key_encode s) (map json_key_encode pl)); subst.
        + simpl; rewrite IHl; reflexivity.
        + apply in_map_json_key_encode in i; congruence.
        + apply in_map_json_key_encode_inv in i; congruence.
        + assumption.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl. rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    (* XXX Is this true? *)
    Lemma data_to_ejson_inv j1 j2:
      data_to_ejson j1 = data_to_ejson j2 -> j1 = j2.
    Proof.
      admit.
    Admitted.

    Lemma data_to_ejson_equiv j1 j2:
      data_to_ejson j1 = data_to_ejson j2 <-> j1 = j2.
    Proof.
      split; intros; subst.
      - apply data_to_ejson_inv; assumption.
      - reflexivity.
    Qed.

    Lemma mult_ejson_to_data a l :
      mult (bdistinct l) a =
      mult (map data_to_ejson (bdistinct l)) (data_to_ejson a).
    Proof.
      intros; revert a.
      induction l; [reflexivity|]; simpl; intros.
      rewrite IHl.
      destruct (mult (map data_to_ejson (bdistinct l)) (data_to_ejson a)); simpl.
      - repeat match_destr.
        + f_equal; apply IHl.
        + congruence.
        + unfold Equivalence.equiv, RelationClasses.complement in *.
          rewrite data_to_ejson_equiv in e; subst.
          congruence.
      - apply IHl.
    Qed.

    Lemma bdistinct_ejson_to_data_comm l :
      map data_to_ejson (bdistinct l) = bdistinct (map data_to_ejson l).
    Proof.
      induction l; [reflexivity|]; simpl in *.
      rewrite <- IHl; clear IHl.
      rewrite <- mult_ejson_to_data; simpl.
      destruct (mult (bdistinct l) a); reflexivity.
    Qed.

  End RuntimeLemmas.
End DatatoEJson.
