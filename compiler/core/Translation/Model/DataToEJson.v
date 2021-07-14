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
Require Import Ascii.
Require Import ZArith.
Require Import Utils.
Require Import DataRuntime.
Require Import EJsonRuntime.
Require Import ForeignDataToEJson.

Section DataToEJson.
  Context {fruntime:foreign_runtime}.
  Context {fejson:foreign_ejson}.
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
             else drec ((key_decode s1, ejson_to_data j')::nil)
      | ejobject ((s1,ejarray j1)::(s2,j2)::nil) =>
        if (string_dec s1 "$class") then
          if (string_dec s2 "$data") then
            match (ejson_brands j1) with
            | Some br => dbrand br (ejson_to_data j2)
            | None => drec ((key_decode s1, dcoll (map ejson_to_data j1))::(key_decode s2, ejson_to_data j2)::nil)
            end
          else drec ((key_decode s1, dcoll (map ejson_to_data j1))::(key_decode s2, ejson_to_data j2)::nil)
        else drec ((key_decode s1, dcoll (map ejson_to_data j1))::(key_decode s2, ejson_to_data j2)::nil)
      | ejobject r => (drec (map (fun x => (key_decode (fst x), ejson_to_data (snd x))) r))
      | ejforeign fd => dforeign (foreign_to_ejson_to_data fd)
      end.

    Lemma ejson_is_record_some (j:ejson) r :
      ejson_is_record j = Some r ->
      ejson_to_data j = drec (map (fun x => (key_decode (fst x), ejson_to_data (snd x))) r).
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

    Lemma ejson_is_record_none (j:ejson):
      ejson_is_record j = None ->
      (forall r, ejson_to_data j <> drec r).
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

    Lemma ejson_is_either_some_left (j:ejson) jl :
      ejson_is_either j = Some (Some jl, None) ->
      ejson_to_data j = dleft (ejson_to_data jl).
    Proof.
      intros; destruct j; simpl in *; try congruence.
      destruct l; simpl in *; try congruence;
        destruct p; simpl in *; try congruence;
          destruct l; simpl in *; try congruence.
      destruct (string_dec s "$left"); simpl in *; try congruence;
        destruct (string_dec s "$right"); simpl in *; try congruence; subst.
      inversion H; subst.
      destruct jl; reflexivity.
    Qed.

    Lemma ejson_is_either_some_right (j:ejson) jr :
      ejson_is_either j = Some (None, Some jr) ->
      ejson_to_data j = dright (ejson_to_data jr).
    Proof.
      intros; destruct j; simpl in *; try congruence.
      destruct l; simpl in *; try congruence;
        destruct p; simpl in *; try congruence;
          destruct l; simpl in *; try congruence.
      destruct (string_dec s "$left"); simpl in *; try congruence;
        destruct (string_dec s "$right"); simpl in *; try congruence; subst.
      inversion H; subst.
      destruct jr; reflexivity.
    Qed.
      
    Lemma ejson_is_either_none (j:ejson) :
      ejson_is_either j = None ->
      (forall jl jr, ejson_to_data j <> dleft jl /\ ejson_to_data j <> dright jr).
    Proof.
      intros; split; intros;
      destruct j; simpl in *; try congruence;
        destruct l; simpl in *; try congruence;
          destruct p; simpl in *; try congruence;
            destruct l; simpl in *; try congruence;
              destruct (string_dec s "$left"); simpl in *; try congruence;
                destruct (string_dec s "$right"); simpl in *; try congruence; subst;
                  try (destruct e; try congruence);
                  destruct p; try congruence;
                    destruct e; try congruence;
                      destruct l; try congruence;
                        repeat match_destr.
    Qed.

  End toData.

  Section toEJson.

    Fixpoint data_to_ejson (d:data) : ejson :=
      match d with
      | dunit => ejnull
      | dnat n => ejbigint n
      | dfloat n => ejnumber n
      | dbool b => ejbool b
      | dstring s => ejstring s
      | dcoll c => ejarray (map data_to_ejson c)
      | drec r => ejobject (map (fun x => (key_encode (fst x), data_to_ejson (snd x))) r)
      | dleft d' => ejobject (("$left"%string, data_to_ejson d')::nil)
      | dright d' => ejobject (("$right"%string, data_to_ejson d')::nil)
      | dbrand b d' =>
        ejobject (("$class"%string, ejarray (map ejstring b))::("$data"%string, (data_to_ejson d'))::nil)
      | dforeign fd => ejforeign (foreign_to_ejson_from_data fd)
      end.

    Lemma data_to_ejson_on_drec r:
      data_to_ejson (drec (rec_sort r))
      = ejobject (rec_sort (map (fun xy : string * data => (key_encode (fst xy), data_to_ejson (snd xy))) r)).
    Proof.
      simpl.
      rewrite map_rec_sort.
      reflexivity.
      intros.
      apply rec_field_lt_key_eq.
    Qed.

    Lemma ejson_record_of_record r :
      ejson_is_record (data_to_ejson (drec r)) =
      Some (map (fun x => (key_encode (fst x), data_to_ejson (snd x))) r).
    Proof.
      simpl.
      destruct r; simpl; try reflexivity.
      destruct p; simpl; try reflexivity.
      rewrite_string_dec_from_neq (key_encode_not_data s).
      rewrite_string_dec_from_neq (key_encode_not_class s).
      rewrite_string_dec_from_neq (key_encode_not_left s).
      rewrite_string_dec_from_neq (key_encode_not_right s).
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
        rewrite_string_dec_from_neq (key_encode_not_data s).
        rewrite_string_dec_from_neq (key_encode_not_class s).
        rewrite_string_dec_from_neq (key_encode_not_left s).
        rewrite_string_dec_from_neq (key_encode_not_right s).
        assert (eq_simpl:
                  (match data_to_ejson d with
                   | ejarray j1 =>
                     match map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) r with
                     | nil => drec ((key_decode (key_encode s), ejson_to_data (data_to_ejson d)) :: nil)
                     | (s2, j2) :: nil =>
                       drec
                         ((key_decode (key_encode s), dcoll (map ejson_to_data j1))
                            :: (key_decode s2, ejson_to_data j2) :: nil)
                     | (s2, j2) :: _ :: _ =>
                       drec
                         ((key_decode (key_encode s), ejson_to_data (data_to_ejson d))
                            :: map (fun x : string * ejson => (key_decode (fst x), ejson_to_data (snd x)))
                            (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) r))
                     end
                   | _ =>
                     match map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) r with
                     | nil => drec ((key_decode (key_encode s), ejson_to_data (data_to_ejson d)) :: nil)
                     | _ :: _ =>
                       drec
                         ((key_decode (key_encode s), ejson_to_data (data_to_ejson d))
                            :: map (fun x : string * ejson => (key_decode (fst x), ejson_to_data (snd x)))
                            (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) r))
                     end
                   end= drec ((key_decode (key_encode s), ejson_to_data (data_to_ejson d))::(map (fun x : string * ejson => (key_decode (fst x), ejson_to_data (snd x))) (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) r))))).
        {
          destruct (data_to_ejson d); simpl
          ; destruct (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) r      ); simpl; trivial
          ; destruct p
          ; destruct l; simpl; trivial
          ; destruct e; simpl; trivial
          ; destruct l0; simpl; trivial.
        }
        rewrite eq_simpl; clear eq_simpl.
        rewrite key_encode_decode.
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
        rewrite key_encode_decode.
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

    (* Means we can do inversion on data_to_ejson *)
    Lemma data_to_ejson_inj j1 j2:
      data_to_ejson j1 = data_to_ejson j2 -> j1 = j2.
    Proof.
      intros.
      rewrite <- (data_to_ejson_idempotent j1).
      rewrite <- (data_to_ejson_idempotent j2).
      rewrite H.
      reflexivity.
    Qed.

    Lemma data_to_ejson_equiv j1 j2:
      data_to_ejson j1 = data_to_ejson j2 <-> j1 = j2.
    Proof.
      split; intros; subst.
      - apply data_to_ejson_inj; assumption.
      - reflexivity.
    Qed.
  End ModelRoundTrip.

  Section RuntimeLemmas.
    (** Useful *)
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

    Lemma rec_ekey_encode_roundtrip s i0:
      drec ((s, ejson_to_data i0)::nil) = ejson_to_data (ejobject ((key_encode s, i0)::nil)).
    Proof.
      unfold ejson_to_data; simpl.
      rewrite_string_dec_from_neq (key_encode_not_left s).
      rewrite_string_dec_from_neq (key_encode_not_right s).
      rewrite_string_dec_from_neq (key_encode_not_foreign s).
      rewrite key_encode_decode.
      now destruct i0.
    Qed.

    (** For dot operator *)
    Lemma assoc_lookupr_key_encode_comm l s:
      match assoc_lookupr string_eqdec l s with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      assoc_lookupr
        string_eqdec (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l)
        (key_encode s).
    Proof.
      induction l; simpl; [reflexivity|];
        destruct a; simpl.
      rewrite <- IHl; simpl; clear IHl.
      destruct (assoc_lookupr string_eqdec l s); try reflexivity.
      destruct (string_eqdec s s0);
        destruct (string_eqdec (key_encode s) (key_encode s0)); try reflexivity.
      + congruence.
      + destruct (string_eqdec (key_encode s) (key_encode s0)); try reflexivity;
          apply key_encode_diff in c; congruence.
    Qed.

    Lemma edot_key_encode_comm d s:
      match match d with
            | drec r => assoc_lookupr ODT_eqdec r s
            | _ => None
            end with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_is_record (data_to_ejson d) with
      | Some r => assoc_lookupr ODT_eqdec r (key_encode s)
      | None => None
      end.
    Proof.
      destruct d; try reflexivity.
      - rewrite ejson_record_of_record; simpl.
        apply assoc_lookupr_key_encode_comm.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    (** For remove operator *)
    Lemma rremove_key_encode_comm d s:
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
      | Some r => Some (ejobject (rremove r (key_encode s)))
      | None => None
      end.
    Proof.
      destruct d; try reflexivity.
      - rewrite ejson_record_of_record; simpl; f_equal; f_equal.
        induction l; simpl; [reflexivity|];
          destruct a; simpl.
        destruct (string_dec s s0);
          destruct (string_dec (key_encode s) (key_encode s0)); subst.
        + assumption.
        + congruence.
        + apply key_encode_diff in n; congruence.
        + simpl; rewrite IHl; reflexivity.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    (** For project operator *)
    Lemma map_rproject_key_encode_correct l pl:
      map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) (rproject l pl) =
      rproject (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l) (map key_encode pl).
    Proof.
      induction l; simpl; [try reflexivity|];
        destruct a; simpl.
      destruct (in_dec string_dec s pl);
        destruct (in_dec string_dec (key_encode s) (map key_encode pl)); subst.
      + simpl; rewrite IHl; reflexivity.
      + apply in_map_key_encode in i; congruence.
      + apply in_map_key_encode_inv in i; congruence.
      + assumption.
    Qed.

    Lemma rproject_key_encode_comm d pl:
      match match d with
            | drec r => Some (drec (rproject r pl))
            | _ => None
            end with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_is_record (data_to_ejson d) with
      | Some r =>
        match match of_string_list (map ejstring (map key_encode pl)) with
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
        apply map_rproject_key_encode_correct.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl. rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    (** For distinct operator *)
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

    (** For flatten operator *)
    Lemma lift_flat_map_eobject_is_none l l' :
      lift_flat_map
        (fun x : data => match x with
                         | dcoll y => Some y
                         | _ => None
                         end)
        (map (fun x : ejson => ejson_to_data x) (ejobject l :: l')) = None.
    Proof.
      Opaque ejson_to_data.
      simpl; case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
      generalize (ejson_to_data_object_not_coll l l0); intros.
      contradiction.
      Transparent ejson_to_data.
    Qed.

    Lemma flat_map_jflatten_roundtrip l :
      match
        match lift_flat_map (fun x : data => match x with
                                             | dcoll y => Some y
                                             | _ => None
                                             end) l with
        | Some a' => Some (dcoll a')
        | None => None
        end
      with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match jflatten (map data_to_ejson l) with
      | Some a' => Some (ejarray a')
      | None => None
      end.
    Proof.
      induction l; [reflexivity|].
      destruct a; try reflexivity; simpl.
      unfold jflatten in *; simpl.
      destruct (lift_flat_map (fun x : data => match x with
                                               | dcoll y => Some y
                                               | _ => None
                                               end) l);
        destruct (lift_flat_map (fun x : ejson => match x with
                                                  | ejarray y => Some y
                                                  | _ => None
                                                  end) (map data_to_ejson l));
        simpl; try congruence.
      simpl in IHl.
      inversion IHl; clear IHl.
      subst.
      f_equal.
      f_equal.
      apply map_app.
    Qed.

    (** For brand-related operators *)
    Lemma ejson_to_data_jobj_nbrand s e b d: (ejson_to_data (ejobject ((s, e)::nil))) <> dbrand b d.
    Proof.
      simpl.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_jobj_nbrand_long s e p p0 l b d:
      (ejson_to_data (ejobject ((s, e) :: p :: p0 :: l))) <> dbrand b d.
    Proof.
      simpl.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_jobj_nbrand_no_data e s0 e0 b d:
      s0 <> "$data"%string ->
      ejson_to_data (ejobject (("$class"%string, e)::(s0, e0)::nil)) <> dbrand b d.
    Proof.
      intros; simpl.
      repeat match_destr; try congruence.
    Qed.
      
    Lemma ejson_to_data_jobj_nbrand_no_class e s e0 b d:
      s <> "$class"%string ->
      ejson_to_data (ejobject ((s, e)::("$data"%string, e0)::nil)) <> dbrand b d.
    Proof.
      intros; simpl.
      repeat match_destr; try congruence.
    Qed.

    Lemma ejson_to_data_jobj_nbrand_no_class_no_data s e s0 e0 b d:
      s <> "$class"%string ->
      s0 <> "$data"%string ->
      ejson_to_data (ejobject ((s, e)::(s0, e0)::nil)) <> dbrand b d.
    Proof.
      intros; simpl.
      repeat match_destr; try congruence.
    Qed.

    Lemma ejson_data_maybe_brand s s0 e e0 :
      match ejson_to_data (ejobject ((s, e)::(s0, e0)::nil)) with
      | dbrand _ d' => Some d'
      | _ => None
      end =
      match
        match e with
        | ejarray j1 =>
          if string_dec s "$class"
          then
            if string_dec s0 "$data"
            then match ejson_brands j1 with
                 | Some _ => Some e0
                 | None => None
                 end
            else None
          else None
        | _ => None
        end
      with
      | Some a' => Some (ejson_to_data a')
      | None => None
      end.
    Proof.
      case_eq (string_dec s "$class"); intros; subst;
      case_eq (string_dec s0 "$data"); intros; subst.
      - destruct e; simpl;
          try (destruct e0; simpl; reflexivity).
        destruct (ejson_brands l); reflexivity.
      - case_eq (ejson_to_data (ejobject (("$class"%string, e)::(s0, e0)::nil))); intros;
          try (destruct e; simpl; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_data e s0 e0 b d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject ((s, e)::("$data"%string, e0)::nil))); intros;
          try (destruct e; simpl; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class e s e0 b d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject ((s, e)::(s0, e0)::nil))); intros;
          try (destruct e; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class_no_data s e s0 e0 b d n n0);
          intros; contradiction.
    Qed.

    Lemma ejson_data_maybe_cast h b s s0 e e0 :
      match ejson_to_data (ejobject ((s, e)::(s0, e0)::nil)) with
      | dbrand b' _ =>
        if sub_brands_dec h b' b then Some (dsome (ejson_to_data (ejobject ((s, e)::(s0, e0)::nil)))) else Some dnone
      | _ => None
      end =
      match
        match e with
        | ejarray jl2 =>
          if string_dec s "$class"
          then
            if string_dec s0 "$data"
            then
              match ejson_brands jl2 with
              | Some b2 =>
                if sub_brands_dec h b2 b
                then Some (ejobject (("$left"%string, ejobject ((s, e)::(s0, e0)::nil))::nil))
                else Some (ejobject (("$right"%string, ejnull)::nil))
              | None => None
              end
            else None
          else None
        | _ => None
        end
      with
      | Some a' => Some (ejson_to_data a')
      | None => None
      end.
    Proof.
      case_eq (string_dec s "$class"); intros; subst;
      case_eq (string_dec s0 "$data"); intros; subst.
      - destruct e; simpl;
          try (destruct e0; simpl; reflexivity).
        case_eq (ejson_brands l); intros; [|reflexivity].
        destruct (sub_brands_dec h l0 b); [|reflexivity].
        f_equal; simpl; unfold dsome; f_equal.
        rewrite H1.
        reflexivity.
      - case_eq (ejson_to_data (ejobject (("$class"%string, e)::(s0, e0)::nil))); intros;
          try (destruct e; simpl; reflexivity).
          specialize (ejson_to_data_jobj_nbrand_no_data e s0 e0 b0 d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject ((s, e)::("$data"%string, e0)::nil))); intros;
          try (destruct e; simpl; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class e s e0 b0 d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject ((s, e)::(s0, e0)::nil))); intros;
          try (destruct e; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class_no_data s e s0 e0 b0 d n n0);
          intros; contradiction.
    Qed.

    (** Bag operators *)
    Lemma bunion_map_comm l l0:
      map data_to_ejson (bunion l l0) =
      bunion (map data_to_ejson l) (map data_to_ejson l0).
    Proof.
      unfold bunion.
      rewrite map_app.
      reflexivity.
    Qed.

    (** For record concatenation operator *)
    Lemma rec_concat_key_encode_comm l l0 :
      map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) (rec_sort (l ++ l0)) =
      rec_sort
        (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l ++
             map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l0).
    Proof.
      rewrite map_rec_sort.
      rewrite map_app.
      reflexivity.
      intros.
      apply rec_field_lt_key_eq.
    Qed.

    Lemma rconcat_key_encode_comm d d0:
      match
        match d with
        | drec r1 => match d0 with
                     | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                     | _ => None
                     end
        | _ => None
        end
      with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_is_record (data_to_ejson d) with
      | Some r1 =>
        match ejson_is_record (data_to_ejson d0) with
        | Some r2 => Some (ejobject (rec_sort (r1 ++ r2)))
        | None => None
        end
      | None => None
      end.
    Proof.
      destruct d; try reflexivity.
      - rewrite ejson_record_of_record; simpl.
        destruct d0; try reflexivity.
        + rewrite ejson_record_of_record; simpl.
          f_equal. f_equal.
          apply rec_concat_key_encode_comm.
        + destruct d0; reflexivity.
        + destruct d0; reflexivity.
        + simpl; rewrite ejson_brands_map_ejstring; reflexivity.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.
    
    (** For record merge operator *)
    Lemma compatible_with_key_encode_comm s d l:
      compatible_with s d l =
      compatible_with (key_encode s) (data_to_ejson d)
                      (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l).
    Proof.
      unfold compatible_with in *; simpl.
      rewrite <- assoc_lookupr_key_encode_comm.
      unfold EquivDec.equiv_dec in *.
      destruct (assoc_lookupr string_eqdec l s); try reflexivity.
      case_eq (data_eqdec d d0); case_eq (ejson_eqdec (data_to_ejson d) (data_to_ejson d0)); intros.
      - reflexivity.
      - congruence.
      - clear H; apply data_to_ejson_inj in e.
        congruence.
      - reflexivity.
    Qed.

    Lemma compatible_key_encode_comm l l0:
      Compat.compatible l l0
      = Compat.compatible (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l)
                          (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l0).
    Proof.
      unfold Compat.compatible.
      induction l; [reflexivity|]; simpl.
      rewrite <- IHl; clear IHl.
      destruct a; simpl.
      rewrite <- compatible_with_key_encode_comm.
      reflexivity.
    Qed.

    Lemma merge_bindings_key_encode_comm l l0 :
      lift
        (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))))
        (merge_bindings l l0) =
      merge_bindings (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l)
                     (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) l0).
    Proof.
      unfold lift; simpl.
      unfold merge_bindings.
      rewrite <- compatible_key_encode_comm.
      destruct (Compat.compatible l l0); try reflexivity.
      unfold rec_concat_sort.
      rewrite rec_concat_key_encode_comm; reflexivity.
    Qed.

    Lemma rmerge_key_encode_comm d d0:
      match
        match d with
        | drec r1 =>
          match d0 with
          | drec r2 =>
            match merge_bindings r1 r2 with
            | Some x => Some (dcoll (drec x::nil))
            | None => Some (dcoll nil)
            end
          | _ => None
          end
        | _ => None
        end
      with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_is_record (data_to_ejson d) with
      | Some r1 =>
        match ejson_is_record (data_to_ejson d0) with
        | Some r2 =>
          match merge_bindings r1 r2 with
          | Some x => Some (ejarray (ejobject x::nil))
          | None => Some (ejarray nil)
          end
        | None => None
        end
      | None => None
      end.
    Proof.
      destruct d; try reflexivity.
      - rewrite ejson_record_of_record; simpl.
        destruct d0; try reflexivity.
        + rewrite ejson_record_of_record; simpl.
          f_equal. f_equal.
          rewrite <- merge_bindings_key_encode_comm.
          destruct (merge_bindings l l0); reflexivity.
        + destruct d0; reflexivity.
        + destruct d0; reflexivity.
        + simpl; rewrite ejson_brands_map_ejstring; reflexivity.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.
      
    (** For nth operator *)
    Lemma nth_error_to_ejson_comm l n:
      lift data_to_ejson (nth_error l n)
      = nth_error (map data_to_ejson l) n.
    Proof.
      revert l.
      induction n; simpl; try reflexivity; intros.
      - destruct l; reflexivity.
      - unfold lift in *.
        destruct l; try reflexivity.
        rewrite IHn; reflexivity.
    Qed.

    (** For contains operator *)
    Lemma in_data_to_ejson_comm d l:
      In (data_to_ejson d) (map data_to_ejson l) <-> In d l.
    Proof.
      split; intros.
      - rewrite in_map_iff in H.
        elim H; clear H; intros.
        elim H; clear H; intros.
        apply data_to_ejson_inj in H.
        subst; assumption.
      - apply in_map; assumption.
    Qed.

    (** For bag union operator *)
    Lemma bunion_ejson_to_data_comm l1 l2:
      map data_to_ejson (bunion l1 l2) = bunion (map data_to_ejson l1) (map data_to_ejson l2).
    Proof.
      unfold bunion.
      rewrite map_app.
      reflexivity.
    Qed.

    (** For bag minus operator *)
    Lemma remove_one_ejson_to_data_comm d l:
      map data_to_ejson (remove_one d l) = remove_one (data_to_ejson d) (map data_to_ejson l).
    Proof.
      induction l; [reflexivity|]; simpl.
      rewrite <- IHl; clear IHl.
      destruct (EquivDec.equiv_dec d a);
        destruct (EquivDec.equiv_dec (data_to_ejson d) (data_to_ejson a));
        try reflexivity; simpl.
      - rewrite e in c; congruence.
      - apply data_to_ejson_inj in e; subst; congruence.
    Qed.

    Lemma bminus_ejson_to_data_comm l1 l2:
      map data_to_ejson (bminus l1 l2) = bminus (map data_to_ejson l1) (map data_to_ejson l2).
    Proof.
      revert l2; induction l1; simpl in *; intros; [reflexivity|].
      rewrite IHl1.
      rewrite remove_one_ejson_to_data_comm; reflexivity.
    Qed.
    
    (** For bag min operator *)
    Lemma bmin_ejson_to_data_comm l1 l2:
      map data_to_ejson (bmin l1 l2) = bmin (map data_to_ejson l1) (map data_to_ejson l2).
    Proof.
      unfold bmin.
      rewrite bminus_ejson_to_data_comm.
      rewrite bminus_ejson_to_data_comm.
      reflexivity.
    Qed.
    
    (** For bag max operator *)
    Lemma bmax_ejson_to_data_comm l1 l2:
      map data_to_ejson (bmax l1 l2) = bmax (map data_to_ejson l1) (map data_to_ejson l2).
    Proof.
      unfold bmax.
      rewrite bunion_ejson_to_data_comm.
      rewrite bminus_ejson_to_data_comm.
      reflexivity.
    Qed.

    (** For groupby *)
    Definition data_to_ejson_partition (l:list (data * list data)) : list (ejson * list ejson) :=
      (map (fun xy => (data_to_ejson (fst xy),
                       (map data_to_ejson (snd xy))))) l.

    Lemma ejson_lift_map_rproject_correct kl l:
      lift (map data_to_ejson)
           (lift_map (fun d : data => match d with
                                      | drec r => Some (drec (rproject r kl))
                                      | _ => None
                                      end) l)
      =
      lift_map
        (fun d : ejson =>
           match ejson_is_record d with
           | Some r => Some (ejobject (rproject r (map key_encode kl)))
           | None => None
           end) (map data_to_ejson l).
    Proof.
      induction l; try reflexivity; unfold lift in *; simpl in *.
      rewrite <- IHl; clear IHl.
      destruct (lift_map (fun d : data => match d with
                                    | drec r => Some (drec (rproject r kl))
                                    | _ => None
                                          end) l); try reflexivity.
      destruct a; try reflexivity.
      rewrite ejson_record_of_record; simpl.
      - f_equal; f_equal; f_equal.
        apply map_rproject_key_encode_correct.
      - destruct a; reflexivity.
      - destruct a; reflexivity.
      - simpl; rewrite ejson_brands_map_ejstring; reflexivity.
      - destruct a; try reflexivity;
        try (rewrite ejson_record_of_record; try reflexivity).
        + destruct a; reflexivity.
        + destruct a; reflexivity.
        + simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    Lemma data_to_ejson_drec_inv  kl l:
      ejobject (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) (rproject l kl))
      = data_to_ejson (drec (rproject l kl)).
    Proof.
      reflexivity.
    Qed.

    Lemma ejson_key_is_eq_r_correct kl a a0:
      (key_is_eq_r (fun d : data => match d with
                                    | drec r => Some (drec (rproject r kl))
                                    | _ => None
                                    end) a0 a)
      =
      ejson_key_is_eq_r
        (fun j : ejson =>
           match ejson_is_record j with
           | Some r => Some (ejobject (rproject r (map key_encode kl)))
           | None => None
           end) (data_to_ejson a0) (data_to_ejson a).
    Proof.
      unfold key_is_eq_r.
      unfold ejson_key_is_eq_r.
      destruct a0; try reflexivity.
      - rewrite ejson_record_of_record.
        rewrite <- map_rproject_key_encode_correct.
        unfold olift2.
        rewrite data_to_ejson_drec_inv.
        generalize (drec (rproject l kl)); intros.
        case_eq (data_eq_dec d a);
          case_eq (ejson_eq_dec (data_to_ejson d) (data_to_ejson a)); intros; try congruence.
        clear H.
        apply data_to_ejson_inj in e.
        subst. congruence.
      - simpl; destruct (data_to_ejson a0); try reflexivity.
      - simpl; destruct (data_to_ejson a0); try reflexivity.
      - simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    Lemma ejson_group_of_key_correct kl a l1:
      lift (map data_to_ejson)
           (group_of_key (fun d : data => match d with
                                          | drec r => Some (drec (rproject r kl))
                                          | _ => None
                                          end) a l1) =
      ejson_group_of_key
        (fun j : ejson =>
           match ejson_is_record j with
           | Some r => Some (ejobject (rproject r (map key_encode kl)))
           | None => None
           end) (data_to_ejson a) (map data_to_ejson l1).
    Proof.
      unfold group_of_key.
      unfold ejson_group_of_key.
      unfold lift; simpl.
      induction l1; try reflexivity; simpl in *.
      rewrite <- ejson_key_is_eq_r_correct.
      destruct (key_is_eq_r (fun d : data => match d with
                                   | drec r => Some (drec (rproject r kl))
                                   | _ => None
                                             end) a0 a); try reflexivity.
      rewrite <- IHl1; clear IHl1.
      destruct (lift_filter
        (fun d : data =>
         key_is_eq_r (fun d0 : data => match d0 with
                                       | drec r => Some (drec (rproject r kl))
                                       | _ => None
                                       end) d a) l1); try reflexivity.
      destruct b; reflexivity.
    Qed.

    Lemma ejson_lift_map_group_of_key_correct kl l1 l2:
      lift data_to_ejson_partition
           (lift_map
              (fun k : data =>
                 match
                   group_of_key (fun d : data => match d with
                                                 | drec r => Some (drec (rproject r kl))
                                                 | _ => None
                                                 end) k l1
                 with
                 | Some x' => Some (k, x')
                 | None => None
                 end) l2)
      = lift_map
          (fun k : ejson =>
             match
               ejson_group_of_key
                 (fun j : ejson =>
                    match ejson_is_record j with
                    | Some r => Some (ejobject (rproject r (map key_encode kl)))
                    | None => None
                    end) k (map data_to_ejson l1)
             with
             | Some x' => Some (k, x')
             | None => None
             end) (map data_to_ejson l2).
    Proof.
      unfold lift.
      induction l2; try reflexivity; simpl.
      rewrite <- ejson_group_of_key_correct.
      destruct (group_of_key (fun d : data => match d with
                                      | drec r => Some (drec (rproject r kl))
                                      | _ => None
                                              end) a l1); try reflexivity; simpl.
      rewrite <- IHl2; clear IHl2.
      unfold lift; simpl in *.
      destruct (lift_map
        (fun k : data =>
         match
           group_of_key (fun d : data => match d with
                                         | drec r => Some (drec (rproject r kl))
                                         | _ => None
                                         end) k l1
         with
         | Some x' => Some (k, x')
         | None => None
         end) l2); reflexivity.
    Qed.

    Lemma ejson_group_by_nested_eval_correct kl l:
      lift data_to_ejson_partition
           (group_by_nested_eval
              (fun d : data => match d with
                               | drec r => Some (drec (rproject r kl))
                               | _ => None
                               end) l)
      =
      (ejson_group_by_nested_eval
         (fun j : ejson =>
            match ejson_is_record j with
            | Some r => Some (ejobject (rproject r (map key_encode kl)))
            | None => None
            end) (map data_to_ejson l)).
    Proof.
      unfold group_by_nested_eval.
      unfold ejson_group_by_nested_eval.
      unfold olift, lift; simpl.
      rewrite <- ejson_lift_map_rproject_correct.
      destruct (lift_map (fun d : data => match d with
                                          | drec r => Some (drec (rproject r kl))
                                          | _ => None
                                          end) l); try reflexivity.
      simpl.
      rewrite <- bdistinct_ejson_to_data_comm.
      generalize (bdistinct l0); intros.
      specialize (ejson_lift_map_group_of_key_correct kl l1); intros.
      rewrite <- ejson_lift_map_group_of_key_correct.
      reflexivity.
    Qed.

    Lemma ejson_group_to_partitions_correct g a:
      lift data_to_ejson (group_to_partitions g a)
      =
      ejson_group_to_partitions (key_encode g) (data_to_ejson (fst a), map data_to_ejson (snd a)).
    Proof.
      destruct a; simpl in *.
      unfold lift.
      unfold group_to_partitions.
      unfold ejson_group_to_partitions.
      simpl.
      destruct d; try reflexivity.
      - rewrite ejson_record_of_record; simpl.
        unfold rec_concat_sort; rewrite rec_concat_key_encode_comm; reflexivity.
      - destruct d; reflexivity.
      - destruct d; reflexivity.
      - simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    Lemma ejson_to_partition_correct g ol:
      lift (map data_to_ejson) (olift (to_partitions g) ol)
      = olift (ejson_to_partitions (key_encode g)) (lift data_to_ejson_partition ol).
    Proof.
      unfold olift, lift.
      destruct ol; simpl; try reflexivity.
      unfold to_partitions.
      unfold ejson_to_partitions.
      induction l; simpl; try reflexivity.
      rewrite <- ejson_group_to_partitions_correct.
      destruct (group_to_partitions g a); try reflexivity; simpl.
      rewrite <- IHl; clear IHl.
      unfold lift.
      destruct (lift_map (group_to_partitions g) l); reflexivity.
    Qed.

    Lemma ejson_group_by_nested_eval_keys_correct g kl l:
      lift (map data_to_ejson)
           (group_by_nested_eval_keys_partition
              g
              (fun d : data => match d with
                               | drec r => Some (drec (rproject r kl))
                               | _ => None
                               end) l)
      =
      ejson_group_by_nested_eval_keys_partition
        (key_encode g)
        (fun j : ejson =>
           match ejson_is_record j with
           | Some r => Some (ejobject (rproject r (map key_encode kl)))
           | None => None
           end) (map data_to_ejson l).
    Proof.
      unfold lift; simpl.
      unfold group_by_nested_eval_keys_partition.
      unfold ejson_group_by_nested_eval_keys_partition.
      rewrite <- ejson_group_by_nested_eval_correct.
      rewrite <- ejson_to_partition_correct.
      reflexivity.
    Qed.

    Lemma group_by_data_to_ejson_correct g kl l:
      match match group_by_nested_eval_table g kl l with
            | Some dl' => Some (dcoll dl')
            | None => None
            end with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_group_by_nested_eval_table (key_encode g) (map key_encode kl) (map data_to_ejson l) with
      | Some a' => Some (ejarray a')
      | None => None
      end.
    Proof.
      unfold group_by_nested_eval_table.
      unfold ejson_group_by_nested_eval_table.
      rewrite <- ejson_group_by_nested_eval_keys_correct.
      destruct (group_by_nested_eval_keys_partition g
        (fun d : data => match d with
                         | drec r => Some (drec (rproject r kl))
                         | _ => None
                         end) l); reflexivity.
    Qed.

    (** For OrderBy *)
    Definition sortCriteria_to_ejson (sc: string * SortDesc) : ejson :=
      let (lbl, c) := sc in
      match c with
      | Ascending => ejobject (("asc"%string, ejstring (key_encode lbl))::nil)
      | Descending => ejobject (("desc"%string, ejstring (key_encode lbl))::nil)
      end.

    Lemma get_criteria_to_ejson_correct a x:
      get_criteria a x
      = ejson_get_criteria (data_to_ejson a) (sortCriteria_to_ejson x).
    Proof.
      destruct x; simpl.
      destruct s0; simpl.
      (* asc *)
      - unfold edot.
        destruct a; try reflexivity.
        + rewrite ejson_record_of_record; simpl.
          rewrite <- assoc_lookupr_key_encode_comm.
          destruct (assoc_lookupr string_eqdec l s); try reflexivity.
          destruct d; simpl; reflexivity.
        + destruct a; reflexivity.
        + destruct a; reflexivity.
        + simpl; rewrite ejson_brands_map_ejstring; reflexivity.
      (* desc *)
      - unfold edot.
        destruct a; try reflexivity.
        + rewrite ejson_record_of_record; simpl.
          rewrite <- assoc_lookupr_key_encode_comm.
          destruct (assoc_lookupr string_eqdec l s); try reflexivity.
          destruct d; simpl; reflexivity.
        + destruct a; reflexivity.
        + destruct a; reflexivity.
        + simpl; rewrite ejson_brands_map_ejstring; reflexivity.
    Qed.

    Lemma sortable_data_ejson_correct a s :
      lift (fun xy => (fst xy, data_to_ejson (snd xy))) (sortable_data_of_data a s)
      = ejson_sortable_data_of_ejson (data_to_ejson a) (map sortCriteria_to_ejson s).
    Proof.
      unfold sortable_data_of_data.
      unfold ejson_sortable_data_of_ejson.
      unfold lift.
      unfold get_criterias.
      unfold ejson_get_criterias.
      rewrite lift_map_map_fusion.
      induction s; simpl; try reflexivity.
      rewrite get_criteria_to_ejson_correct.
      destruct (ejson_get_criteria (data_to_ejson a) (sortCriteria_to_ejson a0)); try reflexivity; simpl.
      unfold lift.
      destruct (lift_map (get_criteria a) s);
        destruct (lift_map (fun x : string * SortDesc =>
                              ejson_get_criteria (data_to_ejson a) (sortCriteria_to_ejson x))
                           s); try congruence.
      simpl.
      inversion IHs.
      subst.
      reflexivity.
    Qed.

    Lemma sortable_coll_to_ejson_correct s l:
      lift (map (fun xy => (fst xy, data_to_ejson (snd xy)))) (sortable_coll_of_coll s l)
      = ejson_sortable_coll_of_coll (map sortCriteria_to_ejson s) (map data_to_ejson l).
    Proof.
      unfold sortable_coll_of_coll.
      unfold ejson_sortable_coll_of_coll.
      unfold lift.
      induction l; try reflexivity; simpl.
      rewrite <- IHl; clear IHl.
      rewrite <- sortable_data_ejson_correct.
      destruct (sortable_data_of_data a s); try reflexivity; simpl.
      destruct s0; simpl.
      unfold lift.
      destruct (lift_map (fun d0 : data => sortable_data_of_data d0 s) l); reflexivity.
    Qed.

    Lemma sort_sortable_coll_data_to_ejson_comm l:
      sort_sortable_coll (map (fun xy : list sdata * data => (fst xy, data_to_ejson (snd xy))) l)
      = map (fun xy : list sdata * data => (fst xy, data_to_ejson (snd xy))) (sort_sortable_coll l).
    Proof.
      unfold sort_sortable_coll.
      unfold dict_sort.
      rewrite (map_insertion_sort
                 (@dict_field_le_dec (@data (@foreign_runtime_data fruntime)))
                 (@dict_field_le_dec (@ejson fejson))).
      reflexivity.
      intros.
      split; intros;
      destruct x; destruct y; simpl in *.
      - unfold dict_field_le; simpl; auto.
      - unfold dict_field_le; simpl; auto.
    Qed.

    Lemma coll_of_sortable_coll_data_to_ejson_comm l:
      coll_of_sortable_coll (map (fun xy : list sdata * data => (fst xy, data_to_ejson (snd xy))) l)
      = map data_to_ejson (coll_of_sortable_coll l).
    Proof.
      unfold coll_of_sortable_coll.
      rewrite map_map; rewrite map_map; reflexivity.
    Qed.

    Lemma order_by_to_ejson_correct s d :
      match data_sort s d with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end = ejson_sort (map sortCriteria_to_ejson s) (data_to_ejson d).
    Proof.
      unfold data_sort.
      unfold ejson_sort.
      destruct d; simpl; try reflexivity.
      rewrite <- sortable_coll_to_ejson_correct.
      unfold lift.
      destruct (sortable_coll_of_coll s l); try reflexivity; simpl.
      rewrite sort_sortable_coll_data_to_ejson_comm.
      rewrite coll_of_sortable_coll_data_to_ejson_comm.
      reflexivity.
    Qed.

  End RuntimeLemmas.

  Section Lift.
    Definition lift_bindings (env:bindings) : jbindings :=
      List.map (fun xy => (fst xy, data_to_ejson (snd xy))) env.
    Definition lift_pd_bindings (env:pd_bindings) : pd_jbindings :=
      List.map (fun xy => (fst xy, lift data_to_ejson (snd xy))) env.
    Definition lift_result (res:option ejson) : option data :=
      lift ejson_to_data res.
    Definition unlift_result (res:option data) : option ejson :=
      lift data_to_ejson res.
    Definition lift_result_env (res:option pd_jbindings) : option pd_bindings :=
      lift (fun env => List.map (fun xy => (fst xy, lift ejson_to_data (snd xy))) env) res.
    Definition unlift_result_env (res:option pd_bindings) : option pd_jbindings :=
      lift (fun env => List.map (fun xy => (fst xy, lift data_to_ejson (snd xy))) env) res.
  End Lift.

End DataToEJson.
