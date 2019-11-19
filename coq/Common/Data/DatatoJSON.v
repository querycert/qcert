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
Require Import JSON.
Require Import ForeignData.
Require Import ForeignDataToJSON.
Require Import Data.
Require Import DataNorm.

Section DatatoJSON.

  Context {fdata:foreign_data}.
  Fixpoint json_brands (d:list json) : option (list string) :=
    match d with
    | nil => Some nil
    | (jstring s1) :: d' =>
      match json_brands d' with
      | Some s' => Some (s1::s')
      | None => None
      end
    | _ => None
    end.

  Definition json_key_encode (s:string) : string
    := match s with
       | String "$"%char s => String "$"%char (String "$"%char s)
       | _ => s
       end.
                            
  Definition json_key_decode (s:string) : string
    := match s with
       | EmptyString => EmptyString
       | String "$"%char (String "$"%char s) =>  String "$"%char s
       | _ => s
       end.

  Lemma json_key_encode_decode (s:string) : json_key_decode (json_key_encode s) = s.
    do 2 (destruct s; simpl; trivial)
    ; repeat match_destr.
  Qed.

  Section toData.
    Context {ftojson:foreign_to_JSON}.

    (* JSON to CAMP data model (META Variant) *)

    Fixpoint json_to_data_pre (j:json) : data :=
      match j with
      | jnull => dunit
      | jnumber n => dfloat n
      | jbool b => dbool b
      | jstring s => dstring s
      | jarray c => dcoll (map json_to_data_pre c)
      | jobject nil => drec nil
      | jobject ((s1,j')::nil) =>
        if (string_dec s1 "$nat") then
          match j' with
          | jnumber n =>
            dnat (float_truncate n)
          | _ =>
            drec ((json_key_decode s1, json_to_data_pre j')::nil)
          end
        else if (string_dec s1 "$left") then dleft (json_to_data_pre j')
             else if (string_dec s1 "$right") then dright (json_to_data_pre j')
                  else if (string_dec s1 "$foreign") then
                         match foreign_to_JSON_to_data j' with
                         | Some fd => dforeign fd
                         | None => drec ((json_key_decode s1, json_to_data_pre j')::nil)
                         end
                       else drec ((json_key_decode s1, json_to_data_pre j')::nil)
      | jobject ((s1,jarray j1)::(s2,j2)::nil) =>
        if (string_dec s1 "$type") then
          if (string_dec s2 "$data") then
            match (json_brands j1) with
            | Some br => dbrand br (json_to_data_pre j2)
            | None => drec ((json_key_decode s1, dcoll (map json_to_data_pre j1))::(json_key_decode s2, json_to_data_pre j2)::nil)
            end
          else drec ((json_key_decode s1, dcoll (map json_to_data_pre j1))::(json_key_decode s2, json_to_data_pre j2)::nil)
        else drec ((json_key_decode s1, dcoll (map json_to_data_pre j1))::(json_key_decode s2, json_to_data_pre j2)::nil)
      | jobject ((s1,j1)::(s2,jarray j2)::nil) =>
        if (string_dec s1 "$data") then
          if (string_dec s2 "$type") then
            match (json_brands j2) with
            | Some br => dbrand br (json_to_data_pre j1)
            | None => drec ((json_key_decode s1, json_to_data_pre j1)::(json_key_decode s2, dcoll (map json_to_data_pre j2))::nil)
            end
          else drec ((json_key_decode s1, json_to_data_pre j1)::(json_key_decode s2, dcoll (map json_to_data_pre j2))::nil)
        else drec ((json_key_decode s1, json_to_data_pre j1)::(json_key_decode s2, dcoll (map json_to_data_pre j2))::nil)
      | jobject r => (drec (map (fun x => (json_key_decode (fst x), json_to_data_pre (snd x))) r))
      end.

    Definition json_to_data h (j:json) :=
      normalize_data h (json_to_data_pre j).

    (* JSON to CAMP data model (Enhanced Variant) *)

    Fixpoint json_enhanced_to_data_pre (j:json) :=
      match foreign_to_JSON_to_data j with
      | Some fd => dforeign fd
      | None => 
        match j with
        | jnull => dright dunit
        | jnumber n => dfloat n
        | jbool b => dbool b
        | jstring s => dstring s
        | jarray c => dcoll (map json_enhanced_to_data_pre c)
        | jobject r =>
          let rfields := domain r in
          if (in_dec string_dec "key"%string rfields)
          then
            match edot r "key" with
            | Some (jstring key) => dleft (dstring key)
            | _ => drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
            end
          else
            if (in_dec string_dec "$class"%string rfields)
            then
              match r with
              | (s1,jstring j1) :: rest =>
                if (string_dec s1 "$class") then
                  match (json_brands ((jstring j1)::nil)) with
                  | Some br => dbrand br (drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) rest))
                  | None => drec ((s1, dstring j1)::(map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) rest))
                  end
                else drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
              | _ =>
                drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
              end
            else
              drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
        end
      end.

    Definition json_enhanced_to_data h (j:json) :=
      normalize_data h (json_enhanced_to_data_pre j).
    
  End toData.

  Section toJSON.
    Context {ftojson:foreign_to_JSON}.

    Definition Z_to_json (n: Z) : json :=
      jobject (("$nat"%string, jnumber (float_of_int n))::nil).

    Fixpoint data_enhanced_to_js (quotel:string) (d:data) : json :=
      match d with
      | dunit => jnull
      | dnat n => Z_to_json n
      | dfloat n => jnumber n
      | dbool b => jbool b
      | dstring s => jstring s
      | dcoll c => jarray (map (data_enhanced_to_js quotel) c)
      | drec r => jobject (map (fun x => (fst x, (data_enhanced_to_js quotel) (snd x))) r)
      | dleft d' => jobject (("left"%string, data_enhanced_to_js quotel d')::nil)
      | dright d' => jobject (("right"%string, data_enhanced_to_js quotel d')::nil)
      | dbrand b (drec r) => jobject (("$class "%string, jarray (map jstring b))::(map (fun x => (fst x, data_enhanced_to_js quotel (snd x))) r))
      | dbrand b d' => jobject (("$class"%string, jarray (map jstring b))::("$data"%string, (data_enhanced_to_js quotel d'))::nil)
      | dforeign fd => foreign_to_JSON_from_data fd
      end.

    Fixpoint data_enhanced_to_json (d:data) : json := data_enhanced_to_js "" d.

    Fixpoint data_to_json (d:data) : json :=
      match d with
      | dunit => jnull
      | dnat n => Z_to_json n
      | dfloat n => jnumber n
      | dbool b => jbool b
      | dstring s => jstring s
      | dcoll c => jarray (map data_to_json c)
      | drec r => jobject (map (fun x => (json_key_encode (fst x), data_to_json (snd x))) r)
      | dleft d' => jobject (("$left"%string, data_to_json d')::nil)
      | dright d' => jobject (("$right"%string, data_to_json d')::nil)
      | dbrand b d' => jobject (("$type"%string, jarray (map jstring b))::("$data"%string, (data_to_json d'))::nil)
      | dforeign fd => jobject (("$foreign"%string, foreign_to_JSON_from_data fd)::nil)
      end.

    End toJSON.

  Section RoundTripping.
    Inductive json_data : data -> Prop :=
    | json_null : json_data dunit
    | json_nat n : json_data (dnat n)
    | json_bool b : json_data (dbool b)
    | json_string s : json_data (dstring s)
    | json_array dl : Forall (fun d => json_data d) dl -> json_data (dcoll dl)
    | json_rec r :
        is_list_sorted ODT_lt_dec (domain r) = true ->
        Forall (fun ab => json_data (snd ab)) r ->
        json_data (drec r)
    .
  
    Inductive pure_data : data -> Prop :=
    | pure_null : pure_data dunit
    | pure_nat n : pure_data (dnat n)
    | pure_bool b : pure_data (dbool b)
    | pure_string s : pure_data (dstring s)
    | pure_array dl : Forall (fun d => pure_data d) dl -> pure_data (dcoll dl)
    | pure_rec r :
        assoc_lookupr string_dec r "$left"%string = None ->
        assoc_lookupr string_dec r "$right"%string = None ->
        assoc_lookupr string_dec r "$class"%string = None ->
        is_list_sorted ODT_lt_dec (domain r) = true ->
        Forall (fun ab => pure_data (snd ab)) r ->
        pure_data (drec r)
    | pure_left d :
        pure_data d -> pure_data (dleft d)
    | pure_right d :
        pure_data d -> pure_data (dright d)
    | pure_brand b r :
        pure_data (drec r) -> pure_data (dbrand b (drec r))
    .

    Lemma pure_dcoll_inv c:
      Forall (fun d : data => pure_data d) c <-> pure_data (dcoll c).
    Proof.
      split; intros.
      econstructor; assumption.
      inversion H; assumption.
    Qed.

    Lemma no_assoc_with_map (r:list (string*data)) (f:data->data) s:
      assoc_lookupr string_dec r s = None ->
      assoc_lookupr string_dec (map (fun x => (fst x, f (snd x))) r) s = None.
    Proof.
      intros.
      induction r.
      reflexivity.
      destruct a; simpl in *.
      case_eq (assoc_lookupr string_dec r s); intros.
      rewrite H0 in H; congruence.
      rewrite H0 in H.
      rewrite (IHr H0).
      destruct (string_dec s s0); congruence.
    Qed.
    
    Lemma domains_with_map (r:list (string*data)) (f:data->data):
      domain (map (fun x : string * data => (fst x, f (snd x))) r) = domain r.
    Proof.
      induction r. reflexivity.
      simpl.
      rewrite IHr; reflexivity.
    Qed.

    Lemma assoc_lookupr_skip {A} (a:string*A) (l:list (string*A)) (s:string):
      assoc_lookupr string_dec (a::l) s = None ->
      assoc_lookupr string_dec l s = None.
    Proof.
      intros.
      simpl in H.
      destruct a; simpl in *.
      destruct (assoc_lookupr string_dec l s); congruence.
    Qed.

    
    Lemma pure_drec_cons_inv a r:
      pure_data (drec (a::r)) -> (pure_data (drec r) /\ pure_data (snd a)).
    Proof.
      intros.
      inversion H; clear H; subst.
      inversion H5; clear H5; subst.
      split.
      - constructor.
        apply (assoc_lookupr_skip a r _ H1).
        apply (assoc_lookupr_skip a r _ H2).
        apply (assoc_lookupr_skip a r _ H3).
        apply (rec_sorted_skip_first r a H4).
        assumption.
      - assumption.
    Qed.

  End RoundTripping.

End DatatoJSON.


(* TODO: figure out what to do and move this somewhere else *)
Axiom float_truncate_float_of_int : forall (z:Z), float_truncate (float_of_int z) = z.

Section ModelRoundTrip.

  Context {fdata:foreign_data}.
  Context {ftojson:foreign_to_JSON}.
  Lemma json_brands_map_jstring b : json_brands (map jstring b) = Some b.
  Proof.
    induction b; simpl; trivial.
    now rewrite IHb.
  Qed.


  Lemma json_key_encode_not_data s : (json_key_encode s) <> "$data"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma json_key_encode_not_type s : (json_key_encode s) <> "$type"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma json_key_encode_not_foreign s : (json_key_encode s) <> "$foreign"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma json_key_encode_not_nat s : (json_key_encode s) <> "$nat"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma json_key_encode_not_left s : (json_key_encode s) <> "$left"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma json_key_encode_not_right s : (json_key_encode s) <> "$right"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
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


  Lemma json_to_data_to_json_idempotent h d:
    json_to_data h (data_to_json d) = normalize_data h d.
  Proof.
    unfold json_to_data.
    induction d; simpl; trivial.
    - rewrite float_truncate_float_of_int; trivial.
    - f_equal.
      repeat rewrite map_map.
      now apply map_eq.
    -
      destruct r; simpl; trivial.
      destruct p; simpl.
      rewrite_string_dec_from_neq (json_key_encode_not_nat s).
      rewrite_string_dec_from_neq (json_key_encode_not_data s).
      rewrite_string_dec_from_neq (json_key_encode_not_type s).
      rewrite_string_dec_from_neq (json_key_encode_not_left s).
      rewrite_string_dec_from_neq (json_key_encode_not_right s).
      rewrite_string_dec_from_neq (json_key_encode_not_foreign s).

      assert (eq_simpl: match data_to_json d with
                        | jarray j1 =>
                          match map (fun x : string * data => (json_key_encode (fst x), data_to_json (snd x))) r with
                          | nil =>
                            drec ((json_key_decode (json_key_encode s), json_to_data_pre (data_to_json d)) :: nil)
                          | (s2, jnull as j2) :: nil | (s2, jnumber _ as j2) :: nil | (s2, jbool _ as j2) :: nil |
                          (s2, jstring _ as j2) :: nil | (s2, jarray _ as j2) :: nil |
                          (s2, jobject _ as j2) :: nil =>
                          drec
                            ((json_key_decode (json_key_encode s), dcoll (map json_to_data_pre j1))
                               :: (json_key_decode s2, json_to_data_pre j2) :: nil)
                          | (s2, jnull as j2) :: _ :: _ | (s2, jnumber _ as j2) :: _ :: _ |
                          (s2, jbool _ as j2) :: _ :: _ | (s2, jstring _ as j2) :: _ :: _ |
                          (s2, jarray _ as j2) :: _ :: _ | (s2, jobject _ as j2) :: _ :: _ =>
                                                           drec
                                                             ((json_key_decode (json_key_encode s), json_to_data_pre (data_to_json d))
                                                                :: map (fun x : string * json => (json_key_decode (fst x), json_to_data_pre (snd x)))
                                                                (map (fun x : string * data => (json_key_encode (fst x), data_to_json (snd x))) r))
                          end
                        | _ =>
                          match map (fun x : string * data => (json_key_encode (fst x), data_to_json (snd x))) r with
                          | nil =>
                            drec ((json_key_decode (json_key_encode s), json_to_data_pre (data_to_json d)) :: nil)
                          | (s2, jarray j2) :: nil =>
                            drec
                              ((json_key_decode (json_key_encode s), json_to_data_pre (data_to_json d))
                                 :: (json_key_decode s2, dcoll (map json_to_data_pre j2)) :: nil)
                          | (s2, jarray j2) :: _ :: _ =>
                            drec
                              ((json_key_decode (json_key_encode s), json_to_data_pre (data_to_json d))
                                 :: map (fun x : string * json => (json_key_decode (fst x), json_to_data_pre (snd x)))
                                 (map (fun x : string * data => (json_key_encode (fst x), data_to_json (snd x))) r))
                          | (s2, jnull) :: _ | (s2, jnumber _) :: _ | (s2, jbool _) :: _ | 
                          (s2, jstring _) :: _ | (s2, jobject _) :: _ =>
                                                 drec
                                                   ((json_key_decode (json_key_encode s), json_to_data_pre (data_to_json d))
                                                      :: map (fun x : string * json => (json_key_decode (fst x), json_to_data_pre (snd x)))
                                                      (map (fun x : string * data => (json_key_encode (fst x), data_to_json (snd x))) r))
                          end
                        end = drec ((json_key_decode (json_key_encode s), json_to_data_pre (data_to_json d))::(map (fun x : string * json => (json_key_decode (fst x), json_to_data_pre (snd x))) (map (fun x : string * data => (json_key_encode (fst x), data_to_json (snd x))) r)))).
      {
        destruct (data_to_json d); simpl
        ; destruct (map (fun x : string * data => (json_key_encode (fst x), data_to_json (snd x))) r      ); simpl; trivial
        ; destruct p
        ; destruct j; simpl; trivial
        ; destruct l; simpl; trivial
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
      apply map_eq.
      revert H3.
      apply Forall_impl; intros.
      rewrite json_key_encode_decode.
      rewrite H; trivial.
    - cut (
          match data_to_json d with
          | jnull | _ => normalize_data h (dleft (json_to_data_pre (data_to_json d)))
          end = dleft (normalize_data h d)).
      + now destruct (data_to_json d).
      + simpl.
        rewrite IHd.
        now destruct (data_to_json d).
    - cut (
          match data_to_json d with
          | jnull | _ => normalize_data h (dright (json_to_data_pre (data_to_json d)))
          end = dright (normalize_data h d)).
      + now destruct (data_to_json d).
      + simpl.
        rewrite IHd.
        now destruct (data_to_json d).
    - cut (
          match data_to_json d with
          | jnull | _ =>
                    match json_brands (map jstring b) with
                    | Some br => (normalize_data h (dbrand br (json_to_data_pre (data_to_json d))))
                    | None =>
                      (normalize_data h (drec
                                           (("type"%string, dcoll (map json_to_data_pre (map jstring b)))
                                              :: ("data"%string, json_to_data_pre (data_to_json d)) :: nil)))
                    end
          end = dbrand (BrandRelation.canon_brands h b) (normalize_data h d)).
      + now (destruct (data_to_json d); destruct (json_brands (map jstring b))).
      + simpl.
        rewrite IHd.
        rewrite json_brands_map_jstring.
        now destruct (data_to_json d).
    - rewrite foreign_to_JSON_to_data_to_json.
      now destruct (foreign_to_JSON_from_data fd).
  Qed.

  Section RuntimeLemmas.
    (* XXX Some assumptions for the correctness of operators translation -- do they hold?? *)
    Lemma json_to_data_object_not_boolean h l b:
      ~(json_to_data h (jobject l) = dbool b).
    Proof.
    Admitted.

    Lemma json_to_data_object_not_coll h l j:
      ~(json_to_data h (jobject l) = dcoll j).
    Proof.
    Admitted.

    Lemma rec_json_key_encode_roundtrip h s i0:
      drec ((s, json_to_data h i0)::nil) = json_to_data h (jobject ((json_key_encode s, i0)::nil)).
    Proof.
    Admitted.

    Lemma assoc_lookupr_json_key_encode_roundtrip h l s:
      match json_to_data h (jobject l) with
      | drec r => assoc_lookupr ODT_eqdec r s
      | _ => None
      end =
      match assoc_lookupr ODT_eqdec l (json_key_encode s) with
      | Some a' => Some (json_to_data h a')
      | None => None
      end.
    Proof.
      admit.
    Admitted.

    Lemma rremove_json_key_encode_roundtrip h l s:
      match json_to_data h (jobject l) with
      | drec r => Some (drec (rremove r s))
      | _ => None
      end = Some (json_to_data h (jobject (rremove l (json_key_encode s)))).
    Proof.
      admit.
    Admitted.

  End RuntimeLemmas.
End ModelRoundTrip.
