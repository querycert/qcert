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

Section DatatoJSON.
  Require Import List.
  Require Import String.
  Require Import ZArith.
  Require Import Utils.
  Require Import JSON.
  Require Import ForeignData.
  Require Import ForeignDataToJSON.
  Require Import Data.
  Require Import DataNorm.

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

  Section toData.
    Context {ftojson:foreign_to_JSON}.

    (* JSON to CAMP data model (META Variant) *)

    Fixpoint json_to_data_pre (j:json) : data :=
      match foreign_to_JSON_to_data j with
      | Some fd => dforeign fd
      | None => 
        match j with
        | jnil => dunit
        | jnumber n => dnumber n
        | jbool b => dbool b
        | jstring s => dstring s
        | jarray c => dcoll (map json_to_data_pre c)
        | jobject nil => drec nil
        | jobject ((s1,j')::nil) =>
          if (string_dec s1 "left") then dleft (json_to_data_pre j')
          else if (string_dec s1 "right") then dright (json_to_data_pre j')
               else drec ((s1, json_to_data_pre j')::nil)
        | jobject ((s1,jarray j1)::(s2,j2)::nil) =>
          if (string_dec s1 "type") then
            if (string_dec s2 "data") then
              match (json_brands j1) with
              | Some br => dbrand br (json_to_data_pre j2)
              | None => drec ((s1, dcoll (map json_to_data_pre j1))::(s2, json_to_data_pre j2)::nil)
              end
            else drec ((s1, dcoll (map json_to_data_pre j1))::(s2, json_to_data_pre j2)::nil)
          else drec ((s1, dcoll (map json_to_data_pre j1))::(s2, json_to_data_pre j2)::nil)
        | jobject ((s1,j1)::(s2,jarray j2)::nil) =>
          if (string_dec s1 "data") then
            if (string_dec s2 "type") then
              match (json_brands j2) with
              | Some br => dbrand br (json_to_data_pre j1)
              | None => drec ((s1, json_to_data_pre j1)::(s2, dcoll (map json_to_data_pre j2))::nil)
              end
            else drec ((s1, json_to_data_pre j1)::(s2, dcoll (map json_to_data_pre j2))::nil)
          else drec ((s1, json_to_data_pre j1)::(s2, dcoll (map json_to_data_pre j2))::nil)
        | jobject r => (drec (map (fun x => (fst x, json_to_data_pre (snd x))) r))
        end
      end.

    Definition json_to_data h (j:json) :=
      normalize_data h (json_to_data_pre j).

    (* JSON to CAMP data model (Enhanced Variant) *)

    Fixpoint json_enhanced_to_data_pre (j:json) :=
      match foreign_to_JSON_to_data j with
      | Some fd => dforeign fd
      | None => 
        match j with
        | jnil => dright dunit
        | jnumber n => dnumber n
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
    Require Import JsAst.JsNumber.
    
    Fixpoint data_enhanced_to_json (d:data) : json :=
      match d with
      | dunit => jnil
      | dnat n => jnumber (of_int n)
      | dnumber n => jnumber n
      | dbool b => jbool b
      | dstring s => jstring s
      | dcoll c => jarray (map data_enhanced_to_json c)
      | drec r => jobject (map (fun x => (fst x, data_enhanced_to_json (snd x))) r)
      | dleft d' => jobject (("left"%string, data_enhanced_to_json d')::nil)
      | dright d' => jobject (("right"%string, data_enhanced_to_json d')::nil)
      | dbrand b (drec r) => jobject (("$class "%string, jarray (map jstring b))::(map (fun x => (fst x, data_enhanced_to_json (snd x))) r))
      | dbrand b d' => jobject (("$class"%string, jarray (map jstring b))::("$data"%string, (data_enhanced_to_json d'))::nil)
      | dforeign fd => foreign_to_JSON_from_data fd
      end.

    Fixpoint data_to_json (d:data) : json :=
      match d with
      | dunit => jnil
      | dnat n => jnumber (of_int n)
      | dnumber n => jnumber n
      | dbool b => jbool b
      | dstring s => jstring s
      | dcoll c => jarray (map data_to_json c)
      | drec r => jobject (map (fun x => (fst x, data_to_json (snd x))) r)
      | dleft d' => jobject (("left"%string, data_to_json d')::nil)
      | dright d' => jobject (("right"%string, data_to_json d')::nil)
      | dbrand b d' => jobject (("type"%string, jarray (map jstring b))::("data"%string, (data_to_json d'))::nil)
      | dforeign fd => foreign_to_JSON_from_data fd
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

