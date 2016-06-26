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

Section JSON.

  Require Import List String.
  Require Import Utils.
  Require Import BasicRuntime.
  Require Import ForeignToJSON.

  Context {fdata:foreign_data}.
  Context {ftojson:foreign_to_JSON}.

  (* TEMPORARY -- NOT PROVED ROUNDTRIPPING *)

  Fixpoint json_brands (d:list data) : option (list string) :=
    match d with
    | nil => Some nil
    | (dstring s1) :: d' =>
      match json_brands d' with
      | Some s' => Some (s1::s')
      | None => None
      end
    | _ => None
    end.
  
  (* JSON to CAMP data model (META Variant) *)

  Fixpoint json_to_data_pre (d:data) :=
    match foreign_to_JSON_to_data d with
    | Some fd => dforeign fd
    | None => 
      match d with
      | dunit => dunit
      | dnat n => dnat n
      | dbool b => dbool b
      | dstring s => dstring s
      | dcoll c => dcoll (map json_to_data_pre c)
      | drec nil => drec nil
      | drec ((s1,d')::nil) =>
        if (string_dec s1 "left") then dleft (json_to_data_pre d')
        else if (string_dec s1 "right") then dright (json_to_data_pre d')
             else drec ((s1, json_to_data_pre d')::nil)
      | drec ((s1,dcoll d1)::(s2,d2)::nil) =>
        if (string_dec s1 "type") then
          if (string_dec s2 "data") then
            match (json_brands d1) with
            | Some br => dbrand br (json_to_data_pre d2)
            | None => drec ((s1, dcoll (map json_to_data_pre d1))::(s2, json_to_data_pre d2)::nil)
            end
          else drec ((s1, dcoll (map json_to_data_pre d1))::(s2, json_to_data_pre d2)::nil)
        else drec ((s1, dcoll (map json_to_data_pre d1))::(s2, json_to_data_pre d2)::nil)
      | drec ((s1,d1)::(s2,dcoll d2)::nil) =>
        if (string_dec s1 "data") then
          if (string_dec s2 "type") then
            match (json_brands d2) with
            | Some br => dbrand br (json_to_data_pre d1)
            | None => drec ((s1, json_to_data_pre d1)::(s2, dcoll (map json_to_data_pre d2))::nil)
            end
          else drec ((s1, json_to_data_pre d1)::(s2, dcoll (map json_to_data_pre d2))::nil)
        else drec ((s1, json_to_data_pre d1)::(s2, dcoll (map json_to_data_pre d2))::nil)
      | drec r => (drec (map (fun x => (fst x, json_to_data_pre (snd x))) r))
      | dleft d' => dleft (json_to_data_pre d')
      | dright d' => dright (json_to_data_pre d')
      | dbrand b d' => dbrand b (json_to_data_pre d')
      | dforeign fd => dforeign fd
      end
    end.

  Definition json_to_data h (d:data) :=
    normalize_data h (json_to_data_pre d).

  (* JSON to CAMP data model (Enhanced Variant) *)

  Fixpoint json_enhanced_to_data_pre (d:data) :=
    match foreign_to_JSON_to_data d with
    | Some fd => dforeign fd
    | None => 
      match d with
      | dunit => dright dunit
      | dnat n => dnat n
      | dbool b => dbool b
      | dstring s => dstring s
      | dcoll c => dcoll (map json_enhanced_to_data_pre c)
      | drec r =>
        let rfields := domain r in
        if (in_dec string_dec "key"%string rfields)
        then
          match edot r "key" with
          | Some key => dleft key
          | None => drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
          end
        else
          if (in_dec string_dec "$class"%string rfields)
          then
            match r with
            | (s1,dstring d1) :: rest =>
              if (string_dec s1 "$class") then
                match (json_brands ((dstring d1)::nil)) with
                | Some br => dbrand br (drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) rest))
                | None => drec ((s1, dstring d1)::(map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) rest))
                end
              else drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
            | _ =>
              drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
            end
          else
            drec (map (fun x => (fst x, json_enhanced_to_data_pre (snd x))) r)
      | dleft d' => dleft (json_enhanced_to_data_pre d')
      | dright d' => dright (json_enhanced_to_data_pre d')
      | dbrand b d' => dbrand b (json_enhanced_to_data_pre d')
      | dforeign fd => dforeign fd
      end
    end.

  Definition json_enhanced_to_data h (d:data) :=
    normalize_data h (json_enhanced_to_data_pre d).

  (* Prototype stuff *)
  
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
  
  Inductive jsonc_data : data -> Prop :=
  | jsonc_null : jsonc_data dunit
  | jsonc_nat n : jsonc_data (dnat n)
  | jsonc_bool b : jsonc_data (dbool b)
  | jsonc_string s : jsonc_data (dstring s)
  | jsonc_array dl : Forall (fun d => jsonc_data d) dl -> jsonc_data (dcoll dl)
  | jsonc_left r d :
      assoc_lookupr string_dec r "$left"%string = Some d ->
      (forall s, In s (domain r) -> s = "$left"%string) ->
      Forall (fun ab => jsonc_data (snd ab)) r ->
      jsonc_data (drec r)
  | jsonc_right r d :
      assoc_lookupr string_dec r "$right"%string = Some d ->
      (forall s, In s (domain r) -> s = "$right"%string) ->
      Forall (fun ab => jsonc_data (snd ab)) r ->
      jsonc_data (drec r)
  | jsonc_rec r :
      assoc_lookupr string_dec r "$left"%string = None ->
      assoc_lookupr string_dec r "$right"%string = None ->
      assoc_lookupr string_dec r "$class"%string = None ->
      is_list_sorted ODT_lt_dec (domain r) = true ->
      Forall (fun ab => jsonc_data (snd ab)) r ->
      jsonc_data (drec r)
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

  Fixpoint data_to_json (d:data) :=
    match d with
    | dunit => dunit
    | dnat n => dnat n
    | dbool b => dbool b
    | dstring s => dstring s
    | dcoll c => dcoll (map data_to_json c)
    | drec r => (drec (map (fun x => (fst x, data_to_json (snd x))) r))
    | dleft d' => drec (("$left"%string, data_to_json d')::nil)
    | dright d' => drec (("$right"%string, data_to_json d')::nil)
    | dbrand b (drec r) => drec (("$class "%string, dcoll (map dstring b))::r)
    | dbrand b d' => drec (("$class"%string, dcoll (map dstring b))::("$data"%string,d')::nil)
    | dforeign fd => foreign_to_JSON_from_data fd
     end.

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

  Lemma pure_data_to_jsonc (d:data) :
    pure_data d -> jsonc_data (data_to_json d).
  Proof.
    induction d; simpl; try reflexivity; intros.
    - constructor.
    - constructor.
    - constructor.
    - constructor.
    - constructor.
      induction c.
      apply Forall_nil.
      inversion H0; clear H0; subst.
      inversion H; clear H; subst.
      inversion H2; clear H2; subst.
      rewrite pure_dcoll_inv in H5.
      specialize (IHc H4 H5); clear H4 H5.
      rewrite Forall_forall in *; intros; simpl in *.
      elim H; clear H; intros. subst.
      apply H3; clear H3; assumption.
      apply IHc; assumption.
    - inversion H0; intros; subst.
      apply jsonc_rec; try (apply no_assoc_with_map; assumption).
      rewrite domains_with_map; assumption.
      clear H2 H3 H4 H5. induction r. apply Forall_nil; simpl in *.
      inversion H; clear H; subst.
      inversion H6; clear H6; subst.
      assert (pure_data (drec r) /\ (pure_data (snd a))) by apply (pure_drec_cons_inv a r H0).
      elim H; clear H; intros.
      specialize (IHr H4 H H5); clear H4 H5 H.
      constructor.
      + destruct a; simpl in *. apply H3; apply H1.
      + apply IHr.
    - inversion H; clear H; subst.
      apply (jsonc_left _ (data_to_json d)); simpl.
      reflexivity.
      intros; elim H; intros; auto; contradiction.
      rewrite Forall_forall; intros; simpl in *.
      elim H; clear H; try contradiction; intros.
      destruct x; simpl in *.
      inversion H; clear H; subst; apply (IHd H1).
    - inversion H; clear H; subst.
      apply (jsonc_right _ (data_to_json d)); simpl.
      reflexivity.
      intros; elim H; intros; auto; contradiction.
      rewrite Forall_forall; intros; simpl in *.
      elim H; clear H; try contradiction; intros.
      destruct x; simpl in *.
      inversion H; clear H; subst; apply (IHd H1).
    - inversion H; clear H; subst.
      specialize (IHd H1); clear H1.
      admit. (* This part's wrong still.. *)
    - admit.
  Admitted.
  
  Fixpoint JSONtoConcise (d:data) :=
    match d with
    | dunit => dunit
    | dnat n => dnat n
    | dbool b => dbool b
    | dstring s => dstring s
    | dcoll c => dcoll (map JSONtoConcise c)
    | drec nil => drec nil
    | drec ((s1,d')::nil) =>
      if (string_dec s1 "$left") then dleft (JSONtoConcise d')
      else if (string_dec s1 "$right") then dright (JSONtoConcise d')
           else drec ((s1, JSONtoConcise d')::nil)
    | drec r => (drec (map (fun x => (fst x, JSONtoConcise (snd x))) r))
    | dleft d' => dleft (JSONtoConcise d')
    | dright d' => dright (JSONtoConcise d')
    | dbrand b d' => dbrand b (JSONtoConcise d')
    | dforeign fd => dforeign fd
    end.

  Lemma JSONtoConcise_idem h d:
    data_normalized h d ->
    JSONtoConcise (JSONtoConcise d) = JSONtoConcise d.
  Proof.
    induction d; simpl; try reflexivity; intros.
    - induction c; simpl in *; try reflexivity.
      inversion H0.
      subst.
      assert (data_normalized h (dcoll c)).
      inversion H2. subst. clear H2.
      constructor. assumption.
      inversion H; clear H; subst.
      inversion H2; clear H2; subst.
      specialize (IHc H6 H1); clear H6 H1.
      specialize (H5 H4); clear H4.
      rewrite H5.
      f_equal; f_equal.
      inversion IHc. repeat rewrite H1. reflexivity.
    - destruct r; try reflexivity; destruct p; simpl in *.
      destruct r; simpl in *.
      + destruct (string_dec s "$left").
        inversion H; clear H; subst; simpl in *.
        inversion H0; clear H0; subst; simpl in *.
        inversion H1; clear H1; subst; simpl in *.
        rewrite (H3 H5); reflexivity.
        destruct (string_dec s "$right").
        inversion H; clear H; subst; simpl in *.
        inversion H0; clear H0; subst; simpl in *.
        inversion H1; clear H1; subst; simpl in *.
        rewrite (H3 H5); reflexivity.
        simpl in *.
        destruct (string_dec s "$left"); try congruence.
        destruct (string_dec s "$right"); try congruence.
        inversion H; clear H; subst; simpl in *.
        inversion H0; clear H0 H2; subst; simpl in *.
        inversion H1; clear H1; subst; simpl in *.
        specialize (H3 H2); clear H2.
        rewrite H3; reflexivity.
      + inversion H; clear H; subst; simpl in *.
        inversion H0; clear H0; subst; simpl in *.
        destruct p; simpl in *.
        inversion H1; clear H1; subst; simpl in *.
        inversion H6; clear H6; subst; simpl in *.
        rewrite (H3 H5); f_equal; f_equal.
        inversion H4; clear H4; subst; simpl in *.
        rewrite (H6 H1); f_equal.
        clear H2 H6 H3.
        induction r; try reflexivity.
        inversion H7; clear H7; subst; simpl in *.
        inversion H8; clear H8; subst; simpl in *.
        specialize (IHr H3 H6); clear H3 H6.
        rewrite (H4 H2); f_equal.
        rewrite IHr; reflexivity.
    - inversion H; clear H; subst.
      rewrite (IHd H1); reflexivity.
    - inversion H; clear H; subst.
      rewrite (IHd H1); reflexivity.
    - inversion H; clear H; subst.
      rewrite (IHd H3); reflexivity.
  Qed.

End JSON.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
