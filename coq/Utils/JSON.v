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
  Require Import List.
  Require Import String.
  Require Import ZArith.
  Require Import CoqLibAdd.
  
  Unset Elimination Schemes.

  Inductive json : Set :=
  | jnil : json
  | jnumber : Z -> json
  | jbool : bool -> json
  | jstring : string -> json
  | jarray : list json -> json
  | jobject : list (string * json) -> json
  .

  Set Elimination Schemes.

  (** Induction principles used as backbone for inductive proofs on json *)
  Definition json_rect (P : json -> Type)
             (fnil : P jnil)
             (fnumber : forall n : Z, P (jnumber n))
             (fbool : forall b : bool, P (jbool b))
             (fstring : forall s : string, P (jstring s))
             (farray : forall c : list json, Forallt P c -> P (jarray c))
             (fobject : forall r : list (string * json), Forallt (fun ab => P (snd ab)) r -> P (jobject r))
    :=
      fix F (j : json) : P j :=
    match j as j0 return (P j0) with
      | jnil => fnil
      | jnumber x => fnumber x
      | jbool x => fbool x
      | jstring x => fstring x
      | jarray x => farray x ((fix F2 (c : list json) : Forallt P c :=
                            match c as c0 with
                              | nil => Forallt_nil _
                              | cons j c0 => @Forallt_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | jobject x => fobject x ((fix F3 (r : list (string*json)) : Forallt (fun ab => P (snd ab)) r :=
                           match r as c0 with
                             | nil => Forallt_nil _
                             | cons sj c0 => @Forallt_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
    end.

  Definition json_ind (P : json -> Prop)
             (fnil : P jnil)
             (fnumber : forall n : Z, P (jnumber n))
             (fbool : forall b : bool, P (jbool b))
             (fstring : forall s : string, P (jstring s))
             (farray : forall c : list json, Forall P c -> P (jarray c))
             (fobject : forall r : list (string * json), Forall (fun ab => P (snd ab)) r -> P (jobject r))
    :=
      fix F (j : json) : P j :=
    match j as j0 return (P j0) with
      | jnil => fnil
      | jnumber x => fnumber x
      | jbool x => fbool x
      | jstring x => fstring x
      | jarray x => farray x ((fix F2 (c : list json) : Forall P c :=
                            match c with
                              | nil => Forall_nil _
                              | cons j c0 => @Forall_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | jobject x => fobject x ((fix F3 (r : list (string*json)) : Forall (fun ab => P (snd ab)) r :=
                           match r with
                             | nil => Forall_nil _
                             | cons sj c0 => @Forall_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
    end.

  Definition json_rec (P:json->Set) := json_rect P.
  
  Lemma jsonInd2 (P : json -> Prop)
        (f : P jnil)
        (f0 : forall n : Z, P (jnumber n))
        (fb : forall b : bool, P (jbool b))
        (f1 : forall s : string, P (jstring s))
        (f2 : forall c : list json, (forall x, In x c -> P x) -> P (jarray c))
        (f3 : forall r : list (string * json), (forall x y, In (x,y) r -> P y) -> P (jobject r)):
    forall d, P d.
  Proof.
    intros.
    apply json_ind; trivial.
    - intros. rewrite Forall_forall in H.
      auto.
    - intros. rewrite Forall_forall in H.
      apply f3.
      intros. apply (H (x,y)). trivial.
  Qed.

  Section toString.
    Require Import Ascii.
    Require Import String.
    Require Import StringAdd.
    Require Import Digits.

    Local Open Scope string.

    Definition js_quote_char (a:ascii)
      := match a with
         | """"%char => "\"""
         | _ => String a EmptyString
         end.

    Definition js_quote_string (s:string)
      := flat_map_string js_quote_char s.

    Definition stringToJS (quotel:string) (s:string)
      := "" ++ quotel ++ "" ++ js_quote_string s ++ "" ++ quotel ++ "".

    Fixpoint jsonToJS (quotel:string) (j : json) : string
      := match j with
         | jnil => "null" (* to be discussed *)
         | jnumber n => Z_to_string10 n
         | jbool b => if b then "true" else "false"
         | jstring s => stringToJS quotel s
         | jarray ls =>
           let ss := map (jsonToJS quotel) ls in
           "[" ++ (joinStrings ", " ss) ++ "]"
         | jobject ls =>
           let ss := (map (fun kv => let '(k,v) := kv in
                                     "" ++ quotel ++ "" ++ k ++ "" ++ quotel ++ ": " ++ (jsonToJS quotel v)) ls) in
           "{" ++ (joinStrings ", " ss) ++ "}"
         end.

  End toString.
  
End JSON.

