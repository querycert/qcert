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
Require Import Ascii.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import JsAst.JsNumber.
Require Import Float.
Require Import ToString.
Require Import CoqLibAdd.
Require Import StringAdd.
Require Import Digits.
Require Import EquivDec.

Section JSON.
  Unset Elimination Schemes.

  Inductive json : Set :=
  | jnull : json
  | jnumber : float -> json
  | jbigint : Z -> json
  | jbool : bool -> json
  | jstring : string -> json
  | jarray : list json -> json
  | jobject : list (string * json) -> json
  .

  Set Elimination Schemes.

  (** Induction principles used as backbone for inductive proofs on json *)
  Definition json_rect (P : json -> Type)
             (fnull : P jnull)
             (fnumber : forall n : number, P (jnumber n))
             (fbigint : forall n : Z, P (jbigint n))
             (fbool : forall b : bool, P (jbool b))
             (fstring : forall s : string, P (jstring s))
             (farray : forall c : list json, Forallt P c -> P (jarray c))
             (fobject : forall r : list (string * json), Forallt (fun ab => P (snd ab)) r -> P (jobject r))
    :=
      fix F (j : json) : P j :=
    match j as j0 return (P j0) with
      | jnull => fnull
      | jnumber x => fnumber x
      | jbigint x => fbigint x
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
             (fnull : P jnull)
             (fnumber : forall n : number, P (jnumber n))
             (fbigint : forall n : Z, P (jbigint n))
             (fbool : forall b : bool, P (jbool b))
             (fstring : forall s : string, P (jstring s))
             (farray : forall c : list json, Forall P c -> P (jarray c))
             (fobject : forall r : list (string * json), Forall (fun ab => P (snd ab)) r -> P (jobject r))
    :=
      fix F (j : json) : P j :=
    match j as j0 return (P j0) with
      | jnull => fnull
      | jnumber x => fnumber x
      | jbigint x => fbigint x
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
        (f : P jnull)
        (f0 : forall n : number, P (jnumber n))
        (f1 : forall n : Z, P (jbigint n))
        (f2 : forall b : bool, P (jbool b))
        (f3 : forall s : string, P (jstring s))
        (f4 : forall c : list json, (forall x, In x c -> P x) -> P (jarray c))
        (f5 : forall r : list (string * json), (forall x y, In (x,y) r -> P y) -> P (jobject r)):
    forall d, P d.
  Proof.
    intros.
    apply json_ind; trivial.
    - intros. rewrite Forall_forall in H.
      auto.
    - intros. rewrite Forall_forall in H.
      apply f5.
      intros. apply (H (x,y)). trivial.
  Qed.

  (** Equality is decidable for json *)
  Lemma json_eq_dec : forall x y:json, {x=y}+{x<>y}.
  Proof.
    induction x; destruct y; try solve[right; inversion 1].
    - left; trivial.
    - destruct (float_eq_dec n f).
      + left; f_equal; trivial.
      + right;intro;apply c;inversion H; reflexivity.
    - destruct (Z.eq_dec n z).
      + left; f_equal; trivial.
      + right;intro;apply n0;inversion H; trivial.
    - destruct (bool_dec b b0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial. 
    - destruct (string_dec s s0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial.
    - destruct (list_Forallt_eq_dec c l H). subst. auto.
      right; inversion 1. auto.
    - destruct (list_Forallt_eq_dec r l); subst; auto.
      + apply (forallt_impl H).
        apply forallt_weaken; clear; intros.
        destruct x; destruct y; simpl in *.
        apply pair_eq_dec; auto.
        apply string_dec.
      + right; inversion 1; auto.
  Defined.

  (* begin hide *)
  Global Instance json_eqdec : EqDec json eq := json_eq_dec.
  (* begin hide *)

  Section toString.

    Local Open Scope string.

    Fixpoint jsonStringify (quotel:string) (j : json) : string
      := match j with
         | jnull => "null"
         | jnumber n => toString n
         | jbigint n => toString n
         | jbool b => toString b
         | jstring s => stringToStringQuote quotel s
         | jarray ls =>
           let ss := map (jsonStringify quotel) ls in
           "[" ++ (concat ", " ss) ++ "]"
         | jobject ls =>
           let ss := (map (fun kv =>
                             let '(k,v) := kv in
                             "" ++ quotel ++ "" ++ k ++ ""
                                ++ quotel ++ ": " ++ (jsonStringify quotel v)) ls)
           in "{" ++ (concat ", " ss) ++ "}"
         end.

  End toString.

  Section preProcess.
    Fixpoint json_to_qjson (j:json) : json :=
      match j with
      | jnull => jnull
      | jnumber n => jnumber n
      | jbigint n => jbigint n
      | jbool b => jbool b
      | jstring s => jstring s
      | jarray c => jarray (map json_to_qjson c)
      | jobject nil => jobject nil
      | jobject ((s1,j')::nil) =>
        if (string_dec s1 "$nat") then
          match j' with
          | jnumber n => jobject ((s1, jbigint (float_truncate n))::nil)
          | _ => jobject ((s1, json_to_qjson j')::nil)
          end
        else jobject ((s1, json_to_qjson j')::nil)
      | jobject r => jobject (map (fun x => (fst x, json_to_qjson (snd x))) r)
      end.

    Fixpoint qjson_to_json (j:json) : json :=
      match j with
      | jnull => jnull
      | jnumber n => jnumber n
      | jbigint n => jbigint n
      | jbool b => jbool b
      | jstring s => jstring s
      | jarray c => jarray (map qjson_to_json c)
      | jobject nil => jobject nil
      | jobject ((s1,j')::nil) =>
        if (string_dec s1 "$nat") then
          match j' with
          | jbigint n => jobject ((s1, jnumber (float_of_int n))::nil)
          | _ => jobject ((s1, qjson_to_json j')::nil)
          end
        else jobject ((s1, qjson_to_json j')::nil)
      | jobject r => jobject (map (fun x => (fst x, qjson_to_json (snd x))) r)
      end.

  End preProcess.
End JSON.
