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

Require Import String.
Require Import List.
Require Import Sumbool.
Require Import ZArith.
Require Import Bool.
Require Import EquivDec.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import EquivDec.

Section Data.

  (** Data is:
     - unit - used for undefined results.
     - nat - an integer
     - float - a floating point number (IEEE 754 double precision)
     - bool - true or false
     - string - a character string
     - coll - a bag
     - rec - a record
     - left - left sum value
     - right - right sum value
     - foreign - foreign data
   *)

  Unset Elimination Schemes.

  Context {fdata:foreign_data}.

  Inductive data : Set :=
  | dunit : data
  | dnat : Z -> data
  | dfloat : float -> data
  | dbool : bool -> data
  | dstring : string -> data
  | dcoll : list data -> data
  | drec : list (string * data) -> data
  | dleft : data -> data
  | dright : data -> data
  | dbrand : brands -> data -> data
  | dforeign : foreign_data_type -> data
  .

  Set Elimination Schemes.

  (** Induction principles used as backbone for inductive proofs on data *)
  Definition data_rect (P : data -> Type)
             (funit : P dunit)
             (fnat : forall n : Z, P (dnat n))
             (ffloat : forall f : float, P (dfloat f))
             (fbool : forall b : bool, P (dbool b))
             (fstring : forall s : string, P (dstring s))
             (fcoll : forall c : list data, Forallt P c -> P (dcoll c))
             (frec : forall r : list (string * data), Forallt (fun ab => P (snd ab)) r -> P (drec r))
             (fleft: forall d, P d -> P (dleft d))
             (fright: forall d, P d -> P (dright d))
             (fbrand: forall b d, P d -> P (dbrand b d))
             (fforeign: forall fd, P (dforeign fd))
    :=
      fix F (d : data) : P d :=
    match d as d0 return (P d0) with
      | dunit => funit
      | dnat x => fnat x
      | dfloat x => ffloat x
      | dbool x => fbool x
      | dstring x => fstring x
      | dcoll x => fcoll x ((fix F2 (c : list data) : Forallt P c :=
                            match c as c0 with
                              | nil => Forallt_nil _
                              | cons d c0 => @Forallt_cons _ P d c0 (F d) (F2 c0)
                            end) x)
      | drec x => frec x ((fix F3 (r : list (string*data)) : Forallt (fun ab => P (snd ab)) r :=
                           match r as c0 with
                             | nil => Forallt_nil _
                             | cons sd c0 => @Forallt_cons _ (fun ab => P (snd ab)) sd c0 (F (snd sd)) (F3 c0)
                           end) x)
      | dleft x => fleft _ (F x)
      | dright x => fright _ (F x)
      | dbrand b x => fbrand b _ (F x)
      | dforeign fd => fforeign fd
    end.

  Definition data_ind (P : data -> Prop)
             (funit : P dunit)
             (fnat : forall n : Z, P (dnat n))
             (ffloat : forall n : float, P (dfloat n))
             (fbool : forall b : bool, P (dbool b))
             (fstring : forall s : string, P (dstring s))
             (fcoll : forall c : list data, Forall P c -> P (dcoll c))
             (frec : forall r : list (string * data), Forall (fun ab => P (snd ab)) r -> P (drec r))
             (fleft: forall d, P d -> P (dleft d))
             (fright: forall d, P d -> P (dright d))
             (fbrand: forall b d, P d -> P (dbrand b d))
             (fforeign: forall fd, P (dforeign fd))
    :=
      fix F (d : data) : P d :=
    match d as d0 return (P d0) with
      | dunit => funit
      | dnat x => fnat x
      | dfloat x => ffloat x
      | dbool x => fbool x
      | dstring x => fstring x
      | dcoll x => fcoll x ((fix F2 (c : list data) : Forall P c :=
                            match c with
                              | nil => Forall_nil _
                              | cons d c0 => @Forall_cons _ P d c0 (F d) (F2 c0)
                            end) x)
      | drec x => frec x ((fix F3 (r : list (string*data)) : Forall (fun ab => P (snd ab)) r :=
                           match r with
                             | nil => Forall_nil _
                             | cons sd c0 => @Forall_cons _ (fun ab => P (snd ab)) sd c0 (F (snd sd)) (F3 c0)
                           end) x)
      | dleft d => fleft d (F d)
      | dright d => fright d (F d)
      | dbrand b d => fbrand b d (F d)
      | dforeign fd => fforeign fd
    end.

  Definition data_rec (P:data->Set) := data_rect P.
  
  Lemma dataInd2 (P : data -> Prop)
        (f : P dunit)
        (f0 : forall n : Z, P (dnat n))
        (fn : forall f : float, P (dfloat f))
        (fb : forall b : bool, P (dbool b))
        (f1 : forall s : string, P (dstring s))
        (f2 : forall c : list data, (forall x, In x c -> P x) -> P (dcoll c))
        (f3 : forall r : list (string * data), (forall x y, In (x,y) r -> P y) -> P (drec r))
        (f4 : forall d, P d -> P (dleft d))
        (f5 : forall d, P d -> P (dright d))
        (f6 : forall b d, P d -> P (dbrand b d))
        (fforeign : forall fd, P (dforeign fd)):
    forall d, P d.
  Proof.
    intros.
    apply data_ind; trivial.
    - intros. rewrite Forall_forall in H.
      auto.
    - intros. rewrite Forall_forall in H.
      apply f3.
      intros. apply (H (x,y)). trivial.
  Qed.

  Lemma brand_eq_dec : EqDec brand eq.
  Proof.
    repeat red. apply string_dec.
  Defined.

  (** Equality is decidable for data *)
  Lemma data_eq_dec : forall x y:data, {x=y}+{x<>y}.
  Proof.
    induction x; destruct y; try solve[right; inversion 1].
    - left; trivial.
    - destruct (Z.eq_dec n z).
      + left; f_equal; trivial.
      + right;intro;apply n0;inversion H; trivial.
    - destruct (float_eq_dec f f0).
      + left; f_equal; trivial.
      + right;intro;apply c;inversion H; reflexivity.
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
    - destruct (IHx y).
      + left. subst; trivial.
      + right; inversion 1; auto.
    - destruct (IHx y).
      + left. subst; trivial.
      + right; inversion 1; auto.
    - destruct (b == b0); unfold equiv, complement in *.
      + destruct (IHx y); [left|right]; congruence.
      + right; congruence.
    - destruct (foreign_data_dec fd f).
      + left. f_equal; apply e.
      + right. inversion 1; congruence.
  Defined.

  (* begin hide *)
  Global Instance data_eqdec : EqDec data eq := data_eq_dec.
  (* begin hide *)

  (* Equality is decidable for tables *)
  Lemma rec_eq_dec : forall x y: list (string*data), {x=y}+{x<>y}.
  Proof.
    intros.
    apply (list_Forallt_eq_dec x y).
    apply forallt_weaken.
    destruct x0; destruct y0.
    apply pair_eq_dec.
    apply string_dec.
    apply data_eq_dec.
  Defined.

  (* begin hide *)
  Global Instance rec_eqdec : EqDec (list (string*data)) eq := rec_eq_dec.
  (* end hide *)

  (* synonyms for option as either *)
  Definition dsome x := dleft x.
  Definition dnone := dright dunit.

  Definition bindings := list (string*data).

End Data.

(* begin hide *)
Class ConstLiteral {fdata:foreign_data} (A:Type)
      := dconst : A -> data.

Global Instance ConstLiteral_nat {fdata:foreign_data} : ConstLiteral Z
  := dnat.

Global Instance ConstLiteral_float {fdata:foreign_data} : ConstLiteral float
  := dfloat.

Global Instance ConstLiteral_bool {ftype:foreign_data} : ConstLiteral bool 
  := dbool.

Global Instance ConstLiteral_string {fdata:foreign_data} : ConstLiteral string 
  := dstring.

(* end hide *)

