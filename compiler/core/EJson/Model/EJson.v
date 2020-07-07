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
Require Import ForeignEJson.
Require Import Utils.

Section EJson.
  Context {fejson:foreign_ejson}.

  Unset Elimination Schemes.

  Inductive ejson : Set :=
  | ejnull : ejson
  | ejnumber : float -> ejson
  | ejbigint : Z -> ejson
  | ejbool : bool -> ejson
  | ejstring : string -> ejson
  | ejarray : list ejson -> ejson
  | ejobject : list (string * ejson) -> ejson
  | ejforeign : foreign_ejson_model -> ejson
  .

  Set Elimination Schemes.

  (** Induction principles used as backbone for inductive proofs on json *)
  Definition ejson_rect (P : ejson -> Type)
             (fnull : P ejnull)
             (fnumber : forall n : number, P (ejnumber n))
             (fbigint : forall n : Z, P (ejbigint n))
             (fbool : forall b : bool, P (ejbool b))
             (fstring : forall s : string, P (ejstring s))
             (farray : forall c : list ejson, Forallt P c -> P (ejarray c))
             (fobject : forall r : list (string * ejson), Forallt (fun ab => P (snd ab)) r -> P (ejobject r))
             (fforeign: forall fd, P (ejforeign fd))
    :=
      fix F (j : ejson) : P j :=
    match j as j0 return (P j0) with
      | ejnull => fnull
      | ejnumber x => fnumber x
      | ejbigint x => fbigint x
      | ejbool x => fbool x
      | ejstring x => fstring x
      | ejarray x => farray x ((fix F2 (c : list ejson) : Forallt P c :=
                            match c as c0 with
                              | nil => Forallt_nil _
                              | cons j c0 => @Forallt_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | ejobject x => fobject x ((fix F3 (r : list (string*ejson)) : Forallt (fun ab => P (snd ab)) r :=
                           match r as c0 with
                             | nil => Forallt_nil _
                             | cons sj c0 => @Forallt_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
      | ejforeign fd => fforeign fd
    end.

  Definition ejson_ind (P : ejson -> Prop)
             (fnull : P ejnull)
             (fnumber : forall n : number, P (ejnumber n))
             (fbigint : forall n : Z, P (ejbigint n))
             (fbool : forall b : bool, P (ejbool b))
             (fstring : forall s : string, P (ejstring s))
             (farray : forall c : list ejson, Forall P c -> P (ejarray c))
             (fobject : forall r : list (string * ejson), Forall (fun ab => P (snd ab)) r -> P (ejobject r))
             (fforeign: forall fd, P (ejforeign fd))
    :=
      fix F (j : ejson) : P j :=
    match j as j0 return (P j0) with
      | ejnull => fnull
      | ejnumber x => fnumber x
      | ejbigint x => fbigint x
      | ejbool x => fbool x
      | ejstring x => fstring x
      | ejarray x => farray x ((fix F2 (c : list ejson) : Forall P c :=
                            match c with
                              | nil => Forall_nil _
                              | cons j c0 => @Forall_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | ejobject x => fobject x ((fix F3 (r : list (string*ejson)) : Forall (fun ab => P (snd ab)) r :=
                           match r with
                             | nil => Forall_nil _
                             | cons sj c0 => @Forall_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
      | ejforeign fd => fforeign fd
    end.

  Definition ejson_rec (P:ejson->Set) := ejson_rect P.

  Lemma ejsonInd2 (P : ejson -> Prop)
        (f : P ejnull)
        (f0 : forall n : number, P (ejnumber n))
        (f1 : forall n : Z, P (ejbigint n))
        (f2 : forall b : bool, P (ejbool b))
        (f3 : forall s : string, P (ejstring s))
        (f4 : forall c : list ejson, (forall x, In x c -> P x) -> P (ejarray c))
        (f5 : forall r : list (string * ejson), (forall x y, In (x,y) r -> P y) -> P (ejobject r))
        (fforeign : forall fd, P (ejforeign fd)):
    forall d, P d.
  Proof.
    intros.
    apply ejson_ind; trivial.
    - intros. rewrite Forall_forall in H.
      auto.
    - intros. rewrite Forall_forall in H.
      apply f5.
      intros. apply (H (x,y)). trivial.
  Qed.

  (** Equality is decidable for json *)
  Lemma ejson_eq_dec : forall x y:ejson, {x=y}+{x<>y}.
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
    - destruct (foreign_ejson_dec fd f).
      + left. f_equal; apply e.
      + right. inversion 1; congruence.
  Defined.

  (* begin hide *)
  Global Instance ejson_eqdec : EqDec ejson eq := ejson_eq_dec.
  (* begin hide *)

  Section toString.

    Local Open Scope string.

    Fixpoint ejsonStringify (quotel:string) (j : ejson) : string
      := match j with
         | ejnull => "null"
         | ejnumber n => toString n
         | ejbigint n => toString n
         | ejbool b => toString b
         | ejstring s => stringToStringQuote quotel s
         | ejarray ls =>
           let ss := map (ejsonStringify quotel) ls in
           "[" ++ (concat ", " ss) ++ "]"
         | ejobject ls =>
           let ss := (map (fun kv =>
                             let '(k,v) := kv in
                             "" ++ quotel ++ "" ++ k ++ ""
                                ++ quotel ++ ": " ++ (ejsonStringify quotel v)) ls)
           in "{" ++ (concat ", " ss) ++ "}"
         | ejforeign fd => toString fd
         end.

  End toString.

  Section Util.
    Fixpoint of_string_list (d:list ejson) : option (list string) :=
      match d with
      | nil => Some nil
      | (ejstring s1) :: d' =>
        match of_string_list d' with
        | Some s' => Some (s1::s')
        | None => None
        end
      | _ => None
      end.

    Lemma of_string_list_map_ejstring sl :
      of_string_list (map ejstring sl) = Some sl.
    Proof.
      induction sl; try reflexivity; simpl.
      unfold of_string_list in *; simpl.
      rewrite IHsl; reflexivity.
    Qed.

    Lemma of_string_list_map_ejstring_f {A} (f:A -> string) (sl:list A) :
      of_string_list (map (fun x => (ejstring (f x))) sl) = Some (map f sl).
    Proof.
      induction sl; try reflexivity; simpl.
      unfold of_string_list in *; simpl.
      rewrite IHsl; reflexivity.
    Qed.

    Definition ejson_brands (d:list ejson) : option (list string) := of_string_list d.

    Lemma ejson_brands_map_ejstring b : ejson_brands (map ejstring b) = Some b.
    Proof.
      apply of_string_list_map_ejstring.
    Qed.
    
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

    Fixpoint ejson_numbers (d:list ejson) : option (list float) :=
      match d with
      | nil => Some nil
      | (ejnumber n) :: d' =>
        match ejson_numbers d' with
        | Some s' => Some (n::s')
        | None => None
        end
      | _ => None
      end.

    Fixpoint ejson_strings (d:list ejson) : option (list string) :=
      match d with
      | nil => Some nil
      | (ejstring n) :: d' =>
        match ejson_strings d' with
        | Some s' => Some (n::s')
        | None => None
        end
      | _ => None
      end.

    Definition jflatten (d:list ejson) : option (list ejson) :=
      lift_flat_map (fun x =>
                       match x with
                       | ejarray y => Some y
                       | _ => None end) d.
    
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

    Definition ejson_is_either (j:ejson) : option (option ejson * option ejson) :=
      match j with
      | ejobject ((s1,j')::nil) =>
        if (string_dec s1 "$left") then Some (Some j', None)
        else if (string_dec s1 "$right") then Some (None, Some j')
             else None
      | ejobject r => None
      | _ => None
      end.

  End Util.

  Section Env.
    Definition jbindings := list (string * ejson).
    Definition pd_jbindings := list (string * option ejson).
  End Env.

  Section CEJson.
    Inductive cejson : Set :=
    | cejnull : cejson
    | cejnumber : float -> cejson
    | cejbigint : Z -> cejson
    | cejbool : bool -> cejson
    | cejstring : string -> cejson
    | cejforeign : foreign_ejson_model -> cejson
    .

    Definition cejsonStringify (quotel:string) (j : cejson) : string
      := match j with
         | cejnull => "null"
         | cejnumber n => toString n
         | cejbigint n => toString n
         | cejbool b => toString b
         | cejstring s => stringToStringQuote quotel s
         | cejforeign fd => toString fd
         end.

  End CEJson.
End EJson.

