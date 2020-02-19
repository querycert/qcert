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

Section EJsonToEJsonMut.
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

  Section ListToNth.
    Fixpoint list_n_nat {A} (n:nat) (l:list A) :=
      match n with
      | 0 => nil
      | S n' =>
        match l with
        | nil => nil
        | x :: l' => x :: (list_n_nat n' l')
        end
      end.

    Definition list_n {A} (l:list A) (z:Z) :=
      list_n_nat (Z.to_nat z) l.

    Lemma list_n_nat_map_comm {A B} (l:list A) (f:A -> B) n :
      list_n_nat n (map f l) = map f (list_n_nat n l).
    Proof.
      revert l; induction n; intros; simpl.
      - reflexivity.
      - destruct l; simpl.
        + reflexivity.
        + rewrite IHn.
          reflexivity.
    Qed.

    Lemma list_n_map_comm {A B} (l:list A) (f:A -> B) z :
      list_n (map f l) z = map f (list_n l z).
    Proof.
      apply list_n_nat_map_comm.
    Qed.

    Lemma list_n_nat_of_length_id {A} (l:list A):
      list_n_nat (List.length l) l = l.
    Proof.
      induction l; simpl.
      - reflexivity.
      - rewrite IHl.
        reflexivity.
    Qed.
  
    Lemma list_n_of_length_id {A} (l:list A):
      list_n l (Z.of_nat (List.length l)) = l.
    Proof.
      unfold list_n; simpl.
      rewrite Nat2Z.id.
      apply list_n_nat_of_length_id.
    Qed.

  End ListToNth.

  Context {fejson:foreign_ejson}.

  Section toEJson.
    (* EJson to Data *)
    Fixpoint ejson_mut_to_ejson (j:ejson) : ejson :=
      match j with
      | ejnull => ejnull
      | ejnumber n => ejnumber n
      | ejbigint n => ejbigint n
      | ejbool b => ejbool b
      | ejstring s => ejstring s
      | ejarray c => ejarray (map ejson_mut_to_ejson c)
      | ejobject ((s1,ejarray j1)::(s2,ejbigint j2)::nil) =>
        if (string_dec s1 "$coll") then
          if (string_dec s2 "$length") then
            ejarray (list_n (map ejson_mut_to_ejson j1) j2)
          else ejobject ((s1,ejarray (map ejson_mut_to_ejson j1))::(s2,ejbigint j2)::nil)
        else ejobject ((key_decode s1, ejarray (map ejson_mut_to_ejson j1))::(key_decode s2, ejbigint j2)::nil)
      | ejobject r => ejobject (map (fun x => (key_decode (fst x), ejson_mut_to_ejson (snd x))) r)
      | ejforeign fd => ejforeign fd
      end.

  End toEJson.

  Section toEJsonMut.
    Fixpoint ejson_to_ejson_mut (d:ejson) : ejson :=
      match d with
      | ejnull => ejnull
      | ejbigint n => ejbigint n
      | ejnumber n => ejnumber n
      | ejbool b => ejbool b
      | ejstring s => ejstring s
      | ejarray c => ejobject (("$coll"%string, ejarray (map ejson_to_ejson_mut c))::("$length"%string, ejbigint (Z.of_nat (List.length c)))::nil)
      | ejobject r => ejobject (map (fun x => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r)
      | ejforeign fd => ejforeign fd
      end.

  End toEJsonMut.

  Section ModelRoundTrip.
    Lemma key_encode_not_coll s : (key_encode s) <> "$coll"%string.
    Proof.
      destruct s; simpl; try discriminate.
      repeat match_destr.
    Qed.

    Lemma key_encode_not_length s : (key_encode s) <> "$length"%string.
    Proof.
      destruct s; simpl; try discriminate.
      repeat match_destr.
    Qed.

    Lemma ejson_to_ejson_mut_idempotent j:
      ejson_mut_to_ejson (ejson_to_ejson_mut j) = j.
    Proof.
      induction j; simpl; trivial.
      - f_equal.
        rewrite list_n_map_comm.
        rewrite list_n_map_comm.
        rewrite map_map.
        rewrite list_n_of_length_id.
        apply map_eq_id; assumption.
      - destruct r; simpl; trivial.
        destruct p; simpl.
        rewrite_string_dec_from_neq (key_encode_not_coll s).
        rewrite_string_dec_from_neq (key_encode_not_length s).
        assert (eq_simpl:
                  (match ejson_to_ejson_mut e with
  | ejarray j1 =>
      match map (fun x : string * ejson => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r with
      | nil =>
          ejobject
            ((key_decode (key_encode s), ejson_mut_to_ejson (ejson_to_ejson_mut e))
             :: map (fun x : string * ejson => (key_decode (fst x), ejson_mut_to_ejson (snd x)))
                  (map (fun x : string * ejson => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r))
      | (s2, ejbigint j2) :: nil =>
          ejobject
            ((key_decode (key_encode s), ejarray (map ejson_mut_to_ejson j1))
             :: (key_decode s2, ejbigint j2) :: nil)
      | (s2, ejbigint j2) :: _ :: _ =>
          ejobject
            ((key_decode (key_encode s), ejson_mut_to_ejson (ejson_to_ejson_mut e))
             :: map (fun x : string * ejson => (key_decode (fst x), ejson_mut_to_ejson (snd x)))
                  (map (fun x : string * ejson => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r))
      | (s2, ejnull) :: _ | (s2, ejnumber _) :: _ | (s2, ejbool _) :: _ | (s2, ejstring _) :: _ |
        (s2, ejarray _) :: _ | (s2, ejobject _) :: _ | (s2, ejforeign _) :: _ =>
          ejobject
            ((key_decode (key_encode s), ejson_mut_to_ejson (ejson_to_ejson_mut e))
             :: map (fun x : string * ejson => (key_decode (fst x), ejson_mut_to_ejson (snd x)))
                  (map (fun x : string * ejson => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r))
      end
  | _ =>
      ejobject
        ((key_decode (key_encode s), ejson_mut_to_ejson (ejson_to_ejson_mut e))
         :: map (fun x : string * ejson => (key_decode (fst x), ejson_mut_to_ejson (snd x)))
              (map (fun x : string * ejson => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r))
  end = ejobject ((key_decode (key_encode s), ejson_mut_to_ejson (ejson_to_ejson_mut e))::(map (fun x : string * ejson => (key_decode (fst x), ejson_mut_to_ejson (snd x))) (map (fun x : string * ejson => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r))))).
        {
          destruct (ejson_to_ejson_mut e); simpl
          ; destruct (map (fun x : string * ejson => (key_encode (fst x), ejson_to_ejson_mut (snd x))) r      ); simpl; trivial
          ; destruct p
          ; destruct e0; simpl; trivial
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
    Qed.

    (* Means we can do inversion on ejson_to_ejson_mut *)
    Lemma ejson_to_ejson_mut_inv j1 j2:
      ejson_to_ejson_mut j1 = ejson_to_ejson_mut j2 -> j1 = j2.
    Proof.
      intros.
      rewrite <- (ejson_to_ejson_mut_idempotent j1).
      rewrite <- (ejson_to_ejson_mut_idempotent j2).
      rewrite H.
      reflexivity.
    Qed.

    Lemma ejson_to_ejson_mut_equiv j1 j2:
      ejson_to_ejson_mut j1 = ejson_to_ejson_mut j2 <-> j1 = j2.
    Proof.
      split; intros; subst.
      - apply ejson_to_ejson_mut_inv; assumption.
      - reflexivity.
    Qed.
  End ModelRoundTrip.

End EJsonToEJsonMut.
