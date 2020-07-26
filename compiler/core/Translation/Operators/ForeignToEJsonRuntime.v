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

Require Import EquivDec.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import Utils.
Require Import DataRuntime.
Require Import EJsonRuntime.
Require Import ForeignDataToEJson.
Require Import DataToEJson.

Section ForeignToEJsonRuntime.

  Class foreign_to_ejson_runtime
        {fruntime:foreign_runtime}
        {fejson:foreign_ejson}
        {fetojson:foreign_to_ejson}
        {fejsonops:foreign_ejson_runtime}
      : Type
      := mk_foreign_to_ejson_runtime {
             foreign_to_ejson_runtime_of_unary_op
               (uop:foreign_operators_unary) : foreign_ejson_runtime_op
             ; foreign_to_ejson_runtime_of_unary_op_correct
                 (uop:foreign_operators_unary)
                 (br:brand_relation_t)
                 (d:data) :
                 lift data_to_ejson (foreign_operators_unary_interp br uop d) =
                 foreign_ejson_runtime_op_interp (foreign_to_ejson_runtime_of_unary_op uop)
                                                 (data_to_ejson d::nil)
             ; foreign_to_ejson_runtime_of_binary_op
               (bop:foreign_operators_binary) : foreign_ejson_runtime_op
             ; foreign_to_ejson_runtime_of_binary_op_correct
                 (bop:foreign_operators_binary)
                 (br:brand_relation_t)
                 (d1 d2:data) :
                 lift data_to_ejson (foreign_operators_binary_interp br bop d1 d2) =
                 foreign_ejson_runtime_op_interp (foreign_to_ejson_runtime_of_binary_op bop)
                                                 (data_to_ejson d1::data_to_ejson d2::nil)
             ; foreign_to_ejson_runtime_tostring_correct
                 (d:data) :
                 foreign_operators_unary_data_tostring d =
                 foreign_ejson_runtime_tostring (data_to_ejson d)
             ; foreign_to_ejson_runtime_totext_correct
                 (d:data) :
                 foreign_operators_unary_data_totext d =
                 foreign_ejson_runtime_totext (data_to_ejson d)
         }.

  Section defaultToString.
    Context {fruntime:foreign_runtime}.
    Context {fejson:foreign_ejson}.
    Context {fetojson:foreign_to_ejson}.

    Ltac rewrite_string_dec_from_neq H
      :=  let d := fresh "d" in
          let neq := fresh "neq" in
          destruct (string_dec_from_neq H) as [d neq]
          ; repeat rewrite neq in *
          ; clear d neq.

    Lemma map_tostring_comm1 r :
      map
        (fun '(x, y) =>
           (stringToString (key_decode x) ++ String "-" (String ">" (defaultEJsonToString y)))%string)
        (map (fun x : string * data => (key_encode (fst x), data_to_ejson (snd x))) r)
      = map (fun '(x, y) => (stringToString x ++ String "-" (String ">" (defaultEJsonToString y)))%string)
            (map (fun x : string * data => (fst x, data_to_ejson (snd x))) r).
    Proof.
      repeat rewrite map_map.
      rewrite (map_eq (f:=(fun x : string * data =>
                             (stringToString (key_decode (key_encode (fst x))) ++
                                             String "-" (String ">" (defaultEJsonToString (data_to_ejson (snd x))))))%string) (g:=(fun x : string * data =>
                                                                                                                                     (stringToString (fst x) ++ String "-" (String ">" (defaultEJsonToString (data_to_ejson (snd x)))))%string))); try reflexivity.
      rewrite Forall_forall; intros.
      rewrite key_encode_decode. reflexivity.
    Qed.

    Lemma default_ejson_rec_aux1 j r :
      ejson_is_record j = Some r ->
      defaultEJsonToString j =         string_bracket
          "{"%string
          (String.concat ", "%string
                         (map (fun xy => let '(x,y):=xy in
                                         (append (stringToString (key_decode x)) (append "->"%string (defaultEJsonToString y)))
                              ) r))
          "}"%string.
    Proof.
      intros.
      destruct j; simpl in *; try congruence;
      destruct l; simpl in *; try congruence; [inversion H; subst; reflexivity|];
      destruct p; simpl in *; try congruence.
      destruct e; simpl in *; try congruence;
        try (destruct l; simpl in *; try congruence;
             destruct (string_dec s "$left"); simpl in *; try congruence;
             destruct (string_dec s "$right"); simpl in *; try congruence;
             inversion H; simpl in *; try congruence;
             destruct p; simpl in *; congruence).
      destruct l; simpl in *; try congruence.
      - destruct (string_dec s "$left"); simpl in *; try congruence;
             destruct (string_dec s "$right"); simpl in *; try congruence;
             inversion H; simpl in *; try congruence;
             destruct p; simpl in *; congruence.
      - destruct p; simpl in *; try congruence.
        destruct (string_dec s "$class"); simpl in *; try congruence;
          destruct (string_dec s0 "$data"); simpl in *; try congruence;
            destruct l; simpl in *; try congruence;
        destruct (ejson_brands l0); try congruence; simpl in *;
        repeat f_equal;
        inversion H; simpl in *; subst; try reflexivity.
    Qed.

    Lemma default_ejson_rec_aux2 r:
      Forall
        (fun ab : string * data => defaultDataToString (snd ab) = defaultEJsonToString (data_to_ejson (snd ab)))
        r ->
      defaultDataToString (drec r) = defaultEJsonToString (data_to_ejson (drec r)).
    Proof.
      intros.
      specialize (default_ejson_rec_aux1 (data_to_ejson (drec r))); intros.
      specialize (H0 (map (fun x => (key_encode (fst x), data_to_ejson (snd x))) r) (ejson_record_of_record r)).
      rewrite H0; clear H0.
      rewrite map_map; simpl.
      f_equal; f_equal.
      rewrite (map_eq (f:=(fun '(x, y) =>
                             (stringToString x ++ String "-" (String ">" (defaultDataToString y)))%string))
               (g:=(fun x : string * data =>
                      (stringToString (key_decode (key_encode (fst x))) ++
                                      String "-" (String ">" (defaultEJsonToString (data_to_ejson (snd x)))))%string))); [reflexivity|].
      rewrite Forall_forall in *; intros.
      destruct x; simpl in *.
      specialize (H (s,d) H0); clear H0; simpl in *.
      rewrite <- H.
      rewrite key_encode_decode; reflexivity.
    Qed.

    Lemma default_to_ejson_tostring_correct :
      (forall fd : foreign_data_model,
          toString fd = toString (foreign_to_ejson_from_data fd)) ->
      forall d:data, defaultDataToString d = defaultEJsonToString (data_to_ejson d).
    Proof.
      intros Hforeign.
      induction d; try reflexivity.
      - simpl; rewrite map_map.
        rewrite (map_eq (f:=defaultDataToString) (g:=(fun x => defaultEJsonToString (data_to_ejson x))) H).
        reflexivity.
      - rewrite default_ejson_rec_aux2; [|apply H]; reflexivity.
      - simpl; rewrite IHd.
        destruct (data_to_ejson d); reflexivity.
      - simpl; rewrite IHd.
        destruct (data_to_ejson d); reflexivity.
      - simpl; rewrite IHd.
        rewrite ejson_brands_map_ejstring; reflexivity.
      - simpl; rewrite Hforeign; reflexivity.
    Qed.

  End defaultToString.
End ForeignToEJsonRuntime.

