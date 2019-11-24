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

Require Import Basics.
Require Import List.
Require Import String.
Require Import EquivDec.
Require Import Types.
Require Import Utils.
Require Import CommonRuntime.
Require Import ForeignDataTyping.
Require Import ForeignToJavaScript.

Section DatatoSparkDF.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.
  Context {fttojs: foreign_to_javascript}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Definition data_to_blob (d: data): string :=
    jsonToJS quotel_double (data_to_json d).

  Lemma dataToJS_correctly_escapes_quote_inside_string:
    data_to_blob (dstring "abc""cde") = """abc\""cde"""%string.
  Proof.
    reflexivity.
  Qed.
  
  Fixpoint typed_data_to_json (d: data) (r: rtype₀): option json :=
    match d, r with
    | _, Top₀ => Some (jstring (data_to_blob d))
    | dunit, Unit₀ => Some jnull
    | dnat i, Nat₀ => Some (jnumber (float_of_int i))
    | dfloat i, Float₀ => Some (jnumber i)
    | dbool b, Bool₀ => Some (jbool b)
    | dstring s, String₀ => Some (jstring s)
    | dcoll xs, (Coll₀ et) =>
      let listo := map (flip typed_data_to_json et) xs in
      lift jarray (listo_to_olist listo)
    | drec fs, Rec₀ Closed ft =>
      let fix convert_fields ds ts :=
          match ds, ts with
          | nil, nil => Some nil
          | nil, _ => None
          | _, nil => None
          | ((f, d)::ds), ((_, t)::ts) =>
            match typed_data_to_json d t, convert_fields ds ts with
            | Some json, Some tail => Some ((f, json)::tail)
            | _, _ => None
            end
          end in
      lift (fun fields => jobject (("$blob"%string, jstring "")
                                     :: ("$known"%string, jobject fields) :: nil))
           (convert_fields fs ft)
    | drec fs, Rec₀ Open ft =>
      (* Put typed fields in typed part, leftover fields in .. part *)
      let fix convert_known_fields ds ts us :=
          match ts, ds with
          (* No more typed fields, return leftover .. fields *)
          | nil, ds => Some (nil, us ++ ds)
          | _, nil => None
          | ((tf, t)::ts), ((df, d)::ds) =>
            if string_dec tf df
            then match typed_data_to_json d t, convert_known_fields ds ts us with
                 | Some json, Some (tail, us) => Some (((tf, json)::tail), us)
                 | _, _ => None
                 end
            else
              convert_known_fields ds ts ((df, d)::us)
          end in
      (* I'm not sure the dotdot fields are in the correct order, might need to sort them. *)
      match convert_known_fields fs ft nil with
      | Some (typed_fields, dotdot) =>
        Some (jobject (("$blob"%string, jstring (data_to_blob (drec dotdot)))
                         :: ("$known"%string, jobject typed_fields) :: nil))
      | None => None
      end
    | dleft l, Either₀ lt rt =>
      lift (fun l => jobject (("$left"%string, l)::("$right"%string, jnull)::nil))
           (typed_data_to_json l lt)
    | dright r, Either₀ lt rt =>
      lift (fun r => jobject (("$left"%string, jnull)::("$right"%string, r)::nil))
           (typed_data_to_json r rt)
    | dbrand bs v, Brand₀ bts =>
      (* Recursive brands are an issue. Solution: blob out the data in a brand. *)
      Some (jobject (("$data"%string, jstring (data_to_blob v))
                       :: ("$type"%string, jarray (map jstring bs)) :: nil))
    | _, _ => None
    end.


  Definition typed_data_to_json_string (d: data) (r: rtype): string :=
    match typed_data_to_json d (proj1_sig r) with
    | Some json => jsonToJS """" json
    (* Uhmm... this only works if we also have a proof that this d has this type r...
     * d ◁ r is the notation, if I remember correctly *)
    | None => "typed_data_to_json_string failed. This cannot happen. Get rid of this case by proving that typed_data_to_json always succeeds for well-typed data."
    end.

  (* XXX TO BE LOOKED AT FOR jsnumber
  Lemma test_json_with_toplevel_brand:
    (typed_data_to_json
       (dbrand ("Person"%string::nil)
               (drec (("age"%string, dnat 35)
                        :: ("name"%string, dstring "Fred")
                        :: ("friends"%string, dcoll ((dbrand ("Person"%string::nil)
                                                             (drec (("age"%string, dnat 42)
                                                                      :: ("name"%string, dstring "Berta")
                                                                      :: ("friends"%string, dcoll nil) :: nil))) :: nil)) :: nil)))
       (Brand₀ ("Person"%string::nil)))
    = Some
        (jobject
           (("$data"%string,
             jstring
               "{""age"": 35, ""name"": ""Fred"", ""friends"": [{""type"": [""Person""], ""data"": {""age"": 42, ""name"": ""Berta"", ""friends"": []}}]}")
              :: ("$type"%string, jarray (jstring "Person" :: nil)) :: nil)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma test_json_with_nested_brand:
    (typed_data_to_json
       (drec (("age"%string, dnat 35)
                :: ("name"%string, dstring "Fred")
                :: ("friends"%string, dcoll ((dbrand ("Person"%string::nil)
                                                     (drec (("age"%string, dnat 42)
                                                              :: ("name"%string, dstring "Berta")
                                                              :: ("friends"%string, dcoll nil) :: nil))) :: nil)) :: nil))
       (Rec₀ Closed (("age"%string, Nat₀)
                       :: ("name"%string, String₀)
                       :: ("friends"%string, (Coll₀ (Brand₀ ("Person"%string::nil)))) :: nil)))
    = Some
        (jobject
           (("$blob"%string, jstring "")
              :: ("$known"%string,
                  jobject
                    (("age"%string, jnumber 35)
                       :: ("name"%string, jstring "Fred")
                       :: ("friends"%string,
                           jarray
                             (jobject
                                (("$data"%string, jstring "{""age"": 42, ""name"": ""Berta"", ""friends"": []}")
                                   :: ("$type"%string, jarray (jstring "Person" :: nil)) :: nil) :: nil)) :: nil)) :: nil)).
  Proof. vm_compute. reflexivity. Qed.
   *)
  
  (* Added call for integration within the compiler interface *)
  Definition data_to_sjson (d:data) (r:rtype) : option string :=
    (* Some (typed_data_to_json_string d r) *)
    lift (jsonToJS """") (typed_data_to_json d (proj1_sig r)).

End DatatoSparkDF.

