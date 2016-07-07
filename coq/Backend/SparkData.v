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

Require Import List String.
Require Import Peano_dec.
Require Import EquivDec.

Require Import Utils BasicSystem.
Require Import NNRCRuntime ForeignToJava.
Require Import RType.
Require Import Sumbool.
Require Import ZArith.
Require Import Bool.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import RData.

Require Import TDataInfer.
Require Import BrandRelation.
Require Import Utils Types BasicRuntime.
Require Import ForeignDataTyping.
Require Import NNRCtoJavascript.


Section SparkData.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.
  Context {fttojs: ForeignToJavascript.foreign_to_javascript}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Inductive stype :=
  | STbrand  : string -> stype
  | STnull   : stype
  | STint    : stype
  | STstring : stype
  | STbool   : stype
  | STarray  : stype -> stype
  | STstruct : list (string * stype) -> stype
  .

  Inductive sdata :=
  (* This is outside the actual Spark data model, like .. in open records. Probably use a string representation? *)
  | Sblob   : data -> sdata
  | Snull   : sdata
  | Sint    : Z -> sdata
  | Sstring : string -> sdata
  | Sbool   : bool -> sdata
  | Sarray  : list sdata -> sdata
  | Srow    : list (string * sdata) -> option data -> sdata
  .

  Section with_string_scope.
    Local Open Scope string_scope.
    Fixpoint stype_to_datatype (s: stype) : string :=
      match s with
      | STbrand name => "BRAND_TYPES(\""" ++ name ++ "\"")"
      | STnull => "NullType"
      | STint => "IntegerType"
      | STstring => "StringType"
      | STbool => "BooleanType"
      | STarray e => "ArrayType(" ++ stype_to_datatype e ++ ")"
      | STstruct fields =>
        let fieldTypes :=
            map (fun p => "StructField(\""" ++ fst p ++ "\"", " ++ stype_to_datatype (snd p) ++ ")")
                fields in
        "StructType(Seq(" ++ joinStrings ", " fieldTypes ++ "))"
      end.

    (** sdata to json AST
     * Convert data to a simple format that we can just serialize to JSON *)
    Fixpoint sdata_to_plain_data (s: sdata) : data :=
      match s with
      | Sblob data => dstring (dataToJS "\""" data)
      | Snull => dunit
      | Sint i => dnat i
      | Sstring s => dstring s
      | Sbool b => dbool b
      | Sarray el => dcoll (map sdata_to_plain_data el)
      | Srow known dotdot =>
        let known_fields := map (fun p => (fst p, sdata_to_plain_data (snd p))) known in
        let dotdot_string := match dotdot with
                               None => ""
                             | Some d => dataToJS "\""" d end in
        drec (("$blob", dstring dotdot_string)::("$known", drec known_fields)::nil)
      end.

    Definition sdata_to_json (s: sdata) : string :=
      dataToJS "\""" (sdata_to_plain_data s).

    Fixpoint rtype_to_stype (r: rtype₀) : stype :=
      match r with
      | Bottom₀ => STnull
      | Top₀ => STstring
      | Unit₀ => STnull
      | Nat₀ => STint
      | Bool₀ => STbool
      | String₀ => STstring
      | Coll₀ e_type => STarray (rtype_to_stype e_type)
      | Rec₀ _ fields =>
        let known_fields : list (string * stype) :=
            map (fun p => (fst p, rtype_to_stype (snd p))) fields in
        STstruct (("$blob", STstring)::("$known", STstruct known_fields)::nil)
      | Either₀ l r => STstruct (("$left", rtype_to_stype l)::("$right", rtype_to_stype r)::nil)
      | Brand₀ (b::nil) =>
        STstruct (("$type", STarray STstring)
                    ::("$data", STbrand b)::nil)
      | Brand₀ _ => STnull (* This does not happen for data. Right?! *)
      (* should not occur *)
      | Arrow₀ _ _ => STnull
      | Foreign₀ ft => STnull
      end.

  End with_string_scope.

  Definition flip {a b c} (f : a -> b -> c) : b -> a -> c :=
    fun b a => f a b.

  Fixpoint typed_data_to_sdata_0 (d: data) (r: rtype₀): option sdata :=
    match d, r with
    (* Uh, so this means every piece of data has an additional representation at type top,
     * and it's the same for every type of data. I guess this makes some sense in that we
     * seem to require a blob/string representation for data inside .. anyways. *)
    | _, Top₀ => Some (Sblob d)
    | dunit, Unit₀ => Some Snull
    | dnat i, Nat₀ => Some (Sint i)
    | dbool b, Bool₀ => Some (Sbool b)
    | dstring s, String₀ => Some (Sstring s)
    | dcoll xs, (Coll₀ et) =>
      let listo := map (flip typed_data_to_sdata_0 et) xs in
      lift Sarray (listo_to_olist listo)
    | drec fs, Rec₀ Closed ft =>
      let fix convert_fields ds ts :=
          match ds, ts with
          | nil, nil => Some nil
          | nil, _ => None
          | _, nil => None
          | ((f, d)::ds), ((_, t)::ts) =>
            match typed_data_to_sdata_0 d t, convert_fields ds ts with
            | Some sdata, Some tail => Some ((f, sdata)::tail)
            | _, _ => None
            end
          end in
      lift (fun d => Srow d None) (convert_fields fs ft)
    | drec fs, Rec₀ Open ft =>
    (* Put typed fields in typed part, leftover fields in .. part *)
      let fix convert_known_fields ds ts us :=
          match ts, ds with
          (* No more typed fields, return leftover .. fields *)
          | nil, ds => Some (nil, us ++ ds)
          | _, nil => None
          | ((tf, t)::ts), ((df, d)::ds) =>
            if string_dec tf df
            then match typed_data_to_sdata_0 d t, convert_known_fields ds ts us with
                 | Some sdata, Some (tail, us) => Some (((tf, sdata)::tail), us)
                 | _, _ => None
                 end
            else
              convert_known_fields ds ts ((df, d)::us)
          end in
      (* I'm not sure the dotdot fields are in the correct order, might need to sort them. *)
      match convert_known_fields fs ft nil with
      | Some (typed_fields, dotdot) =>
        Some (Srow typed_fields (Some (drec dotdot)))
      | None => None
      end
    | dleft l, Either₀ lt rt =>
      match typed_data_to_sdata_0 l lt with
      | Some l => Some (Srow (("$left"%string, l)::("$right"%string, Snull)::nil) None)
      | None => None
      end
    | dright r, Either₀ lt rt =>
      match typed_data_to_sdata_0 r rt with
      | Some r => Some (Srow (("$left"%string, Snull)::("$right"%string, r)::nil) None)
      | None => None
      end
    | dbrand bs v, Brand₀ bts =>
      let type := proj1_sig (brands_type bts) in
      match typed_data_to_sdata_0 v type with
      | Some data => Some (Srow (("$data"%string, data)
                                   ::("$type"%string, Sarray (map Sstring bs))::nil)
                                None)
      | None => None
      end
    | dforeign _, _ => None
    | _, _ => None
    end.

  Definition typed_data_to_sdata (d: data) (r: rtype) : option sdata := typed_data_to_sdata_0 d (proj1_sig r).

  Lemma top_typed_data_to_some_sdata (d: data) :
    exists x : sdata, typed_data_to_sdata d ⊤ = Some x.
  Proof.
    intros; subst; unfold typed_data_to_sdata; simpl;
      exists (Sblob d);
      destruct d; reflexivity.
  Qed.

  Lemma well_typed_data_to_some_sdata (d: data) (r: rtype) :
    (d ▹ r) -> exists x : sdata, typed_data_to_sdata d r = Some x.
  Proof.
    revert r; induction d; simpl; intros.
    - inversion H; unfold typed_data_to_sdata; simpl in *; eauto.
    - inversion H; unfold typed_data_to_sdata; simpl in *; eauto.
    - inversion H; unfold typed_data_to_sdata; simpl in *; eauto.
    - inversion H; unfold typed_data_to_sdata; simpl in *; eauto.
    - admit.
    - admit.
    - destruct (istop r); try (subst; apply top_typed_data_to_some_sdata).
      destruct (data_type_dleft_inv e H) as [τ₂' [? ?]]; subst.
      unfold typed_data_to_sdata; simpl.
      specialize (IHd τ₂').
      inversion H. subst.
      assert (τl = τ₂') by apply (rtype_fequal H1).
      subst.
      specialize (IHd H2).
      elim IHd; intros.
      unfold typed_data_to_sdata in H0; simpl in H0.
      rewrite H0.
      eauto.
    - destruct (istop r); try (subst; apply top_typed_data_to_some_sdata).
      destruct (data_type_dright_inv e H) as [? [t ?]]; subst.
      unfold typed_data_to_sdata; simpl.
      specialize (IHd t).
      inversion H. subst.
      assert (τr = t) by apply (rtype_fequal H3).
      subst.
      specialize (IHd H2).
      elim IHd; intros.
      unfold typed_data_to_sdata in H0; simpl in H0.
      rewrite H0.
      eauto.
    - destruct (istop r); try (subst; apply top_typed_data_to_some_sdata).
      inversion H. subst.
      discriminate e.
      subst.
      destruct (data_type_Brand_inv H).
      unfold typed_data_to_sdata. simpl.
      admit.
Admitted.

  (* Added calls for integration within the compiler interface *)
  Require Import ForeignToJSON.
  Require Import JSON JSONtoData.

  Context {ftojson:foreign_to_JSON}.

  Definition data_to_sjson (d:data) (r:rtype) : option string :=
    lift sdata_to_json (typed_data_to_sdata d r).

End SparkData.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
