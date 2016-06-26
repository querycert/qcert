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


Section SparkData.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Inductive stype :=
  | stnull   : stype
  | stint    : stype
  | ststring : stype
  | stbool   : stype
  | starray  : stype -> stype
  | ststruct : list (string * stype) -> stype
  .

  Inductive sdata :=
  (* This is outside the actual Spark data model, like .. in open records. Probably use a string representation? *)
  | sblob   : data -> sdata
  | snull   : sdata
  | sint    : Z -> sdata
  | sstring : string -> sdata
  | sbool   : bool -> sdata
  | sarray  : list sdata -> sdata
  | srow    : list (string * sdata) -> option data -> sdata
  .

  Definition brand_content_rtype (bl: list string) : rtype₀ :=
    (* TODO *)
    Bottom₀.

  Definition brand_content_stype (bl: list string) : stype :=
    (* TODO Intersection of brands models, or something *)
    stnull.

  Fixpoint rtype_to_stype (r: rtype₀) : stype :=
    match r with
    | Bottom₀ => stnull
    | Top₀ => ststring
    | Unit₀ => stnull
    | Nat₀ => stint
    | Bool₀ => stbool
    | String₀ => ststring
    | Coll₀ e_type => starray (rtype_to_stype e_type)
    | Rec₀ _ fields =>
      let known_fields : list (string * stype) :=
          map (fun p => (fst p, rtype_to_stype (snd p))) fields in
      ststruct (("$blob"%string, ststring)::("$known"%string, ststruct known_fields)::nil)
    | Either₀ l r => ststruct (("$left"%string, rtype_to_stype l)::("$right"%string, rtype_to_stype r)::nil)
    | Brand₀ brands =>
      ststruct (("$type"%string, starray ststring)
                  ::("$data"%string, brand_content_stype brands)::nil)
    (* should not occur *)
    | Arrow₀ _ _ => stnull
    | Foreign₀ ft => stnull
    end.

  Definition flip {a b c} (f : a -> b -> c) : b -> a -> c :=
    fun b a => f a b.

  Fixpoint typed_data_to_sdata_0 (d: data) (r: rtype₀): option sdata :=
    match d, r with
    (* Uh, so this means every piece of data has an additional representation at type top,
     * and it's the same for every type of data. I guess this makes some sense in that we
     * seem to require a blob/string representation for data inside .. anyways. *)
    | _, Top₀ => Some (sblob d)
    | dunit, Unit₀ => Some snull
    | dnat i, Nat₀ => Some (sint i)
    | dbool b, Bool₀ => Some (sbool b)
    | dstring s, String₀ => Some (sstring s)
    | dcoll xs, (Coll₀ et) =>
      let listo := map (flip typed_data_to_sdata_0 et) xs in
      lift sarray (listo_to_olist listo)
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
      lift (fun d => srow d None) (convert_fields fs ft)
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
        Some (srow typed_fields (Some (drec dotdot)))
      | None => None
      end
    | dleft l, Either₀ lt rt =>
      match typed_data_to_sdata_0 l lt with
      | Some l => Some (srow (("$left"%string, l)::("$right"%string, snull)::nil) None)
      | None => None
      end
    | dright r, Either₀ lt rt =>
      match typed_data_to_sdata_0 r rt with
      | Some r => Some (srow (("$left"%string, snull)::("$right"%string, r)::nil) None)
      | None => None
      end
    | dbrand bs v, Brand₀ bts =>
      let type := brand_content_rtype bts in
      match typed_data_to_sdata_0 v type with
      | Some data => Some (srow (("$type"%string, sarray (map sstring bs))
                                   ::("$data"%string, data)::nil)
                                None)
      | None => None
      end
    | dforeign _, _ => None
    | _, _ => None
    end.

  Definition typed_data_to_sdata (d: data) (r: rtype) := typed_data_to_sdata_0 d (proj1_sig r).

  Lemma top_typed_data_to_some_sdata (d: data) :
    exists x : sdata, typed_data_to_sdata d ⊤ = Some x.
  Proof.
    intros; subst; unfold typed_data_to_sdata; simpl;
      exists (sblob d);
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
      exists ((srow (("$left"%string, x0) :: ("$right"%string, snull) :: nil) None)).
      reflexivity.
  Admitted.

End SparkData.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
