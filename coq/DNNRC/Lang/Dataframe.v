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
Require Import String.
Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import DNNRCBase.

Section Dataframe.
  Context {fruntime:foreign_runtime}.
  Context {ftype: ForeignType.foreign_type}.
  Context {m : TBrandModel.brand_model}.

  Definition var := string.

  Inductive column :=
  | CCol   : string -> column
  | CDot   : string -> column -> column
  | CLit   : data * rtype₀ -> column
  | CPlus  : column -> column -> column
  | CEq    : column -> column -> column
  | CLessThan : column -> column -> column
  | CNeg   : column -> column
  (* NOTE we actually codegen to a UDF for this, not Spark's printing *)
  | CToString : column -> column
  | CSConcat : column -> column -> column
  (* In contrast to Qcert cast, this takes the runtime brands as input (as a column),
   * not the data, and returns a boolean suitable for filtering, not left(data)/right(null). *)
  | CUDFCast : list string -> column -> column
  | CUDFUnbrand : rtype₀ -> column -> column.

  Inductive dataframe :=
  | DSVar : string -> dataframe
  | DSSelect : list (string * column) -> dataframe -> dataframe
  | DSFilter : column -> dataframe -> dataframe
  | DSCartesian : dataframe -> dataframe -> dataframe
  | DSExplode : string -> dataframe -> dataframe.

  Section eval.
    Context (h:brand_relation_t).

    (** Evaluate a column expression in an environment of toplevel columns
     * i.e. a row in a dataframe. *)
    Fixpoint fun_of_column (c: column) (row: list (string * data)) : option data :=
      let fc := flip fun_of_column row in
      match c with
      | CCol n =>
        lookup string_eqdec row n
      | CNeg c1 =>
        olift (unudbool negb) (fc c1)
      | CDot n c1 =>
        match fc c1 with
        | Some (drec fs) => edot fs n
        | _ => None
        end
      | CLit (d, _) => Some (normalize_data h d)
      | CPlus c1 c2 =>
        match fc c1, fc c2 with
        | Some (dnat l), Some (dnat r) => Some (dnat (Z.add l r))
        | _, _ => None
        end
      | CEq c1 c2 =>
        (* TODO We use Qcert equality here. Define and use Spark equality.
         * Spark has a three-valued logic, meaning special treatment for NULL.
         * In contrast to Qcert it also does not deal with brands, bags, open records, ... *)
        lift2 (fun x y => dbool (if data_eq_dec x y then true else false)) (fc c1) (fc c2)
      | CLessThan c1 c2 =>
        None (* TODO *)
      | CToString c1 =>
        lift (compose dstring foreign_unary_op_data_tostring) (fc c1)
      | CSConcat c1 c2 =>
        match fc c1, fc c2 with
        | Some (dstring l), Some (dstring r) => Some (dstring (l ++ r))
        | _, _ => None
        end
      | CUDFCast target_brands column_of_runtime_brands =>
        match fc column_of_runtime_brands with
        | Some (dcoll runtime_brand_strings) =>
          lift (fun runtime_brands =>
                  dbool (if sub_brands_dec h runtime_brands target_brands then true else false))
               (listo_to_olist (map (fun s => match s with dstring s => Some s | _ => None end) runtime_brand_strings))
        | _ => None
        end
      | CUDFUnbrand _ _ => None (* TODO *)
      end.

    (* NOTE: the semantics for records 
       (when fields are duplicated / in the wrong order)
       are as in Qcert, which is not the same as Spark.
       If we want to model this more accurately, we should have 
       an alternative "lower level" semantics, along with a translation
       fix_names:dataframe->dataframe which uses renaming to ensure that
       everything works out ``naturally''.
       and of course, we want fix_names to preserve (dataframe_eval) semantics,
       and the two evaluation results should coincide for any output of 
       fix_names.
     *)
    Fixpoint dataframe_eval (dsenv : coll_bindings) (e: dataframe) : option (list data) :=
      match e with
      | DSVar s => lookup equiv_dec dsenv s
      | DSSelect cs d =>
        match dataframe_eval dsenv d with
        | Some rows =>
          (* List of column names paired with their functions. *)
          let cfuns: list (string * (list (string * data) -> option data)) :=
              map (fun p => (fst p, fun_of_column (snd p))) (rec_sort cs) in
          (* Call this function on every row in the input dataframe.
           * It calls every column function in the context of the row. *)
          let rfun: data -> option (list (string * data)) :=
              fun row =>
                match row with
                | drec fs =>
                  listo_to_olist (map (fun p => lift (fun r => (fst p, r)) ((snd p) fs)) cfuns)
                | _ => None
                end
          in
          let results := map (compose (lift drec) rfun) rows in
          listo_to_olist results
        | _ => None
        end
      | DSFilter c d =>
        let cfun := fun_of_column c in
        lift (* TODO This silently swallows eval errors. Don't do that. *)
                  (filter (fun row =>
                             match row with
                             | drec fs =>
                               match cfun fs with
                               | Some (dbool true) => true
                               | _ => false
                               end
                             | _ => false
                             end))
                  (dataframe_eval dsenv d)
      | DSCartesian d1 d2 =>
        match dataframe_eval dsenv d1, dataframe_eval dsenv d2 with
        | Some rs1, Some rs2 =>
          let data :=
              flat_map (fun r1 => map (fun r2 =>
                                         match r1, r2 with
                                         | drec a, drec b => Some (drec (rec_concat_sort a b))
                                         | _, _ => None
                                         end)
                                      rs2)
                       rs1 in
          listo_to_olist data
        | _, _ => None
        end
      | DSExplode s d1 =>
        match dataframe_eval dsenv d1 with
        | Some l =>
          let data :=
              flat_map (fun row =>
                          match row with
                          | drec fields =>
                            match edot fields s with
                            | Some (dcoll inners) =>
                              map (fun inner =>
                                     orecconcat (drec fields) (drec ((s, inner)::nil)))
                                  inners
                            | _ => None::nil
                            end
                          | _ => None::nil
                          end)
                       l in
          listo_to_olist data
        | _ => None
        end
      end.
  End eval.

  Section DataframePlug.

    Definition wrap_dataframe_eval h dsenv q :=
      lift dcoll (@dataframe_eval h dsenv q).

    Lemma fun_of_column_normalized {h c r o}:
      Forall (fun d : string * data => data_normalized h (snd d)) r ->
      fun_of_column h c r = Some o ->
      data_normalized h o.
    Proof.
      revert r o.
      induction c; simpl; intros rl o Fd; intros eqq.
      - apply lookup_in in eqq.
        rewrite Forall_forall in Fd.
        apply (Fd _ eqq).
      - unfold flip in eqq.
        specialize (IHc rl).
        match_destr_in eqq.
        match_destr_in eqq.
        specialize (IHc _ Fd (eq_refl _)).
        eapply data_normalized_edot; eauto.
      - destruct p.
        invcs eqq.
        apply normalize_normalizes.
      - unfold flip in eqq.
        match_destr_in eqq.
        match_destr_in eqq.
        match_destr_in eqq.
        match_destr_in eqq.
        invcs eqq.
        constructor.
      - unfold flip in eqq.
        destruct (fun_of_column h c1 rl); simpl in eqq; try discriminate.
        destruct (fun_of_column h c2 rl); simpl in eqq; try discriminate.
        invcs eqq.
        constructor.
      - discriminate.
      - unfold flip, olift in eqq.
        match_destr_in eqq.
        unfold unudbool in eqq.
        match_destr_in eqq.
        invcs eqq.
        constructor.
      - unfold flip, lift in eqq.
        match_destr_in eqq.
        invcs eqq.
        unfold compose.
        constructor.
      - unfold flip in eqq.
        repeat match_destr_in eqq.
        invcs eqq.
        constructor.
      - unfold flip, lift in eqq.
        repeat match_destr_in eqq; invcs eqq; constructor.
      - discriminate.
    Qed.

    Lemma dataframe_eval_normalized h :
      forall q:dataframe, forall (constant_env:coll_bindings) (o:data),
      Forall (fun x => data_normalized h (snd x)) (bindings_of_coll_bindings constant_env) ->
      wrap_dataframe_eval h constant_env q = Some o ->
      data_normalized h o.
    Proof.
      unfold wrap_dataframe_eval, bindings_of_coll_bindings.
      intros ds ce d Fb de.
      apply some_lift in de.
      destruct de as [dl de ?]; subst.
      rewrite Forall_map in Fb.
      simpl in Fb.
      rewrite Forall_forall in Fb.
      revert dl de.
      induction ds; simpl; intros dl de.
      - apply lookup_in in de.
        specialize (Fb _ de); simpl in Fb; trivial.
      - destruct (dataframe_eval h ce ds); try discriminate.
        specialize (IHds _ (eq_refl _)).
        apply listo_to_olist_some in de.
        unfold compose in de.
        invcs IHds.
        rename H0 into IHds.
        constructor.
        revert dl de.
        induction l0; simpl; intros dl de.
        + symmetry in de; apply map_eq_nil in de.
           subst; trivial.
        + destruct dl; simpl in de; try discriminate.
          invcs de.
          invcs IHds.
          constructor; [| auto].
          apply some_lift in H0.
          destruct H0 as [? eqq ?]; subst.
          match_destr_in eqq.
          specialize (IHl0 H4 _ H1).
          apply listo_to_olist_some in eqq.
          rewrite map_map in eqq.
          simpl in eqq.
          constructor.
          * {
              revert H1 eqq.
              generalize (rec_sort l).
              clear l.
              intros l H1 eqq.
              invcs H3.
              revert x eqq H0 dl H1 IHl0.
              induction l; simpl; intros ll eqql dnll dl eqq2 IHl0.
              - symmetry in eqql; apply map_eq_nil in eqql.
                subst; trivial. 
              - destruct ll; invcs eqql.
                apply some_lift in H0.
                destruct H0 as [? fc ?]; subst.
                generalize (fun_of_column_normalized dnll fc); intros dnx.
                constructor; simpl; trivial.
                specialize (IHl _ H1 dnll).
                cut (exists dl,
        map
          (fun x : data =>
           lift drec
             match x with
             | dunit => None
             | dnat _ => None
             | dfloat _ => None
             | dbool _ => None
             | dstring _ => None
             | dcoll _ => None
             | drec fs =>
                 listo_to_olist
                   (map
                      (fun p : string * (list (string * data) -> option data) =>
                       lift (fun r : data => (fst p, r)) (snd p fs))
                      (map (fun p : string * column => (fst p, fun_of_column h (snd p))) l))
             | dleft _ => None
             | dright _ => None
             | dbrand _ _ => None
             | dforeign _ => None
             end) l0 = map Some dl /\
        Forall (fun x : data => data_normalized h x) dl).
                { intros [? [??]]; eauto. }
            revert H4 dl eqq2 IHl0.
            clear.
            {
              induction l0; simpl; intros Fdn1 dl eqq Fdnl.
              - eauto.
              - destruct dl; try discriminate.
                simpl in eqq; invcs eqq.
                invcs Fdn1.
                invcs Fdnl.
                specialize (IHl0 H4 _ H1 H6).
                destruct IHl0 as [dl' [dl'eqq Fd']].
                apply some_lift in H0.
                destruct H0 as [dl'' de ?]; subst.
                destruct a0; try discriminate.
                case_eq (lift (fun r : data => (fst a, r)) (fun_of_column h (snd a) l1) )
                ; [intros ? eqq2 | intros eqq2]; rewrite eqq2 in de; try discriminate.
                match_destr_in de.
                simpl.
                exists (drec l2::dl'); simpl.
                split.
                + rewrite dl'eqq; trivial.
                + constructor; trivial.
                  invcs de.
                  invcs H5.
                  invcs H0.
                  constructor; trivial.
                  apply is_list_sorted_cons_inv in H2; trivial.
            }
            } 
          * assert (dxdl:domain x = domain (rec_sort l)).
            {
              revert x eqq. clear.
              generalize (rec_sort l).
              induction l0; simpl; intros x eqq.
              - symmetry in eqq; apply map_eq_nil in eqq.
                subst; trivial.
              - destruct x; try discriminate.
                simpl in eqq.
                invcs eqq.
                apply some_lift in H0.
                destruct H0 as [? fc ?]; subst.
                simpl.
                rewrite IHl0 by trivial.
                trivial.
            }
            rewrite dxdl; clear dxdl.
            eauto.
      - apply some_lift in de.
        destruct de as [dl' de ?]; subst.
        specialize (IHds _ de).
        constructor.
        apply Forall_filter.
        invcs IHds.
        trivial.
      - destruct (dataframe_eval h ce ds1); try discriminate.
        specialize (IHds1 _ (eq_refl _)).
        destruct (dataframe_eval h ce ds2); try discriminate.
        specialize (IHds2 _ (eq_refl _)).
        constructor.
        invcs IHds1.
        invcs IHds2.
        apply listo_to_olist_some in de.
        rewrite flat_map_concat_map in de.
        revert dl H0 de.
        induction l; simpl; intros dl Fdl eqq.
        + symmetry in eqq; apply map_eq_nil in eqq; subst; trivial.
        + invcs Fdl.
          symmetry in eqq.
          apply map_app_break in eqq.
          destruct eqq as [b' [c' [eqq1 [eqq2 eqq3]]]].
          subst.
          apply Forall_app; auto.
          clear eqq3 IHl.
          revert b' H1 eqq2.
          induction l0; simpl; intros b' Fdn eqq2.
        * symmetry in eqq2; apply map_eq_nil in eqq2; subst; trivial.
        * invcs Fdn.
          destruct b'; try discriminate.
          simpl in eqq2.
          invcs eqq2.
          destruct a; try discriminate.
          destruct a0; try discriminate.
          invcs H0.
          constructor; auto.
          apply data_normalized_rec_concat_sort; trivial.
      - destruct (dataframe_eval h ce ds); try discriminate.
        specialize (IHds _ (eq_refl _)).
        apply listo_to_olist_some in de.
        constructor.
        invcs IHds.
        revert dl H0 de.
        induction l; simpl; intros dl Fdn de.
        + symmetry in de; apply map_eq_nil in de; subst; trivial.
        + invcs Fdn.
           symmetry in de.
           apply map_app_break in de.
           destruct de as [b' [c' [eqq1 [eqq2 eqq3]]]].
           subst.
           apply Forall_app; auto.
           clear eqq3 IHl.
           destruct a; destruct b'; simpl in *; try discriminate; try solve[constructor].
           case_eq (edot l0 s); [intros ? eqq|intros eqq]
           ; rewrite eqq in eqq2; try discriminate.
           destruct d0; try discriminate.
           destruct l1; try discriminate.
           simpl in eqq2.
           invcs eqq2.
           assert (meq:map Some (map (fun inner : data => drec (rec_concat_sort l0 ((s, inner) :: nil))) l1) = map Some b')
             by (rewrite map_map; trivial).
           clear H3.
           apply map_inj in meq; [|inversion 1; congruence].
           subst.
           generalize (data_normalized_edot _ _ _ _ eqq H1); intros dn1.
           invcs dn1.
           invcs H0.
           invcs H1.
           constructor.
          * apply dnrec_sort.
            apply Forall_app; auto.
          * rewrite Forall_map.
            revert H5.
            apply Forall_impl; intros.
            apply dnrec_sort.
            apply Forall_app; auto.
    Qed.

    Global Program Instance SparkIRPlug : (@AlgPlug _ dataframe) :=
      mkAlgPlug wrap_dataframe_eval dataframe_eval_normalized.

  End DataframePlug.

End Dataframe.

