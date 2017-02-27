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
Require Import List String.
Require Import Peano_dec.
Require Import EquivDec.

Require Import Utils BasicSystem.
Require Import NNRCRuntime.
Require Import DNNRC DNNRCSize DNNRCEq.
Require Import RType.
Require Import TDNNRCInfer.
Require Import TOpsInfer.
Require Import Dataset DatasetSize.
Require Import OptimizerStep OptimizerLogger.


Section DNNRCDatasetRewrites.

  Context {fruntime:foreign_runtime}.
  (* This can be used to lift any rewrite on P to dnnrc A P.
     Practical note: the appropriate map_deep should probably 
     be used on the provided rewrite *)
  
  Fixpoint dnnrc_map_plug {A: Set} {P: Set}
           (f: P -> P)
           (e: @dnnrc _ A P) : @dnnrc _ A P
    := match e with
       | DNNRCVar a e0 => DNNRCVar a e0
       | DNNRCConst a e0 => DNNRCConst a e0
       | DNNRCBinop a b e1 e2 =>
         DNNRCBinop a b (dnnrc_map_plug f e1) (dnnrc_map_plug f e2)
       | DNNRCUnop a u e0 =>
         DNNRCUnop a u (dnnrc_map_plug f e0)
       | DNNRCLet a x e1 e2 =>
         DNNRCLet a x (dnnrc_map_plug f e1) (dnnrc_map_plug f e2)
       | DNNRCFor a x e1 e2 =>
         DNNRCFor a x (dnnrc_map_plug f e1) (dnnrc_map_plug f e2)
       | DNNRCIf a e1 e2 e3 =>
         DNNRCIf a
                (dnnrc_map_plug f e1)
                (dnnrc_map_plug f e2)
                (dnnrc_map_plug f e3)
       | DNNRCEither a e0 x1 e1 x2 e2 =>
         DNNRCEither a (dnnrc_map_plug f e0) x1 (dnnrc_map_plug f e1) x2 (dnnrc_map_plug f e2)
       | DNNRCGroupBy a g sl e0 =>
         DNNRCGroupBy a g sl (dnnrc_map_plug f e0)
       | DNNRCCollect a e0 =>
         DNNRCCollect a (dnnrc_map_plug f e0)
       | DNNRCDispatch a e0 =>
         DNNRCDispatch a (dnnrc_map_plug f e0)
       | DNNRCAlg a p sdl =>
         DNNRCAlg a (f p) (map (fun sd => (fst sd, (dnnrc_map_plug f (snd sd)))) sdl)
    end.

  Lemma dnnrc_map_plug_correct {A: Set} {P: Set}  
        {plug:AlgPlug P}
        {f: P -> P}
        (pf:forall (a:A) e env, dnnrc_eq (DNNRCAlg a e env) (DNNRCAlg a (f e) env))
        (e: @dnnrc _ A P) :
    dnnrc_eq e (dnnrc_map_plug f e).
  Proof.
    induction e; simpl; 
      try reflexivity.
    - apply dbinop_proper; trivial; try reflexivity.
    - apply dunop_proper; trivial; try reflexivity.
    - apply dlet_proper; trivial; reflexivity.
    - apply dfor_proper; trivial; reflexivity.
    - apply dif_proper; trivial; reflexivity.
    - apply deither_proper; trivial; reflexivity.
    - apply dgroupby_proper; trivial; reflexivity.
    - apply dcollect_proper; trivial; reflexivity.
    - apply ddispatch_proper; trivial; reflexivity.
    - rewrite pf.
      apply dalg_proper; trivial.
      apply Forall2_map_Forall.
      revert H; apply Forall_impl; intros; simpl; tauto.
  Qed.

  Fixpoint dnnrc_map_deep {A: Set} {P: Set}
           (f: @dnnrc _ A P -> @dnnrc _ A P)
           (e: @dnnrc _ A P) : @dnnrc _ A P
    := match e with
       | DNNRCVar a e0 =>
         f (DNNRCVar a e0)
       | DNNRCConst a e0 =>
         f (DNNRCConst a e0)
       | DNNRCBinop a b e1 e2 =>
         f (DNNRCBinop a b (dnnrc_map_deep f e1) (dnnrc_map_deep f e2))
       | DNNRCUnop a u e0 =>
         f (DNNRCUnop a u (dnnrc_map_deep f e0))
       | DNNRCLet a x e1 e2 =>
         f (DNNRCLet a x (dnnrc_map_deep f e1) (dnnrc_map_deep f e2))
       | DNNRCFor a x e1 e2 =>
         f (DNNRCFor a x (dnnrc_map_deep f e1) (dnnrc_map_deep f e2))
       | DNNRCIf a e1 e2 e3 =>
         f (DNNRCIf a
                (dnnrc_map_deep f e1)
                (dnnrc_map_deep f e2)
                (dnnrc_map_deep f e3))
       | DNNRCEither a e0 x1 e1 x2 e2 =>
         f (DNNRCEither a (dnnrc_map_deep f e0) x1 (dnnrc_map_deep f e1) x2 (dnnrc_map_deep f e2))
       | DNNRCGroupBy a g sl e0 =>
         f (DNNRCGroupBy a g sl (dnnrc_map_deep f e0))
       | DNNRCCollect a e0 =>
         f (DNNRCCollect a (dnnrc_map_deep f e0))
       | DNNRCDispatch a e0 =>
         f (DNNRCDispatch a (dnnrc_map_deep f e0))
       | DNNRCAlg a p sdl =>
         f (DNNRCAlg a p (map (fun sd => (fst sd, (dnnrc_map_deep f (snd sd)))) sdl))
    end.

    Lemma dnnrc_map_deep_correctness {A: Set} {P: Set} 
          {plug:AlgPlug P}
          {f: @dnnrc _ A P -> @dnnrc _ A P}
          (pf:forall e, dnnrc_eq e (f e))
          (e: @dnnrc _ A P) :
      dnnrc_eq e (dnnrc_map_deep f e).
    Proof.
      induction e; simpl; try auto 2
      ;  (etransitivity; [| apply pf]).
      - apply dbinop_proper; trivial; try reflexivity.
      - apply dunop_proper; trivial; try reflexivity.
      - apply dlet_proper; trivial; reflexivity.
      - apply dfor_proper; trivial; reflexivity.
      - apply dif_proper; trivial; reflexivity.
      - apply deither_proper; trivial; reflexivity.
      - apply dgroupby_proper; trivial; reflexivity.
      - apply dcollect_proper; trivial; reflexivity.
      - apply ddispatch_proper; trivial; reflexivity.
      - apply dalg_proper; trivial.
        apply Forall2_map_Forall.
        revert H; apply Forall_impl; intros; simpl; tauto.
    Qed.

    Context {ftype:foreign_type}.
    Context {h:brand_relation_t}.
    Context {m:brand_model}.

  (** Discover the traditional casting the world pattern:
   * Iterate over a collection (the world), cast the element and perform some action on success, return the empty collection otherwise, and flatten at the end.
   * We can translate this into a filter with a user defined cast function.
   * We do not inline unbranding, as we would have to make sure that we don't use the branded value anywhere.
   *)
  Definition rec_cast_to_filter {A: Set}
             (e: @dnnrc _ (type_annotation A) dataset) :
    @dnnrc _ (type_annotation A) dataset
    := match e with
    | DNNRCUnop t1 AFlatten
               (DNNRCFor t2 x
                        (DNNRCCollect t3 xs)
                        (DNNRCEither _ (DNNRCUnop t4 (ACast brands) (DNNRCVar _ x'))
                                    leftVar
                                    leftE
                                    _
                                    (DNNRC.DNNRCConst _ (dcoll nil)))) =>
      if (x == x')
      then
        match olift tuneither (lift_tlocal (ta_inferred t4)) with
        | Some (castSuccessType, _) =>
          let algTypeA := ta_mk (ta_base t4) (Tdistr castSuccessType) in
          let collectTypeA := ta_mk (ta_base t3) (Tlocal (Coll castSuccessType)) in
          (* We need a fresh name for the DNNRCAlg environment that binds DNNRC terms to
           * be referred to by name in the algebra part.
           * I talked to Avi about it and this is what needs to happen:
           * - TODO write a function that finds free (and possibly bound) names in Dataset
           * - TODO use existing fresh_var-related functions in Basic.Util.RFresh
           * - TODO also need to avoid runtime helpers, Spark(SQL) names, scala keywords, ...
           *)
          let ALG := (DNNRCAlg algTypeA
                            (DSFilter (CUDFCast brands (CCol "$type"))
                                      (DSVar "map_cast"))
                            (("map_cast"%string, xs)::nil)) in
          (DNNRCUnop t1 AFlatten
                         (DNNRCFor t2 leftVar (DNNRCCollect collectTypeA ALG)
                                  leftE))
        | _ => e
        end
      else e
    | _ => e
    end.

  Definition rec_cast_to_filter_step {A:Set}
    := mkOptimizerStep
         "rec cast filter" (* name *)
         "???" (* description *)
         "rec_cast_to_filter" (* lemma name *)
         (@rec_cast_to_filter A) (* lemma *).
  
  (* Replace (Unbrand (Var s)) expressions by just (Var s), for one specific s.
   * If there are uses of (Var s) outside Unbrand, fail. We use this to lift
   * unbranding into a map, but only if the value is not used unbranded. This is
   * a very limited instance of common subexpression elimination.
   *)
  Fixpoint rewrite_unbrand_or_fail
           {A: Set} {P: Set}
           (s: string)
           (e: @dnnrc _ A P) : option (@dnnrc _ A P)
    := match e with
    | DNNRCUnop t1 AUnbrand (DNNRCVar t2 v) =>
      if (s == v)
      then Some (DNNRCVar t1 s)
      else None
    | DNNRCVar _ v =>
      if (s == v)
      then None
      else Some e
    | DNNRCConst _ _ => Some e
    | DNNRCBinop a b x y =>
      lift2 (DNNRCBinop a b) (rewrite_unbrand_or_fail s x) (rewrite_unbrand_or_fail s y)
    | DNNRCUnop a b x =>
      lift (DNNRCUnop a b) (rewrite_unbrand_or_fail s x)
    | DNNRCLet a b x y =>
      lift2 (DNNRCLet a b) (rewrite_unbrand_or_fail s x) (rewrite_unbrand_or_fail s y)
    | DNNRCFor a b x y =>
      lift2 (DNNRCFor a b) (rewrite_unbrand_or_fail s x) (rewrite_unbrand_or_fail s y)
    | DNNRCIf a x y z =>
      match rewrite_unbrand_or_fail s x, rewrite_unbrand_or_fail s y, rewrite_unbrand_or_fail s z with
      | Some x', Some y', Some z' => Some (DNNRCIf a x' y' z')
      | _, _, _ => None
      end
    | DNNRCEither a x b y c z =>
      match rewrite_unbrand_or_fail s x, rewrite_unbrand_or_fail s y, rewrite_unbrand_or_fail s z with
      | Some x', Some y', Some z' => Some (DNNRCEither a x' b y' c z')
      | _, _, _ => None
      end
    | DNNRCGroupBy a g sl x =>
      lift (DNNRCGroupBy a g sl) (rewrite_unbrand_or_fail s x)
    | DNNRCCollect a x =>
      lift (DNNRCCollect a) (rewrite_unbrand_or_fail s x)
    | DNNRCDispatch a x =>
      lift (DNNRCDispatch a) (rewrite_unbrand_or_fail s x)
    (* TODO Can we discover uses of the variable s in an algebra expression? *)
    | DNNRCAlg _ _ _ => None
    end.

  Definition rec_lift_unbrand
             {A : Set}
             (e: @dnnrc _ (type_annotation A) dataset):
    (@dnnrc _ (type_annotation _) dataset) :=
    match e with
    | DNNRCFor t1 x (DNNRCCollect t2 xs as c) body =>
      match lift_tlocal (di_required_typeof c) with
      | Some (exist _ (Coll₀ (Brand₀ bs)) _) =>
        let t := proj1_sig (brands_type bs) in
        match rewrite_unbrand_or_fail x body with
        | Some e' =>
          let ALG :=
              (* TODO fresh name for lift_unbrand! *)
              DNNRCAlg (dnnrc_annotation_get xs)
                       (DSSelect (("$blob"%string, CCol "unbranded.$blob")
                                    :: ("$known"%string, CCol "unbranded.$known")::nil)
                                 (DSSelect (("unbranded"%string, CUDFUnbrand t (CCol "$data"))::nil)
                                           (DSVar "lift_unbrand")))
                       (("lift_unbrand"%string, xs)::nil)
          in
          DNNRCFor t1 x (DNNRCCollect t2 ALG) e'
        | None => e
        end
      | _ => e
      end
    | _ => e
    end.

    Definition rec_lift_unbrand_step {A:Set}
    := mkOptimizerStep
         "rec lift unbrand" (* name *)
         "???" (* description *)
         " rec_lift_unbrand" (* lemma name *)
         (@rec_lift_unbrand A) (* lemma *).

  Fixpoint spark_equality_matches_qcert_equality_for_type (r: rtype₀) :=
    match r with
    | Nat₀
    | Bool₀
    | String₀ => true
    | Rec₀ Closed fs =>
      forallb (compose spark_equality_matches_qcert_equality_for_type snd) fs
    | Either₀ l r  =>
      andb (spark_equality_matches_qcert_equality_for_type l)
           (spark_equality_matches_qcert_equality_for_type r)
    | Bottom₀
    | Top₀
    | Unit₀ (* lit(null).equalTo(lit(null)) => NULL *)
    | Coll₀ _ (* NOTE collections would work, if we kept them in order *)
    | Rec₀ Open _
    | Arrow₀ _ _
    | Brand₀ _
    | Foreign₀ _ => false
    end.

  Fixpoint condition_to_column {A: Set}
           (e: @dnnrc _ (type_annotation A) dataset)
           (binding: (string * column)) :=
    match e with
    (* TODO figure out how to properly handle vars and projections *)
    | DNNRCUnop _ (ADot fld) (DNNRCVar _ n) =>
      let (var, _) := binding in
      if (n == var)
      then Some (CCol ("$known."%string ++ fld))
      else None
    (*    | DNNRCVar _ n =>
      (* TODO generalize to multiple bindings, for joins *)
      let (var, expr) := binding in
      if (n == var)
      then Some expr
      else None
    | DNNRCUnop _ (ADot fld) c =>
      lift (fun c =>
              (CDot cname fld c))
           (condition_to_column c "c" binding) *)
    | DNNRCConst _ d =>
      lift (fun t => CLit (d, (proj1_sig t))) (lift_tlocal (di_required_typeof e))
    | DNNRCBinop _ AEq l r =>
      let types_are_okay :=
          lift2 (fun lt rt => andb (equiv_decb lt rt)
                                   (spark_equality_matches_qcert_equality_for_type (proj1_sig lt)))
                (lift_tlocal (di_typeof l)) (lift_tlocal (di_typeof r)) in
      match types_are_okay, condition_to_column l binding, condition_to_column r binding with
      | Some true, Some l', Some r' =>
        Some (CEq l' r')
      | _, _, _ => None
      end
    | DNNRCBinop _ ASConcat l r =>
      lift2 CSConcat
            (condition_to_column l binding)
            (condition_to_column r binding)
    | DNNRCBinop _ ALt l r =>
      lift2 CLessThan
            (condition_to_column l binding)
            (condition_to_column r binding)
    (* TODO properly implement this *)
    | DNNRCUnop _ AToString x =>
      lift CToString
           (condition_to_column x binding)

    | _ => None
    end.

  Definition rec_if_else_empty_to_filter {A: Set}
             (e: @dnnrc _ (type_annotation A) dataset):
    (@dnnrc _ (type_annotation A) dataset) :=
    match e with
    | DNNRCUnop t1 AFlatten
               (DNNRCFor t2 x (DNNRCCollect t3 xs)
                        (DNNRCIf _ condition
                                thenE
                                (DNNRC.DNNRCConst _ (dcoll nil)))) =>
      match condition_to_column condition (x, CCol "abc") with
      | Some c' =>
        let ALG :=
            DNNRCAlg (dnnrc_annotation_get xs)
                    (DSFilter c' (DSVar "if_else_empty_to_filter"))
                    (("if_else_empty_to_filter"%string, xs)::nil)
        in
        DNNRCUnop t1 AFlatten
                       (DNNRCFor t2 x (DNNRCCollect t3 ALG)
                                thenE)
      | None => e
      end
    | _ => e
    end.

  Definition rec_if_else_empty_to_filter_step {A:Set}
    := mkOptimizerStep
         "rec/if/empty" (* name *)
         "" (* description *)
         "rec_if_else_empty_to_filter" (* lemma name *)
         (@rec_if_else_empty_to_filter A) (* lemma *).

  Definition rec_remove_map_singletoncoll_flatten {A: Set}
             (e: @dnnrc _ (type_annotation A) dataset):
    @dnnrc _ (type_annotation A) dataset :=
    match e with
    | DNNRCUnop t1 AFlatten
               (DNNRCFor t2 x xs
                        (DNNRCUnop t3 AColl e)) =>
      DNNRCFor t1 x xs e
    | _ => e
    end.

  Definition rec_remove_map_singletoncoll_flatten_step {A:Set}
    := mkOptimizerStep
         "flatten/for/coll" (* name *)
         "Simplifes flatten of a for comprehension that creates singleton bags" (* description *)
         "rec_remove_map_singletoncoll_flatten" (* lemma name *)
         (@rec_remove_map_singletoncoll_flatten A) (* lemma *).

  Definition rec_for_to_select {A: Set}
             (e: @dnnrc _ (type_annotation A) dataset):
    @dnnrc _ (type_annotation A) dataset :=
    match e with
    | DNNRCFor t1 x (DNNRCCollect t2 xs) body =>
      match lift_tlocal (di_typeof body) with
      (* TODO generalize to other types than String ...
       * This involves returning more than one column ... *)
      | Some String =>
        (* TODO rename condition_to_column, if this works *)
        match condition_to_column body (x, CCol "abc") with
        | Some body' =>
          (* TODO generalize to other types than String ... *)
          let ALG_type := Tdistr String in
          let ALG :=
              DNNRCAlg (ta_mk (ta_base t1) ALG_type)
                      (DSSelect (("value"%string, body')::nil) (DSVar "for_to_select"))
                      (("for_to_select"%string, xs)::nil)
          in
          DNNRCCollect t1 ALG
        | None => e
        end
      | _ => e
      end
    | _ => e
    end.

  Definition rec_for_to_select_step {A:Set}
    := mkOptimizerStep
         "rec for to select" (* name *)
         "???" (* description *)
         "rec_for_to_select" (* lemma name *)
         (@rec_for_to_select A) (* lemma *).

  Import ListNotations.

  Definition dnnrc_optim_list {A} :
    list (OptimizerStep (@dnnrc _ (type_annotation A) dataset))
    := [
        rec_cast_to_filter_step
        ; rec_lift_unbrand_step
        ; rec_if_else_empty_to_filter_step
        ; rec_remove_map_singletoncoll_flatten_step
        ; rec_for_to_select_step
      ].

  Lemma dnnrc_optim_list_distinct {A:Set}:
    optim_list_distinct (@dnnrc_optim_list A).
  Proof.
    apply optim_list_distinct_prover.
    vm_compute.
    apply eq_refl.
  Qed.
  
  Definition run_dnnrc_optims {A}
             {logger:optimizer_logger string (@dnnrc _ (type_annotation A) dataset)}
             (phaseName:string)
             (optims:list string)
             (iterationsBetweenCostCheck:nat)
    : @dnnrc _ (type_annotation A) dataset -> @dnnrc _ (type_annotation A) dataset :=
    run_phase dnnrc_map_deep (dnnrc_size (* dataset_size *)) dnnrc_optim_list
              ("[dnnrc] " ++ phaseName) optims iterationsBetweenCostCheck.

  Definition dnnrc_default_optim_list : list string
    := [
        optim_step_name (@rec_for_to_select_step unit)
          ; optim_step_name (@rec_remove_map_singletoncoll_flatten_step unit)
          ; optim_step_name (@rec_if_else_empty_to_filter_step unit)
          ; optim_step_name (@rec_lift_unbrand_step unit)
          ; optim_step_name (@rec_cast_to_filter_step unit)
        ].

  Remark dnnrc_default_optim_list_all_valid  {A:Set}
    : valid_optims (@dnnrc_optim_list A) dnnrc_default_optim_list = (dnnrc_default_optim_list,nil).
  Proof.
    vm_compute; trivial.
  Qed.

  Definition dnnrcToDatasetRewrite {A:Set}
             {logger:optimizer_logger string (@dnnrc _ (type_annotation A) dataset)}
    := run_dnnrc_optims "" dnnrc_default_optim_list 6.

End DNNRCDatasetRewrites.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
