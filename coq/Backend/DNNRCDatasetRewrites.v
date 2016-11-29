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
Require Import NNRCRuntime ForeignToJava ForeignToJavascript.
Require Import DNNRC.
Require Import RType.
Require Import TDNRCInfer.
Require Import TOpsInfer.
Require Import Dataset.

Section DNNRCDatasetRewrites.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  Context {fdtyping:foreign_data_typing}.
  Context {fboptyping:foreign_binary_op_typing}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {fttjs: foreign_to_javascript}.

  (* This should really be some clever monadic combinator thing to compose tree rewritings and strategies, think Stratego.
   *
   * A Haskell Hosted DSL for Writing Transformation Systems.
   * Andy Gill. IFIP Working Conference on DSLs, 2009.
   * http://ku-fpg.github.io/files/Gill-09-KUREDSL.pdf *)
  Fixpoint tryBottomUp {A: Set} {P: Set}
           (f: dnnrc A P -> option (dnnrc A P))
           (e: dnnrc A P)
    : dnnrc A P :=
    let try := fun e =>
                 match f e with
                 | Some e' => e'
                 | None => e
                 end in
    match e with
    | DNNRCVar _ _ => try e
    | DNNRCConst _ _ => try e
    | DNNRCBinop a b x y =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      try (DNNRCBinop a b x' y')
    | DNNRCUnop a b x =>
      let x' := tryBottomUp f x in
      try (DNNRCUnop a b x')
    | DNNRCLet a b x y =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      try (DNNRCLet a b x' y')
    | DNNRCFor a b x y =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      try (DNNRCFor a b x' y')
    | DNNRCIf a x y z =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      let z' := tryBottomUp f z in
      try (DNNRCIf a x' y' z')
    | DNNRCEither a x b y c z =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      let z' := tryBottomUp f z in
      try (DNNRCEither a x' b y' c z')
    | DNNRCGroupBy a g sl x =>
      let x' := tryBottomUp f x in
      try (DNNRCGroupBy a g sl x')
    | DNNRCCollect a x =>
      let x' := tryBottomUp f x in
      try (DNNRCCollect a x')
    | DNNRCDispatch a x =>
      let x' := tryBottomUp f x in
      try (DNNRCDispatch a x')
    | DNNRCAlg a b c =>
      (* TODO Should I try to match on the dnnrc environment? *)
      try e
    end.

  (** Discover the traditional casting the world pattern:
   * Iterate over a collection (the world), cast the element and perform some action on success, return the empty collection otherwise, and flatten at the end.
   * We can translate this into a filter with a user defined cast function.
   * We do not inline unbranding, as we would have to make sure that we don't use the branded value anywhere.
   *)
  Definition rec_cast_to_filter {A: Set}
             (e: dnnrc (type_annotation A) dataset) :=
    match e with
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
          Some (DNNRCUnop t1 AFlatten
                         (DNNRCFor t2 leftVar (DNNRCCollect collectTypeA ALG)
                                  leftE))
        | _ => None
        end
      else None
    | _ => None
    end.

  (* Replace (Unbrand (Var s)) expressions by just (Var s), for one specific s.
   * If there are uses of (Var s) outside Unbrand, fail. We use this to lift
   * unbranding into a map, but only if the value is not used unbranded. This is
   * a very limited instance of common subexpression elimination.
   *)
  Fixpoint rewrite_unbrand_or_fail
           {A: Set} {P: Set}
           (s: string)
           (e: dnnrc A P) :=
    match e with
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
             (e: dnnrc (type_annotation A) dataset):
    option (dnnrc (type_annotation _) dataset) :=
    match e with
    | DNNRCFor t1 x (DNNRCCollect t2 xs as c) e =>
      match lift_tlocal (di_required_typeof c) with
      | Some (exist _ (Coll₀ (Brand₀ bs)) _) =>
        let t := proj1_sig (brands_type bs) in
        match rewrite_unbrand_or_fail x e with
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
          Some (DNNRCFor t1 x (DNNRCCollect t2 ALG) e')
        | None => None
        end
      | _ => None
      end
    | _ => None
    end.


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
           (e: dnnrc (type_annotation A) dataset)
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
             (e: dnnrc (type_annotation A) dataset):
    option (dnnrc (type_annotation A) dataset) :=
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
        Some (DNNRCUnop t1 AFlatten
                       (DNNRCFor t2 x (DNNRCCollect t3 ALG)
                                thenE))
      | None => None
      end
    | _ => None
    end.

  Definition rec_remove_map_singletoncoll_flatten {A: Set}
             (e: dnnrc (type_annotation A) dataset):
    option (dnnrc (type_annotation A) dataset) :=
    match e with
    | DNNRCUnop t1 AFlatten
               (DNNRCFor t2 x xs
                        (DNNRCUnop t3 AColl e)) =>
      Some (DNNRCFor t1 x xs e)
    | _ => None
    end.

  Definition rec_for_to_select {A: Set}
             (e: dnnrc (type_annotation A) dataset):
    option (dnnrc (type_annotation A) dataset) :=
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
          Some (DNNRCCollect t1 ALG)
        | None => None
        end
      | _ => None
      end
    | _ => None
    end.

  Definition dnnrcToDatasetRewrite {A : Set}
             (e: dnnrc (type_annotation A) dataset) : dnnrc (type_annotation A) dataset
    :=
      let e' := e in
      let e'' := tryBottomUp rec_cast_to_filter e' in
      let e''' := tryBottomUp rec_lift_unbrand e'' in
      let e'''' := tryBottomUp rec_if_else_empty_to_filter e''' in
      let e''''' := tryBottomUp rec_remove_map_singletoncoll_flatten e'''' in
      let e'''''' := tryBottomUp rec_for_to_select e''''' in
      e''''''.


End DNNRCDatasetRewrites.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
