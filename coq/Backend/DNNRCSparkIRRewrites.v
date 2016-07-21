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
Require Import DNNRC.
Require Import RType.
Require Import TDNRCInfer.
Require Import TOpsInfer.
Require Import SparkIR.

Section DNNRCSparkIRRewrites.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  Context {fdtyping:foreign_data_typing}.
  Context {fboptyping:foreign_binary_op_typing}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {fttjs: ForeignToJavascript.foreign_to_javascript}.

  (* This should really be some clever monadic combinator thing to compose tree rewritings and strategies, think Stratego.
   *
   * A Haskell Hosted DSL for Writing Transformation Systems.
   * Andy Gill. IFIP Working Conference on DSLs, 2009.
   * http://ku-fpg.github.io/files/Gill-09-KUREDSL.pdf *)
  Fixpoint tryBottomUp {A: Set} {P: Set}
           (f: dnrc A P -> option (dnrc A P))
           (e: dnrc A P)
    : dnrc A P :=
    let try := fun e =>
                 match f e with
                 | Some e' => e'
                 | None => e
                 end in
    match e with
    | DNRCVar _ _ => try e
    | DNRCConst _ _ => try e
    | DNRCBinop a b x y =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      try (DNRCBinop a b x' y')
    | DNRCUnop a b x =>
      let x' := tryBottomUp f x in
      try (DNRCUnop a b x')
    | DNRCLet a b x y =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      try (DNRCLet a b x' y')
    | DNRCFor a b x y =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      try (DNRCFor a b x' y')
    | DNRCIf a x y z =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      let z' := tryBottomUp f z in
      try (DNRCIf a x' y' z')
    | DNRCEither a x b y c z =>
      let x' := tryBottomUp f x in
      let y' := tryBottomUp f y in
      let z' := tryBottomUp f z in
      try (DNRCEither a x' b y' c z')
    | DNRCCollect a x =>
      let x' := tryBottomUp f x in
      try (DNRCCollect a x')
    | DNRCDispatch a x =>
      let x' := tryBottomUp f x in
      try (DNRCDispatch a x')
    | DNRCAlg a b c =>
      (* TODO Should I try to match on the dnrc environment? *)
      try e
    end.

  (** Discover the traditional casting the world pattern:
   * Iterate over a collection (the world), cast the element and perform some action on success, return the empty collection otherwise, and flatten at the end.
   * We can translate this into a filter with a user defined cast function.
   * We do not inline unbranding, as we would have to make sure that we don't use the branded value anywhere.
   *)
  Definition rec_cast_to_filter {A: Set}
             (e: dnrc (type_annotation _ _ A) dataset) :=
    match e with
    | DNRCUnop t1 AFlatten
               (DNRCFor t2 x
                        (DNRCCollect t3 xs)
                        (DNRCEither _ (DNRCUnop t4 (ACast brands) (DNRCVar _ x'))
                                    leftVar
                                    leftE
                                    _
                                    (DNNRC.DNRCConst _ (dcoll nil)))) =>
      if (x == x')
      then
        match olift tuneither (lift_tlocal (ta_inferred t4)) with
        | Some (castSuccessType, _) =>
          let algTypeA := ta_mk (ta_base t4) (Tdistr castSuccessType) in
          let collectTypeA := ta_mk (ta_base t3) (Tlocal (Coll castSuccessType)) in
          (* We need a fresh name for the DNRCAlg environment that binds DNNRC terms to
           * be referred to by name in the algebra part.
           * I talked to Avi about it and this is what needs to happen:
           * - TODO write a function that finds free (and possibly bound) names in SparkIR
           * - TODO use existing fresh_var-related functions in Basic.Util.RFresh
           * - TODO also need to avoid runtime helpers, Spark(SQL) names, scala keywords, ...
           *)
          let ALG := (DNRCAlg algTypeA
                            (DSFilter (CUDFCast "_ignored" brands (CCol "$type"))
                                      (DSVar "map_cast"))
                            (("map_cast"%string, xs)::nil)) in
          Some (DNRCUnop t1 AFlatten
                         (DNRCFor t2 leftVar (DNRCCollect collectTypeA ALG)
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
           (e: dnrc A P) :=
    match e with
    | DNRCUnop t1 AUnbrand (DNRCVar t2 v) =>
      if (s == v)
      then Some (DNRCVar t1 s)
      else None
    | DNRCVar _ v =>
      if (s == v)
      then None
      else Some e
    | DNRCConst _ _ => Some e
    | DNRCBinop a b x y =>
      lift2 (DNRCBinop a b) (rewrite_unbrand_or_fail s x) (rewrite_unbrand_or_fail s y)
    | DNRCUnop a b x =>
      lift (DNRCUnop a b) (rewrite_unbrand_or_fail s x)
    | DNRCLet a b x y =>
      lift2 (DNRCLet a b) (rewrite_unbrand_or_fail s x) (rewrite_unbrand_or_fail s y)
    | DNRCFor a b x y =>
      lift2 (DNRCFor a b) (rewrite_unbrand_or_fail s x) (rewrite_unbrand_or_fail s y)
    | DNRCIf a x y z =>
      match rewrite_unbrand_or_fail s x, rewrite_unbrand_or_fail s y, rewrite_unbrand_or_fail s z with
      | Some x', Some y', Some z' => Some (DNRCIf a x' y' z')
      | _, _, _ => None
      end
    | DNRCEither a x b y c z =>
      match rewrite_unbrand_or_fail s x, rewrite_unbrand_or_fail s y, rewrite_unbrand_or_fail s z with
      | Some x', Some y', Some z' => Some (DNRCEither a x' b y' c z')
      | _, _, _ => None
      end
    | DNRCCollect a x =>
      lift (DNRCCollect a) (rewrite_unbrand_or_fail s x)
    | DNRCDispatch a x =>
      lift (DNRCDispatch a) (rewrite_unbrand_or_fail s x)
    (* TODO Can we discover uses of the variable s in an algebra expression? *)
    | DNRCAlg _ _ _ => None
    end.

  Definition rec_lift_unbrand
             {A : Set}
             (e: dnrc (type_annotation _ _ A) dataset):
    option (dnrc (type_annotation _ _ _) dataset) :=
    match e with
    | DNRCFor t1 x (DNRCCollect t2 xs as c) e =>
      match lift_tlocal (di_required_typeof c) with
      | Some (exist _ (Coll₀ (Brand₀ bs)) _) =>
        let t := proj1_sig (brands_type bs) in
        match rewrite_unbrand_or_fail x e with
        | Some e' =>
          let ALG :=
              (* TODO fresh name for lift_unbrand! *)
              DNRCAlg (dnrc_annotation_get xs)
                      (DSSelect ((CAs "$blob" (CCol "unbranded.$blob"))
                                   ::(CAs "$known" (CCol "unbranded.$known"))::nil)
                                (DSSelect ((CUDFUnbrand "unbranded" t (CCol "$data"))::nil)
                                          (DSVar "lift_unbrand")))
                      (("lift_unbrand"%string, xs)::nil)
          in
          Some (DNRCFor t1 x (DNRCCollect t2 ALG) e')
        | None => None
        end
      | _ => None
      end
    | _ => None
    end.

  Fixpoint condition_to_column {A: Set}
           (e: dnrc (type_annotation _ _ A) dataset)
           (cname: string)
           (binding: (string * column)) :=
    match e with
    (* TODO figure out how to properly handle vars and projections *)
    | DNRCUnop _ (ADot fld) (DNRCVar _ n) =>
      let (var, _) := binding in
      if (n == var)
      then Some (CAs cname (CCol ("$known."%string ++ fld)))
      else None
(*    | DNRCVar _ n =>
      (* TODO generalize to multiple bindings, for joins *)
      let (var, expr) := binding in
      if (n == var)
      then Some expr
      else None
    | DNRCUnop _ (ADot fld) c =>
      lift (fun c =>
              (CDot cname fld c))
           (condition_to_column c "c" binding) *)
    | DNRCConst _ d =>
      lift (fun t => CLit cname (d, (proj1_sig t))) (lift_tlocal (di_required_typeof e))
    | DNRCBinop _ AEq l r =>
      (* TODO check that the types of l and r admit Spark built-in equality *)
      match condition_to_column l "l" binding, condition_to_column r "r" binding with
      | Some l', Some r' =>
        Some (CEq cname l' r')
      | _, _ => None
      end
    | _ => None
    end.

  Definition rec_if_else_empty_to_filter {A: Set}
             (e: dnrc (type_annotation _ _ A) dataset):
    option (dnrc (type_annotation _ _ A) dataset) :=
    match e with
    | DNRCUnop t1 AFlatten
               (DNRCFor t2 x (DNRCCollect t3 xs)
                        (DNRCIf _ condition
                                thenE
                                (DNNRC.DNRCConst _ (dcoll nil)))) =>
      match condition_to_column condition "ignored" (x, CCol "abc") with
      | Some c' =>
        let ALG :=
            DNRCAlg (dnrc_annotation_get xs)
                    (DSFilter c' (DSVar "if_else_empty_to_filter"))
                    (("if_else_empty_to_filter"%string, xs)::nil)
        in
        Some (DNRCUnop t1 AFlatten
                       (DNRCFor t2 x (DNRCCollect t3 ALG)
                                thenE))
      | None => None
      end
    | _ => None
    end.

End DNNRCSparkIRRewrites.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
