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

Section Helpers.
  Require Import String.
  Definition eol := String (Ascii.ascii_of_nat 10) EmptyString.

  Fixpoint indent (i : nat) : string
    := match i with
       | 0 => ""
       | S j => "  " ++ (indent j)
       end.

End Helpers.

Require Import List String.
Require Import Peano_dec.
Require Import EquivDec.

Require Import Utils BasicSystem.
Require Import NNRCRuntime ForeignToJava.
Require Import DNNRC.
Require Import RType.
Require Import TDataInfer.
Require Import TDNRCInfer.
Require Import TOpsInfer.
Require Import SparkData.
Require Import SparkIR.

Local Open Scope string_scope.

Section DNNRCtoScala.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.

  Definition quote_string (s: string) : string :=
    """" ++ s ++ """".

  (** Scala-level type of an rtype.
   *
   * These are things like Int, String, Boolean, Array[...], Row.
   *
   * We need to annotate some expressions with Scala-level types
   * (e.g. Array[Row]() for an empty Array of Records) to help
   * the Scala compiler because it does not infer types everywhere.
   *)
  Fixpoint rtype_to_scala_type {ftype: foreign_type} (t: rtype₀): string :=
    match t with
    | Bottom₀ => "BOTTOM?"
    | Top₀ => "TOP?"
    | Unit₀ => "Unit"
    | Nat₀ => "Int"
    | Bool₀ => "Boolean"
    | String₀ => "String"
    | Coll₀ r => "Array[" ++ rtype_to_scala_type r ++ "]"
    | Rec₀ _ _ => "Record"
    | Either₀ tl tr => "Either"
    | Brand₀ bs => "BrandedValue"
    | Arrow₀ tin t => "CANNOT PUT AN ARROW INTO A DATASET"
    | Foreign₀ f => "FOREIGN?"
    end.

  Definition drtype_to_scala {ftype: foreign_type} {br: brand_relation} (t: drtype): string :=
    match t with
    | Tlocal r => rtype_to_scala_type (proj1_sig r)
    | Tdistr r => "Dataset[" ++ rtype_to_scala_type (proj1_sig r) ++ "]"
    end.

  (* This produces literal data at the correct type.
   * TODO actually write this. Currently this is only just enough for test07 to run. *)
  Fixpoint scala_literal_data {fttojs: ForeignToJavascript.foreign_to_javascript} {ftype: foreign_type} {m: brand_model} (d: data) (t: rtype₀) {struct t}: string :=
    match t, d with
    | Unit₀, d => "()"
    | Nat₀, dnat i => Z_to_string10 i
    | Bool₀, dbool true => "true"
    | Bool₀, dbool false => "false"
    | String₀, dstring s => quote_string s
    | Coll₀ r, dcoll xs =>
      let element_type := rtype_to_scala_type r in
      let elements := map (fun x => scala_literal_data x r) xs in
      "Array[" ++ element_type ++ "](" ++ joinStrings ", " elements ++ ")"
    | Rec₀ _ fts, drec fds =>
      let blob := quote_string (data_to_blob d) in
      let known_schema :=
          "StructType(Seq("
            ++ joinStrings ", "
            (map (fun ft =>
                    "StructField(""" ++ fst ft ++ """, " ++ rtype_to_scala (snd ft) ++ ")")
                 fts)
            ++ "))" in
      let fields := map (fun ft => match lookup string_dec fds (fst ft) with
                                   | Some d => scala_literal_data d (snd ft)
                                   | None => "FIELD_IN_TYPE_BUT_NOT_IN_DATA"
                                   end) fts in
      let known := "srow(" ++ joinStrings ", " (known_schema :: fields) ++ ")" in
      "srow(StructType(Seq(StructField(""$blob"", StringType), StructField(""$known"", " ++ known_schema ++ "))), " ++ blob ++ ", " ++ known ++ ")"
    (* TODO Some of these can't happen, some are just not implemented *)
    | _, _ => "UNIMPLEMENTED_SCALA_LITERAL_DATA"
    end.

  Definition scala_of_unop {ftype: foreign_type} {m: brand_model} (required_type: drtype) (op: unaryOp) (x: string) : string :=
    let prefix s := s ++ "(" ++ x ++ ")" in
    let postfix s := x ++ "." ++ s in
    match op with
    | AArithMean => prefix "arithMean"
    | ABrand bs => "brand(" ++ joinStrings ", " (x::(map quote_string bs)) ++ ")"
    | ACast bs =>
      "cast(" ++ x ++ ", " ++ joinStrings ", " (map quote_string bs) ++ ")"
    | AColl => prefix "Array"
    | ACount => postfix "length"
    | ADot n =>
      match lift_tlocal required_type with
      | Some r =>
        prefix ("dot[" ++ rtype_to_scala_type (proj1_sig r) ++ "](""" ++ n ++ """)")
      | None => "NONLOCAL EXPECTED TYPE IN DOT"
      end
    | AFlatten => postfix "flatten.sorted(QCertOrdering)"
    | AIdOp => prefix "identity"
    | ALeft => prefix "left"
    | ANeg => "(!" ++ x ++ ")"
    | ANumMax => prefix "anummax"
    | ANumMin => prefix "anummin"
    | ARec n =>
      match lift_tlocal required_type with
      | Some (exist _ (Rec₀ Closed ((_, ft)::nil)) _) =>
        "singletonRecord(" ++ quote_string n ++ ", " ++ rtype_to_scala ft ++ ", " ++ x ++ ")"
      | _ => "AREC_WITH_UNEXPECTED_REQUIRED_TYPE"
      end
    | ARecProject fs => prefix ("recProject(" ++ joinStrings ", " (map quote_string fs) ++ ")")
    | ARight => prefix "right"
    | ASum => postfix "sum"
    | AToString => prefix "toBlob" (* TODO what are the exact semantics for AToString? *)
    | AUArith ArithAbs => prefix "Math.abs"
    | AUnbrand =>
      match lift_tlocal required_type with
      | Some (exist _ r _) =>
        let schema := rtype_to_scala r in
        let scala := rtype_to_scala_type r in
        "unbrand[" ++ scala ++ "](" ++ schema ++ ", " ++ x ++ ")"
      | None => "UNBRAND_REQUIRED_TYPE_ISSUE"
      end
    | ADistinct => postfix "distinct"

    (* TODO *)
    | AForeignUnaryOp _ => "AFOREIGNUNARYOP???"
    | ARecRemove _ => "ARECREMOVE???"
    | ASingleton => "SINGLETON???"
    | AUArith ArithLog2 => "LOG2???" (* Integer log2? Not sure what the Coq semantics are. *)
    | AUArith ArithSqrt => "SQRT???" (* Integer sqrt? Not sure what the Coq semantics are. *)
    end.

  Definition scala_of_binop (op: binOp) (l: string) (r: string) : string :=
    (* Put parens outside? (l op r) *)
    let infix s := l ++ "." ++ s ++ "(" ++ r ++ ")" in
    let infix' s := "(" ++ l ++ " " ++ s ++ " " ++ r ++ ")" in
    let prefix s := s ++ "(" ++ l ++ ", " ++ r ++ ")" in
    match op with
    | AAnd => infix "&&"
    | ABArith ArithDivide => infix "/"
    | ABArith ArithMax => infix "max"
    | ABArith ArithMin => infix "min"
    | ABArith ArithMinus => infix "-"
    | ABArith ArithMult => infix "*"
    | ABArith ArithPlus => infix "+"
    | ABArith ArithRem => infix "%" (* TODO double check the exact semantics of this *)
    | AConcat => prefix "recordConcat"
    | AContains => prefix "AContains" (* left argument is the element, right element is the collection *)
    (* TODO We also need to fix operators that use equality internally:
     *      Contains, comparisons, AMax, AMin, AMinus, AUnion *)
    | AEq => prefix "equal"
    | ALe => prefix "lessOrEqual"
    | ALt => prefix "lessThan"
    (* TODO we might want to put convenience helpers into the runtime for these *)
    | AMax => l ++ ".++(" ++ r ++ ".diff(" ++ l ++ "))" (* l1 ⊎ (l2 ⊖ l1) *)
    | AMin => l ++ ".diff(" ++ l ++ ".diff(" ++ r ++ "))" (* l1 ⊖ (l1 ⊖ l2) Can't make recursive calls, but AMinus is weird anyways... *)
    | AMinus => r ++ ".diff(" ++ l ++ ")" (* bag minus has operands "the wrong way" around *)
    | AMergeConcat => prefix "mergeConcat"
    | AOr => infix "||"
    | ASConcat => infix "+" (* string concat *)
    | AUnion => infix "++" ++ ".sorted(QCertOrdering)" (* bag union *)

    (* TODO *)
    | AForeignBinaryOp op => "FOREIGNBINARYOP???"
    end.

  Fixpoint scala_of_dnrc {A: Set} {ft:foreign_type} {fdt:foreign_data_typing} {m:brand_model} {fttojs: ForeignToJavascript.foreign_to_javascript} (d: dnrc (type_annotation ft m A) dataset) : string :=
    let code :=
        match d with
        | DNRCVar t n => n (* "(" ++ n ++ ": " ++ drtype_to_scala (di_typeof d) ++ ")" *)
        | DNRCConst t c =>
          match (lift_tlocal (di_required_typeof d)) with
          | Some r => scala_literal_data c (proj1_sig r)
          | None => "Don't know how to construct a distributed constant"
          end
        | DNRCBinop t op x y =>
          scala_of_binop op (scala_of_dnrc x) (scala_of_dnrc y)
        | DNRCUnop t op x =>
          scala_of_unop (di_required_typeof d) op (scala_of_dnrc x)
        | DNRCLet t n x y => (* let n: t = x in y *) (* TODO could use line break *)
          "{ val " ++ n ++ ": " ++ drtype_to_scala (di_typeof x) ++ " = " ++ scala_of_dnrc x ++ "; " ++
                   scala_of_dnrc y ++ " }"
        | DNRCFor t n x y => (* x.map((n: t) => y) *) (* TODO might not need braces, could use line breaks *)
          scala_of_dnrc x ++ ".map((" ++ n ++ ") => { " ++ scala_of_dnrc y ++ " })"
        | DNRCIf t x y z => (* if (x) y else z *) (* TODO might not need parentheses *)
          "(if (" ++ scala_of_dnrc x ++ ") " ++ scala_of_dnrc y ++ " else " ++ scala_of_dnrc z ++ ")"
        | DNRCEither t x vy y vz z =>
          match olift tuneither (lift_tlocal (di_required_typeof x)) with
          | Some (lt, rt) =>
            "either(" ++ scala_of_dnrc x ++ ", (" ++
                      vy ++ ": " ++ rtype_to_scala_type (proj1_sig lt) ++
                      ") => { " ++ scala_of_dnrc y ++ " }, (" ++
                      vz ++ ": " ++ rtype_to_scala_type (proj1_sig rt) ++
                      ") => { " ++ scala_of_dnrc z ++ " })"
          | None => "DNRCEither's first argument is not of type Either"
          end
        | DNRCCollect t x => scala_of_dnrc x ++ ".collect()"
        (* TODO handle bags of non-record types (ints, strings, bags, ...) *)
        | DNRCDispatch t x =>
          match olift tuncoll (lift_tlocal (di_typeof x)) with
          | Some et =>
            "dispatch(" ++ rtype_to_scala (proj1_sig et) ++ ", " ++ scala_of_dnrc x ++ ")"
          | None => "Argument to dispatch is not a local collection."
          end
        | DNRCAlg t a ((x, d)::nil) =>
          (* TODO think again about how to pass arguments to algebra code.. *)
          "{ val " ++ x ++ " = " ++ scala_of_dnrc d ++ "; " ++
                   code_of_dataset a
                   ++ " }"
        | DNRCAlg _ _ _ =>
          "NON_UNARY_ALG_CODEGEN_IS_NOT_CURRENTLY_IMPLEMENTED"
        end in
    if di_typeof d == di_required_typeof d then code else
      match lift_tlocal (di_required_typeof d) with
      (* TODO Actually have a way to do arbitrary casts.
       *
       * Going through blobs did not quite work, because the fromBlob code in the runtime
       * has (Scala-level) type safety issues.
       * We think that perhaps we only need a different required type for literal data.
       * That would be great, because that already works by emitting the data at the
       * correct type in the first place. If this is indeed the only case, we can just
       * remove this whole casting business here. We would need to prove that of course...
       *
       * For now, use identity as a marker.
       *)
      | Some r => "identity/*CAST*/(" ++ code ++ ")"
      | None => "CANTCASTTODISTRIBUTEDTYPE"
      end.

  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  Context {fdtyping:foreign_data_typing}.
  Context {fboptyping:foreign_binary_op_typing}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {fttjs: ForeignToJavascript.foreign_to_javascript}.

  Require Import SparkIR.

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
                        (DNRCEither _ (DNRCUnop _ (ACast brands) (DNRCVar _ x'))
                                    leftVar
                                    leftE
                                    _
                                    (DNNRC.DNRCConst _ (dcoll nil)))) =>
      if (x == x')
      then
        let ALG := (DNRCAlg (dnrc_annotation_get xs)
                            (DSFilter (CUDFCast "_ignored" brands (CCol "$type"))
                                      (DSVar "map_cast"))
                            (("map_cast", xs)::nil))
        in
        Some (DNRCUnop t1 AFlatten
                       (DNRCFor t2 leftVar (DNRCCollect t3 ALG)
                                leftE))
      else None
    | _ => None
    end.

  (* This should really be some clever monadic combinator thing to compose tree rewritings and strategies, think Stratego. *)
  Fixpoint tryBottomUp {A: Set} {plug_type: Set}
           (f: dnrc (type_annotation _ _ A) _ -> option (dnrc (type_annotation _ _ A) _))
           (e: dnrc (type_annotation _ _ A) _)
    : dnrc (type_annotation _ _ A) plug_type :=
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

  (** Toplevel entry to Spark2/Scala codegen *)

  Definition dnrcToSpark2Top {A : Set} (inputType:rtype) (name: string) (e: dnrc A dataset) : string :=
    let tdb: tdbindings :=
        ("CONST$WORLD", (Tdistr inputType))::nil
    in
    match infer_dnrc_type tdb e with
    | None =>
      "TYPE INFERENCE FAILED "
    | Some e' =>
      let e'' := tryBottomUp rec_cast_to_filter e' in
      ""
        ++ "import org.apache.spark.sql.types._" ++ eol
        ++ "import org.apache.spark.sql.{Dataset, Row}" ++ eol
        ++ "import org.apache.spark.sql.functions._" ++ eol
        ++ "import org.qcert.QCertRuntime" ++ eol
        ++ "object " ++ name ++ " extends QCertRuntime {" ++ eol
        ++ "val worldType = " ++ rtype_to_scala (proj1_sig inputType) ++ eol
        ++ "def run(CONST$WORLD: Dataset[Row]) = {" ++ eol
        ++ "println(toBlob(" ++ eol
        ++ scala_of_dnrc e'' ++ eol
        ++ "))" ++ eol
        ++ "}" ++ eol
        ++ "}"
    end.

End DNNRCtoScala.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
