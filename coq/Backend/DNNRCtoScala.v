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
Require Import Dataset.
Require Import SparkData.

Local Open Scope string_scope.

Section DNNRCtoScala.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  Context {fdtyping:foreign_data_typing}.
  Context {fboptyping:foreign_binary_op_typing}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {fttjs: ForeignToJavascript.foreign_to_javascript}.

  Definition quote_string (s: string) : string :=
    """" ++ s ++ """".

  (** Get code for a Spark DataType corresping to an rtype.
   *
   * These are things like StringType, ArrayType(...), StructType(Seq(FieldType(...), ...)), ...
   *
   * This function encodes details of our data representation, e.g. records are StructFields
   * with two toplevel fields $blob and $known, and the $known contains a record with the
   * statically known fields and their types.
   *)
  Fixpoint rtype_to_spark_DataType (r: rtype₀) : string :=
    match r with
    | Bottom₀ => "NullType"
    | Top₀ => "StringType"
    | Unit₀ => "NullType"
    | Nat₀ => "IntegerType"
    | Bool₀ => "BooleanType"
    | String₀ => "StringType"
    | Coll₀ e => "ArrayType(" ++ rtype_to_spark_DataType e ++ ")"
    | Rec₀ _ fields =>
      let known_fields: list string :=
          map (fun p => "StructField(""" ++ fst p ++ """, " ++ rtype_to_spark_DataType (snd p) ++ ")")
              fields in
      let known_struct := "StructType(Seq(" ++ joinStrings ", " known_fields ++ "))" in
      "StructType(Seq(StructField(""$blob"", StringType), StructField(""$known"", " ++ known_struct ++ ")))"
    | Either₀ l r =>
      "StructType(Seq(StructField(""$left"", " ++ rtype_to_spark_DataType l ++ "), StructField(""$right"", " ++ rtype_to_spark_DataType r ++ ")))"
    | Brand₀ _ =>
      "StructType(Seq(StructField(""$data"", StringType), StructField(""$type"", ArrayType(StringType))))"
    (* should not occur *)
    | Arrow₀ _ _ => "ARROW TYPE?"
    | Foreign₀ ft => "FOREIGN TYPE?"
    end.

  (** Scala-level type of an rtype.
   *
   * These are things like Int, String, Boolean, Array[...], Row.
   *
   * We need to annotate some expressions with Scala-level types
   * (e.g. Array[Row]() for an empty Array of Records) to help
   * the Scala compiler because it does not infer types everywhere.
   *)
  Fixpoint rtype_to_scala_type (t: rtype₀): string :=
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

  Definition drtype_to_scala (t: drtype): string :=
    match t with
    | Tlocal r => rtype_to_scala_type (proj1_sig r)
    | Tdistr r => "Dataset[" ++ rtype_to_scala_type (proj1_sig r) ++ "]"
    end.

  (* This produces literal data at the correct type.
   * TODO actually write this. Currently this is only just enough for test07 to run. *)
  Fixpoint scala_literal_data (d: data) (t: rtype₀) {struct t}: string :=
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
                    "StructField(""" ++ fst ft ++ """, " ++ rtype_to_spark_DataType (snd ft) ++ ")")
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

  Fixpoint code_of_column (c: column) : string :=
    match c with
    | CCol s => "column(""" ++ s ++ """)"
    | CDot fld c => code_of_column c ++ ".getField(" ++ quote_string fld ++ ")"
    | CEq c1 c2 => code_of_column c1 ++ ".equalTo(" ++ code_of_column c2 ++ ")"
    | CLit (d, r) => "lit(" ++ scala_literal_data d r ++ ")"
    | CNeg c => "not(" ++ code_of_column c ++ ")"
    | CPlus c1 c2 => code_of_column c1 ++ ".plus(" ++ code_of_column c2 ++ ")"
    | CSConcat c1 c2 =>
      "concat(" ++ code_of_column c1 ++ ", " ++ code_of_column c2 ++ ")"
    | CToString c =>
      "QCertRuntime.toQCertStringUDF(" ++ code_of_column c ++ ")"
    | CUDFCast bs c =>
      "QCertRuntime.castUDF(" ++ joinStrings ", " ("brandHierarchy"%string :: map quote_string bs) ++ ")(" ++ code_of_column c ++ ")"
    | CUDFUnbrand t c =>
      "QCertRuntime.unbrandUDF(" ++ rtype_to_spark_DataType t ++ ")(" ++ code_of_column c ++ ")"
    end.

  Fixpoint code_of_dataset (e: dataset) : string :=
    match e with
    | DSVar s => s
    | DSSelect cs d =>
      let columns :=
          map (fun nc => code_of_column (snd nc) ++ ".as(""" ++ fst nc ++ """)") cs in
      code_of_dataset d ++ ".select(" ++ joinStrings ", " columns ++ ")"
    | DSFilter c d => code_of_dataset d ++ ".filter(" ++ code_of_column c ++ ")"
    | DSCartesian d1 d2 => code_of_dataset d1 ++ ".join(" ++ (code_of_dataset d2) ++ ")"
    | DSExplode s d1 => code_of_dataset d1 ++ ".select(explode(" ++ code_of_column (CCol s) ++ ").as(""" ++ s ++ """))"
    end.

  Definition spark_of_unop (op: unaryOp) (x: string) : string :=
    match op with
    | ACount => x ++ ".count()" (* This returns a long, is this a problem? *)
    | _ => "SPARK_OF_UNOP don't know how to generate Spark code for this operator"
    end.

  Definition scala_of_unop (required_type: drtype) (op: unaryOp) (x: string) : string :=
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
        "singletonRecord(" ++ quote_string n ++ ", " ++ rtype_to_spark_DataType ft ++ ", " ++ x ++ ")"
      | _ => "AREC_WITH_UNEXPECTED_REQUIRED_TYPE"
      end
    | ARecProject fs => prefix ("recProject(" ++ joinStrings ", " (map quote_string fs) ++ ")")
    | ARight => prefix "right"
    | ASum => postfix "sum"
    | AToString => prefix "QCertRuntime.toQCertString"
    | AUArith ArithAbs => prefix "Math.abs"
    | AUnbrand =>
      match lift_tlocal required_type with
      | Some (exist _ r _) =>
        let schema := rtype_to_spark_DataType r in
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

  Definition spark_of_binop (op: binOp) (x: string) (y: string) : string :=
    match op with
    | AUnion => x ++ ".union(" ++ y ++ ")"
    | _ => "SPARK_OF_BINOP don't know how to generate Spark code for this operator"
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

  (* TODO Move this somewhere, I think rewriting needs something similar *)
  Definition primitive_type (t: rtype) :=
    match proj1_sig t with
    | ⊥₀ | ⊤₀ | Unit₀ | Nat₀ | String₀ | Bool₀ => true
    | Coll₀ _ | Rec₀ _ _ | Either₀ _ _ | Arrow₀ _ _ | Brand₀ _ => false
    (* TODO foreign? *)
    | Foreign₀ _ => false
    end.

  Fixpoint scala_of_dnrc {A: Set} (d: dnrc (type_annotation A) dataset) : string :=
    let code :=
        match d with
        | DNRCVar t n => n (* "(" ++ n ++ ": " ++ drtype_to_scala (di_typeof d) ++ ")" *)
        | DNRCConst t c =>
          match (lift_tlocal (di_required_typeof d)) with
          | Some r => scala_literal_data c (proj1_sig r)
          | None => "Don't know how to construct a distributed constant"
          end
        | DNRCBinop t op x y =>
          match di_typeof x, di_typeof y with
          | Tlocal _, Tlocal _ => scala_of_binop op (scala_of_dnrc x) (scala_of_dnrc y)
          | Tdistr _, Tdistr _ => spark_of_binop op (scala_of_dnrc x) (scala_of_dnrc y)
          | _, _ => "DONT_SUPPORT_MIXED_LOCAL_DISTRIBUTED_BINARY_OPERATORS"
          end
        | DNRCUnop t op x =>
          match di_typeof x with
          | Tlocal _ => scala_of_unop (di_required_typeof d) op (scala_of_dnrc x)
          | Tdistr _ => spark_of_unop op (scala_of_dnrc x)
          end
        | DNRCLet t n x y => (* let n: t = x in y *) (* TODO could use line break *)
          "{ val " ++ n ++ ": " ++ drtype_to_scala (di_typeof x) ++ " = " ++ scala_of_dnrc x ++ "; " ++
                   scala_of_dnrc y ++ " }"
        | DNRCFor t n x y =>
          (* TODO for distributed map of non-record-like-things we have to unwrap *)
          scala_of_dnrc x ++ ".map((" ++ n ++ ") => { " ++ scala_of_dnrc y ++ " })"
        | DNRCIf t x y z =>
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
        | DNRCCollect t x =>
          (* Distributed collections of primitives are wrapped in a singleton record.
           * We need to unwrap them after the call to collect(). *)
          let postfix :=
              match lift primitive_type (olift tuncoll (lift_tdistr (di_typeof x))) with
              | Some true => ".map((row) => row(0))"
              | Some false => ""
              | None => "ARGUMENT_TO_COLLECT_SHOULD_BE_DISTRIBUTED"
              end in
          scala_of_dnrc x ++ ".collect()" ++ postfix
        (* TODO handle bags of non-record types (ints, strings, bags, ...) *)
        | DNRCDispatch t x =>
          match olift tuncoll (lift_tlocal (di_typeof x)) with
          | Some et =>
            "dispatch(" ++ rtype_to_spark_DataType (proj1_sig et) ++ ", " ++ scala_of_dnrc x ++ ")"
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

  Definition dnnrc_infer_type {A: Set} (e: dnrc A dataset) (inputType: rtype)
    : option (dnrc (type_annotation A) dataset) :=
    let tdb: tdbindings :=
        ("CONST$WORLD"%string, (Tdistr inputType))::nil in
    infer_dnrc_type tdb e.

  Definition initBrandHierarchy : string :=
    let lines :=
        map (fun p => "addToBrandHierarchy(""" ++ (fst p) ++ """, """ ++ snd p ++ """);")
            brand_relation_brands in
    joinStrings " " lines.

  (** Toplevel entry to Spark2/Scala codegen *)

  Definition dnrcToSpark2Top {A : Set} (inputType:rtype) (name: string)
             (e: dnrc (type_annotation A) dataset) : string :=
    ""
      ++ "import org.apache.spark.sql.types._" ++ eol
      ++ "import org.apache.spark.sql.{Dataset, Row}" ++ eol
      ++ "import org.apache.spark.sql.functions._" ++ eol
      ++ "import org.qcert.QCertRuntime" ++ eol
      ++ "object " ++ name ++ " extends QCertRuntime {" ++ eol
      ++ initBrandHierarchy ++ eol
      ++ "val worldType = " ++ rtype_to_spark_DataType (proj1_sig inputType) ++ eol
      ++ "def run(CONST$WORLD: Dataset[Row]) = {" ++ eol
      (* sparkSession is a field in QCertRuntime. What it does in an import? I have no idea! *)
      ++ "  import sparkSession.implicits._" ++ eol
      ++ "println(toBlob(" ++ eol
      ++ scala_of_dnrc e ++ eol
      ++ "))" ++ eol
      ++ "}" ++ eol
      ++ "}"
  .

End DNNRCtoScala.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
