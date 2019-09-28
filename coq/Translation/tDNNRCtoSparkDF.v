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

Require Import String.

Section Helpers.
  Definition eol := String (Ascii.ascii_of_nat 10) EmptyString.
End Helpers.

Require Import List.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRCRuntime.
Require Import tDNNRCSystem.
Require Import ForeignToScala.
Require Import DatatoSparkDF.

Local Open Scope string_scope.

Section tDNNRCtoSparkDF.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  Context {fdtyping:foreign_data_typing}.
  Context {fboptyping:foreign_binary_op_typing}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {fttjs: ForeignToJavaScript.foreign_to_javascript}.
  Context {fts: ForeignToScala.foreign_to_scala}.
  Context {ftjson:foreign_to_JSON}.

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
    | Nat₀ => "LongType"
    | Float₀ => "DoubleType"
    | Bool₀ => "BooleanType"
    | String₀ => "StringType"
    | Coll₀ e => "ArrayType(" ++ rtype_to_spark_DataType e ++ ")"
    | Rec₀ _ fields =>
      let known_fields: list string :=
          map (fun p => "StructField(""" ++ fst p ++ """, " ++ rtype_to_spark_DataType (snd p) ++ ")")
              fields in
      let known_struct := "StructType(Seq(" ++ String.concat ", " known_fields ++ "))" in
      "StructType(Seq(StructField(""$blob"", StringType), StructField(""$known"", " ++ known_struct ++ ")))"
    | Either₀ l r =>
      "StructType(Seq(StructField(""$left"", " ++ rtype_to_spark_DataType l ++ "), StructField(""$right"", " ++ rtype_to_spark_DataType r ++ ")))"
    | Brand₀ _ =>
      "StructType(Seq(StructField(""$data"", StringType), StructField(""$type"", ArrayType(StringType))))"
    (* should not occur *)
    | Arrow₀ _ _ => "ARROW TYPE?"
    | Foreign₀ ft => foreign_to_scala_spark_datatype ft
    end.

  (** Scala-level type of an rtype.
   *
   * These are things like Long, String, Boolean, Array[...], Row.
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
    | Nat₀ => "Long"
    | Float₀ => "Double"
    | Bool₀ => "Boolean"
    | String₀ => "String"
    | Coll₀ r => "Array[" ++ rtype_to_scala_type r ++ "]"
    | Rec₀ _ _ => "Record"
    | Either₀ tl tr => "Either"
    | Brand₀ bs => "BrandedValue"
    | Arrow₀ tin t => "CANNOT PUT AN ARROW INTO A DATAFRAME"
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
      "Array[" ++ element_type ++ "](" ++ String.concat ", " elements ++ ")"
    | Rec₀ _ fts, drec fds =>
      let blob := quote_string (data_to_blob d) in
      let known_schema :=
          "StructType(Seq("
            ++ String.concat ", "
            (map (fun ft =>
                    "StructField(""" ++ fst ft ++ """, " ++ rtype_to_spark_DataType (snd ft) ++ ")")
                 fts)
            ++ "))" in
      let fields := map (fun ft => match lookup string_dec fds (fst ft) with
                                   | Some d => scala_literal_data d (snd ft)
                                   | None => "FIELD_IN_TYPE_BUT_NOT_IN_DATA"
                                   end) fts in
      let known := "srow(" ++ String.concat ", " (known_schema :: fields) ++ ")" in
      "srow(StructType(Seq(StructField(""$blob"", StringType), StructField(""$known"", " ++ known_schema ++ "))), " ++ blob ++ ", " ++ known ++ ")"
    (* TODO Some of these can't happen, some are just not implemented *)
    | _, _ => "UNIMPLEMENTED_SCALA_LITERAL_DATA"
    end.

  Fixpoint code_of_column (c: column) : string :=
    match c with
    | CCol s => "column(""" ++ s ++ """)"
    | CDot fld c => code_of_column c ++ ".getField(" ++ quote_string fld ++ ")"
    | CEq c1 c2 => code_of_column c1 ++ ".equalTo(" ++ code_of_column c2 ++ ")"
    | CLessThan c1 c2 => code_of_column c1 ++ ".lt(" ++ code_of_column c2 ++ ")"
    | CLit (d, r) => "lit(" ++ scala_literal_data d r ++ ")"
    | CNeg c => "not(" ++ code_of_column c ++ ")"
    | CPlus c1 c2 => code_of_column c1 ++ ".plus(" ++ code_of_column c2 ++ ")"
    | CSConcat c1 c2 =>
      "concat(" ++ code_of_column c1 ++ ", " ++ code_of_column c2 ++ ")"
    | CToString c =>
      "toQcertStringUDF(" ++ code_of_column c ++ ")"
    | CUDFCast bs c =>
      "castUDF(" ++ String.concat ", " ("INHERITANCE"%string :: map quote_string bs) ++ ")(" ++ code_of_column c ++ ")"
    | CUDFUnbrand t c =>
      "unbrandUDF(" ++ rtype_to_spark_DataType t ++ ")(" ++ code_of_column c ++ ")"
    end.

  Fixpoint code_of_dataframe (e: dataframe) : string :=
    match e with
    | DSVar s => s
    | DSSelect cs d =>
      let columns :=
          map (fun nc => code_of_column (snd nc) ++ ".as(""" ++ fst nc ++ """)") cs in
      code_of_dataframe d ++ ".select(" ++ String.concat ", " columns ++ ")"
    | DSFilter c d => code_of_dataframe d ++ ".filter(" ++ code_of_column c ++ ")"
    | DSCartesian d1 d2 => code_of_dataframe d1 ++ ".join(" ++ (code_of_dataframe d2) ++ ")"
    | DSExplode s d1 => code_of_dataframe d1 ++ ".select(explode(" ++ code_of_column (CCol s) ++ ").as(""" ++ s ++ """))"
    end.

  Definition spark_of_unary_op (op: unary_op) (x: string) : string :=
    match op with
      (* ACount, ASum are distributed to local *)
      | OpCount => x ++ ".count()" (* This returns a long, is this a problem? *)
      | OpNatSum => x ++ ".select(sum(""value"")).first().getLong(0)" (* This is not pretty, but there does not seem to be a .sum() *)
      (* AFlatten is distributed to distributed *)
      (* TODO FIXME ...but this implementation is distributed to local, right?
        Fix this. Might make the whole collect unwrap issue go away *)
      | OpFlatten => x ++ ".flatMap(r => r)"
      | _ => "SPARK_OF_UNARY_OP don't know how to generate Spark code for this operator"
    end.

  Definition scala_of_unary_op (required_type: drtype) (op: unary_op) (x: string) : string :=
    let prefix s := s ++ "(" ++ x ++ ")" in
    let postfix s := x ++ "." ++ s in
    match op with
    | OpIdentity => prefix "identity"
    | OpNeg => "(!" ++ x ++ ")"
    | OpRec n =>
      match lift_tlocal required_type with
      | Some (exist _ (Rec₀ Closed ((_, ft)::nil)) _) =>
        "singletonRecord(" ++ quote_string n ++ ", " ++ rtype_to_spark_DataType ft ++ ", " ++ x ++ ")"
      | _ => "AREC_WITH_UNEXPECTED_REQUIRED_TYPE"
      end
    | OpDot n =>
      match lift_tlocal required_type with
      | Some r =>
        prefix ("dot[" ++ rtype_to_scala_type (proj1_sig r) ++ "](""" ++ n ++ """)")
      | None => "NONLOCAL EXPECTED TYPE IN DOT"
      end
    | OpRecProject fs => prefix ("recProject(" ++ String.concat ", " (map quote_string fs) ++ ")")
    | OpBag => prefix "Array"
    | OpFlatten => postfix "flatten.sorted(QcertOrdering)"
    | OpDistinct => postfix "distinct"
    | OpCount => postfix "length"
    | OpToText
    | OpToString => prefix "toQcertString"
    | OpLength => "(" ++ x ++ ").length()"
    | OpSubstring start olen =>
      "(" ++ x ++ ").substring(" ++ toString start ++
          match olen with
          | Some len => ", " ++ toString len
          | None => ""
          end ++ ")"
    | OpLike pat oescape =>
      "ALike currently implemented.  Please implement as in the java backend"
(*      let lc := make_like_clause pat oescape in
      mk_java_unary_op1 "string_like" ("new LikeClause[]{" ++ (joinStrings "," (map like_clause_to_scala lc)) ++ "}") e1
*)
    | OpLeft => prefix "left"
    | OpRight => prefix "right"
    | OpBrand bs => "brand(" ++ String.concat ", " (x::(map quote_string bs)) ++ ")"
    | OpCast bs =>
      "cast(INHERITANCE, " ++ x ++ ", " ++ String.concat ", " (map quote_string bs) ++ ")"
    | OpUnbrand =>
      match lift_tlocal required_type with
      | Some (exist _ r _) =>
        let schema := rtype_to_spark_DataType r in
        let scala := rtype_to_scala_type r in
        "unbrand[" ++ scala ++ "](" ++ schema ++ ", " ++ x ++ ")"
      | None => "UNBRAND_REQUIRED_TYPE_ISSUE"
      end
    | OpNatUnary NatAbs => prefix "Math.abs"
    | OpNatSum => postfix "sum"
    | OpNatMax => prefix "anummax"
    | OpNatMin => prefix "anummin"
    | OpNatMean => prefix "arithMean"
    | OpForeignUnary o => foreign_to_scala_unary_op o x
    | OpFloatSum => postfix "sum"

    (* TODO *)
    | OpFloatOfNat => prefix "FLOAT OF NAT??"
    | OpFloatUnary _ => prefix "FLOAT ARITH??"
    | OpFloatTruncate => prefix "TRUNCATE??"
    | OpFloatBagMax => prefix "MAX??"
    | OpFloatBagMin => prefix "MIN??"
    | OpFloatMean => prefix "MEAN??"
    | OpOrderBy scl => "SORT???" (* XXX Might be nice to try and support -JS XXX *)
    | OpRecRemove _ => "ARECREMOVE???"
    | OpSingleton => "SINGLETON???"
    | OpNatUnary NatLog2 => "LOG2???" (* Integer log2? Not sure what the Coq semantics are. *)
    | OpNatUnary NatSqrt => "SQRT???" (* Integer sqrt? Not sure what the Coq semantics are. *)
    end.

  Definition spark_of_binary_op (op: binary_op) (x: string) (y: string) : string :=
    match op with
    | OpBagUnion => x ++ ".union(" ++ y ++ ")"
    | _ => "SPARK_OF_BINARY_OP don't know how to generate Spark code for this operator"
    end.

  Definition scala_of_binary_op (op: binary_op) (l: string) (r: string) : string :=
    (* Put parens outside? (l op r) *)
    let infix s := l ++ "." ++ s ++ "(" ++ r ++ ")" in
    let infix' s := "(" ++ l ++ " " ++ s ++ " " ++ r ++ ")" in
    let prefix s := s ++ "(" ++ l ++ ", " ++ r ++ ")" in
    match op with
    | OpEqual => prefix "equal"
    | OpRecConcat => prefix "recordConcat"
    | OpRecMerge => prefix "mergeConcat"
    | OpAnd => infix "&&"
    | OpOr => infix "||"
    | OpLe => prefix "lessOrEqual"
    | OpLt => prefix "lessThan"
    (* TODO We also need to fix operators that use equality internally:
     *      Contains, comparisons, OpBagMax, OpBagMin, OpBagDiff, OpBagUnion *)
    (* TODO we might want to put convenience helpers into the runtime for these *)
    | OpBagUnion => infix "++" ++ ".sorted(QcertOrdering)" (* bag union *)
    | OpBagDiff => r ++ ".diff(" ++ l ++ ")" (* bag minus has operands "the wrong way" around *)
    | OpBagMax => l ++ ".++(" ++ r ++ ".diff(" ++ l ++ "))" (* l1 ⊎ (l2 ⊖ l1) *)
    | OpBagMin => l ++ ".diff(" ++ l ++ ".diff(" ++ r ++ "))" (* l1 ⊖ (l1 ⊖ l2) Can't make recursive calls, but AMinus is weird anyways... *)
    | OpBagNth => prefix "bagNth"
    | OpContains => prefix "AContains" (* left argument is the element, right element is the collection *)
    | OpStringConcat => infix "+" (* string concat *)
    | OpStringJoin => prefix "AStringJoin" (* left argument is the element, right element is the collection *)
    | OpNatBinary NatDiv => infix "/"
    | OpNatBinary NatMax => infix "max"
    | OpNatBinary NatMin => infix "min"
    | OpNatBinary NatMinus => infix "-"
    | OpNatBinary NatMult => infix "*"
    | OpNatBinary NatPlus => infix "+"
    | OpNatBinary NatRem => infix "%" (* TODO double check the exact semantics of this *)
    | OpFloatBinary FloatDiv => infix "/"
    | OpFloatBinary FloatMax => infix "max"
    | OpFloatBinary FloatMin => infix "min"
    | OpFloatBinary FloatMinus => infix "-"
    | OpFloatBinary FloatMult => infix "*"
    | OpFloatBinary FloatPlus => infix "+"
    | OpFloatBinary FloatRem => infix "%" (* TODO double check the exact semantics of this *)
    | OpFloatCompare FloatLt => infix "<"
    | OpFloatCompare FloatLe => infix "<="
    | OpFloatCompare FloatGt => infix ">"
    | OpFloatCompare FloatGe => infix ">="

    (* TODO *)
    | OpForeignBinary op => "FOREIGNBINARYOP???"
    end.

  (* TODO Move this somewhere, I think rewriting needs something similar *)
  Definition primitive_type (t: rtype) :=
    match proj1_sig t with
    | ⊥₀ | ⊤₀ | Unit₀ | Nat₀ | Float₀ | String₀ | Bool₀ => true
    | Coll₀ _ | Rec₀ _ _ | Either₀ _ _ | Arrow₀ _ _ | Brand₀ _ => false
    (* TODO foreign? *)
    | Foreign₀ _ => false
    end.

  Fixpoint scala_of_dnnrc_base {A: Set} (d:@dnnrc_base _ (type_annotation A) dataframe) : string :=
    let code :=
        match d with
        | DNNRCGetConstant t n => n (* "(" ++ n ++ ": " ++ drtype_to_scala (di_typeof d) ++ ")" *)
        | DNNRCVar t n => n (* "(" ++ n ++ ": " ++ drtype_to_scala (di_typeof d) ++ ")" *)
        | DNNRCConst t c =>
          match (lift_tlocal (di_required_typeof d)) with
          | Some r => scala_literal_data c (proj1_sig r)
          | None => "Don't know how to construct a distributed constant"
          end
        | DNNRCBinop t op x y =>
          match di_typeof x, di_typeof y with
          | Tlocal _, Tlocal _ => scala_of_binary_op op (scala_of_dnnrc_base x) (scala_of_dnnrc_base y)
          | Tdistr _, Tdistr _ => spark_of_binary_op op (scala_of_dnnrc_base x) (scala_of_dnnrc_base y)
          | _, _ => "DONT_SUPPORT_MIXED_LOCAL_DISTRIBUTED_BINARY_OPERATORS"
          end
        | DNNRCUnop t op x =>
          match di_typeof x with
          | Tlocal _ => scala_of_unary_op (di_required_typeof d) op (scala_of_dnnrc_base x)
          | Tdistr _ => spark_of_unary_op op (scala_of_dnnrc_base x)
          end
        | DNNRCLet t n x y => (* Scala val is letrec, use anonymous function instead *)
          "((( " ++ n ++ ": " ++ drtype_to_scala (di_typeof x) ++ ") => " ++ scala_of_dnnrc_base y ++ ")(" ++ scala_of_dnnrc_base x ++ "))"
        | DNNRCFor t n x y =>
          (* TODO for distributed map of non-record-like-things we have to unwrap *)
          scala_of_dnnrc_base x ++ ".map((" ++ n ++ ") => { " ++ scala_of_dnnrc_base y ++ " })"
        | DNNRCIf t x y z =>
          "(if (" ++ scala_of_dnnrc_base x ++ ") " ++ scala_of_dnnrc_base y ++ " else " ++ scala_of_dnnrc_base z ++ ")"
        | DNNRCEither t x vy y vz z =>
          match olift tuneither (lift_tlocal (di_required_typeof x)) with
          | Some (lt, rt) =>
            "either(" ++ scala_of_dnnrc_base x ++ ", (" ++
                      vy ++ ": " ++ rtype_to_scala_type (proj1_sig lt) ++
                      ") => { " ++ scala_of_dnnrc_base y ++ " }, (" ++
                      vz ++ ": " ++ rtype_to_scala_type (proj1_sig rt) ++
                      ") => { " ++ scala_of_dnnrc_base z ++ " })"
          | None => "DNNRCEither's first argument is not of type Either"
          end
        (* XXX TODO! XXX *)
        | DNNRCGroupBy t g sl x =>
          "DNNRC_GROUPBY_CODEGEN_IS_NOT_CURRENTLY_IMPLEMENTED"
        | DNNRCCollect t x =>
          (* Distributed collections of primitives are wrapped in a singleton record.
           * We need to unwrap them after the call to collect(). *)
          let postfix :=
              match olift tuncoll (lift_tdistr (di_typeof x)) with
              | Some rt =>
                match proj1_sig rt with
                | Nat₀ => ".map((row) => row.getLong(0))"
                | Foreign₀ _ => ".map((row) => row.getFloat(0))" (* TODO move to ForeignToScala type class *)
                | _ => "" (* TODO figure out when we actually need this *)
                         (* ".map((row) => row(0))" (* Hope for Scala to figure it out *) *)
                end
              | None => "ARGUMENT_TO_COLLECT_SHOULD_BE_A_DISTRIBUTED_COLLECTION"
              end in
          scala_of_dnnrc_base x ++ ".collect()" ++ postfix
        (* TODO handle bags of non-record types (ints, strings, bags, ...) *)
        | DNNRCDispatch t x =>
          match olift tuncoll (lift_tlocal (di_typeof x)) with
          | Some et =>
            "dispatch(" ++ rtype_to_spark_DataType (proj1_sig et) ++ ", " ++ scala_of_dnnrc_base x ++ ")"
          | None => "Argument to dispatch is not a local collection."
          end
        | DNNRCAlg t a ((x, d)::nil) =>
          (* TODO does this also need the lambda encoding for let? *)
          "{ val " ++ x ++ " = " ++ scala_of_dnnrc_base d ++ "; " ++
                   code_of_dataframe a
                   ++ " }"
        | DNNRCAlg _ _ _ =>
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

  Definition initBrandInheritance : string :=
    let lines :=
        map (fun p => "(""" ++ fst p ++ """ -> """ ++ snd p ++ """)")
            brand_relation_brands in
    String.concat ", " lines.

  (* Walk through toplevel constant bindings and emit local scala bindings `val
    NAME = ...`. We read distributed collections as files in Spark's JSON format
    (one JSON record per line, .sio). The file paths are just arguments to the
    main function. TODO Local input is currently not supported. We should
    probably read them in the JSON BLOB format we use for open records. *)
  Fixpoint emitGlobals (tenv: tdbindings) (fileArgCounter: nat) :=
    match tenv with
    | nil => ""
    | (name, Tlocal lt) :: rest => "LOCAL INPUT UNIMPLEMENTED"
    | (name, Tdistr elt) :: rest =>
      "val " ++ name ++ " = sparkSession.read.schema(" ++ rtype_to_spark_DataType (proj1_sig elt) ++ ").json(args(" ++ nat_to_string10 fileArgCounter ++ "))" ++ eol ++
      emitGlobals rest (fileArgCounter + 1)
    end.

  (** Toplevel entry to Spark2/Scala codegen *)
  Definition dnnrc_typed_to_spark_df_top {A : Set} (tenv:tdbindings) (name: string)
             (e:dnnrc_typed) : string :=
    ""
      ++ "import org.apache.spark.SparkContext" ++ eol
      ++ "import org.apache.spark.sql.functions._" ++ eol
      ++ "import org.apache.spark.sql.SparkSession" ++ eol
      ++ "import org.apache.spark.sql.types._" ++ eol
      ++ "import org.qcert.QcertRuntime" ++ eol
      ++ "import org.qcert.QcertRuntime._" ++ eol

      ++ "object " ++ name ++ " {" ++ eol
      ++ "def main(args: Array[String]): Unit = {" ++ eol
      ++ "val INHERITANCE = QcertRuntime.makeInheritance(" ++ initBrandInheritance ++ ")" ++ eol
      ++ "val sparkContext = new SparkContext()" ++ eol
      ++ "org.apache.log4j.Logger.getRootLogger().setLevel(org.apache.log4j.Level.WARN)" ++ eol
      ++ "val sparkSession = SparkSession.builder().getOrCreate()" ++ eol
      ++ emitGlobals tenv 0
      ++ "import sparkSession.implicits._" ++ eol
      ++ "QcertRuntime.beforeQuery()" ++ eol
      ++ "println(QcertRuntime.toBlob(" ++ eol
      ++ scala_of_dnnrc_base e ++ eol
      ++ "))" ++ eol
      ++ "QcertRuntime.afterQuery()" ++ eol
      ++ "sparkContext.stop()" ++ eol
      ++ "}" ++ eol
      ++ "}" ++ eol
  .

End tDNNRCtoSparkDF.

