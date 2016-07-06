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
Require Import SparkData.
Local Open Scope string_scope.

Section DNNRCtoScala.

  Context {f:foreign_runtime}.
  Context {h:brand_relation_t}.

  Definition quote_string (s: string) : string :=
    """" ++ s ++ """".

  (* TODO replace this by stuff from SparkData *)
  Fixpoint dataType_of_rtype₀ {ft:foreign_type} (t: rtype₀) :=
    match t with
    | Bottom₀ => "BOTTOM?"
    | Top₀ => "TOP?"
    | Unit₀ => "DataTypes.NullType"
    | Nat₀ => "DataTypes.IntegerType"
    | Bool₀ => "DataTypes.BooleanType"
    | String₀ => "DataTypes.StringType"
    | Coll₀ r => "ArrayType(" ++ dataType_of_rtype₀ r ++ ")"
    | Rec₀ Closed fs =>
      let fields :=
          map (fun (p : string * rtype₀) =>
                 let (n, t) := p in
                 "StructField(" ++ n ++ ", " ++ dataType_of_rtype₀ t ++ ")")
              fs in
      "StructType(" ++ fold_left (fun a b => a ++ "::" ++ b) fields "Nil" ++ ")"
    | Rec₀ Open _ => "DO NOT KNOW HOW TO DEAL WITH OPEN RECORDS YET"
    | Either₀ tl t => "eitherStructType(" ++ dataType_of_rtype₀ tl ++ ", " ++ dataType_of_rtype₀ t ++ ")"
    | Arrow₀ tin t => "CANNOT PUT AN ARROW INTO A DATASET"
    | Brand₀ bs => "UHM. WE NEED THE STRUCTURAL TYPE THAT IS BRANDED..."
    | Foreign₀ f => "TODO FIGURE OUT WHAT TO DO WITH FOREIGN TYPES"
    end.

  (* TODO replace this by stuff from SparkData *)
  Fixpoint scala_of_data {ft:foreign_type} {fdt:foreign_data_typing} (m:brand_model) (d: data) : string :=
    match d with
    | dstring s => quote_string s
    | dnat n => Z_to_string10 n
    | dunit => "null"
    | dbool true => "true"
    | dbool false => "false"
    | dcoll l => "Array/*[TODO]*/(" ++ joinStrings ", " (map (scala_of_data m) l) ++ ").sorted(QCertOrdering)"
    | dleft v => "left(" ++ (scala_of_data m v) ++ ")"
    | dright v => "right(" ++ (scala_of_data m v) ++ ")"
    | drec fields =>
      match @infer_data_type _ ft fdt m (normalize_data h d) with
      | Some t => dataType_of_rtype₀ (proj1_sig t)
      | None => "CANNOT INFER TYPE FROM DATA. SOMETHING IS SERIOUSLY BROKEN."
      end
    | dbrand _ _ => "DBRAND???"
    | dforeign _ => "DFOREIGN???"
    end.

  Definition scala_of_unop {ftype: foreign_type} {m: brand_model} (op: unaryOp) (x: string) : string :=
    let prefix s := s ++ "(" ++ x ++ ")" in
    let postfix s := x ++ "." ++ s in
    match op with
    | AArithMean => prefix "arithMean"
    | ABrand bs => "brand(" ++ joinStrings ", " (x::(map quote_string bs)) ++ ")"
    | ACast bs =>
      let t := stype_to_datatype (rtype_to_stype (proj1_sig (brands_type bs))) in
      "cast(" ++ joinStrings ", " (x :: t :: (map quote_string bs)) ++ ")"
    | AColl => prefix "Array"
    | ACount => postfix "length"
    | ADot n => prefix ("dot/*[TODO]*/(""" ++ n ++ """)")
    | AFlatten => postfix "flatten.sorted(QCertOrdering)"
    | AIdOp => prefix "identity"
    | ALeft => prefix "left"
    | ANeg => prefix "!"
    | ARec n => "singletonRecord(" ++ quote_string n ++ ", " ++ x ++ ")" (* TODO need to pass schema *)
    | ARight => prefix "right"
    | ASum => postfix "sum"
    | AToString => postfix "toString"
    | AUnbrand => prefix "unbrand/*[TODO]*/" (* TODO pass type *)
    | ADistinct => postfix "distinct"

    (* TODO *)
    | AForeignUnaryOp _ => "AFOREIGNUNARYOP???"
    | ANumMax => "ANUMMAX???" (* Maximum element in a bag? [] => 0 *)
    | ANumMin => "ANUMMIN???" (* Minimum element in a bag? [] => 0 *)
    | ARecProject _ => "ARECPROJECT???"
    | ARecRemove _ => "ARECREMOVE???"
    | ASingleton => "SINGLETON???"
    | AUArith _ => "AUARITH???"
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
    | AContains => infix "contains"
    (* TODO Scala equality is WRONG for records (Row), bags (Array), and possibly more (dates?) *)
    (* TODO We also need to fix operators that use equality internally:
     *      Contains, comparisons, AMax, AMin, AMinus, AUnion *)
    | AEq => infix "=="
    | ALe => infix "<="
    | ALt => infix "<"
    (* TODO we might want to put convenience helpers into the runtime for these *)
    | AMax => l ++ ".++(" ++ r ++ ".diff(" ++ l ++ "))" (* l1 ⊎ (l2 ⊖ l1) *)
    | AMin => l ++ ".diff(" ++ l ++ ".diff(" ++ r ++ "))" (* l1 ⊖ (l1 ⊖ l2) Can't make recursive calls, but AMinus is weird anyways... *)
    | AMinus => r ++ ".diff(" ++ l ++ ")" (* bag minus has operands "the wrong way" around *)
    | AMergeConcat => prefix "mergeConcat"
    | AOr => infix "||"
    | ASConcat => infix "++" (* string concat *)
    | AUnion => infix "++" ++ ".sorted(QCertOrdering)" (* bag union *)

    (* TODO *)
    | AForeignBinaryOp op => "FOREIGNBINARYOP???"
    end.

  Fixpoint scala_of_dnrc {A plug_set: Set} {ft:foreign_type} {fdt:foreign_data_typing} {m:brand_model} (d: dnrc A plug_set) : string :=
    match d with
    | DNRCVar t n => n (* TODO might need an environment or something... *)
    | DNRCConst t c => scala_of_data m c
    | DNRCBinop t op x y =>
      scala_of_binop op (scala_of_dnrc x) (scala_of_dnrc y)
    | DNRCUnop t op x =>
      scala_of_unop op (scala_of_dnrc x)
    | DNRCLet t n x y => (* let n: t = x in y *) (* TODO might need braces, could use line break *)
      "val " ++ n ++ " = " ++ scala_of_dnrc x ++ "; " ++
             scala_of_dnrc y
    | DNRCFor t n x y => (* x.map((n: t) => y) *) (* TODO might not need braces, could use line breaks *)
      scala_of_dnrc x ++ ".map((" ++ n ++ ") => { " ++ scala_of_dnrc y ++ " })"
    | DNRCIf t x y z => (* if (x) y else z *) (* TODO might not need parentheses *)
      "(if (" ++ scala_of_dnrc x ++ ") " ++ scala_of_dnrc y ++ " else " ++ scala_of_dnrc z ++ ")"
    | DNRCEither t x vy y vz z =>
      (* TODO This will not work. We need to annotate the two lambdas with their input types. *)
      "either(" ++ scala_of_dnrc x ++ ", (" ++
                vy ++ "/*: TODO*/) => { " ++ scala_of_dnrc y ++ " }, (" ++
                vz ++ "/*: TODO*/) => { " ++ scala_of_dnrc z ++ "})"
    | DNRCCollect t x => scala_of_dnrc x ++ ".collect()"
    (* Dispatch is a bit tricky, because it requires the global SparkSession,
     * of which there can be only one, if I understand correctly.
     * It also requires the type, to construct the appropriate schema.
     * Last but not least, if the result of dispatch should always be a DataFrame (= Dataset[Row]),
     * then the element type has to be records, or we need to invent a column name. *)
    | DNRCDispatch t x => "DISPATCH???" (* TODO *)
    | DNRCAlg t a xs => "ALG???" (* TODO *)
    end.

  Definition populateBrandTypes {ft: foreign_type} {bm : brand_model} : string :=
    let elements :=
        map (fun p => "\""" ++ fst p ++ "\"" -> " ++ stype_to_datatype (rtype_to_stype (proj1_sig (snd p))))
            brand_context_types in
    "val BRAND_TYPES = Map(" ++ joinStrings ", " elements ++ ")".


  (** Toplevel entry to Spark2/Scala codegen *)

  Definition dnrcToSpark2Top {A : Set} {plug_set:Set} {ft:foreign_type} {fdt:foreign_data_typing} (m:brand_model) (name: string) (e: dnrc A plug_set) : string :=
    "object "
      ++ name ++ " extends org.qcert.QCertRuntime {" ++ eol
      ++ @populateBrandTypes ft m ++ eol
      ++ "val worldType = " ++ "test07InputType /* TODO replace by actual input type */" ++ eol
      ++ "def run(CONST$WORLD: org.apache.spark.sql.Dataset[org.apache.spark.sql.Row]) = {" ++ eol
      ++ "println(" ++ eol
      ++ scala_of_dnrc e ++ eol
      ++ ")" ++ eol
      ++ "}" ++ eol
      ++ "}".

End DNNRCtoScala.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
