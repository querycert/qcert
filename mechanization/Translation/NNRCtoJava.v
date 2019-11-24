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

Require Import List.
Require Import String.
Require Import Ascii.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCRuntime.
Require Import ForeignToJava.

Local Open Scope string_scope.

Section sanitizer.
  Import ListNotations.
  
  (* java allows identifiers that begin with a unicode letter or underscore.
         We avoid beginning with an underscore or dollar sign to 
         avoid problems with frameworks/libraries.
         Since Coq does not seem to have a unicode library, 
         we just allow ascii characters.
   *)

  Definition javaAllowedIdentifierInitialCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]%char.

  (* javascript identifiers can have (after the first character), a unicode letter, digit, underscore, or dollar sign.
         Since Coq does not seem to have a unicode library, we just
         allow ascii characters,
   *)
  Definition javaAllowedIdentifierCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_";"$"]%char.

  Definition javaIdentifierInitialCharacterToAdd := "X"%char.
  Definition javaIdenitiferCharacterForReplacement := "X"%char.

  Definition javaIdentifierFixInitial (ident:string) : string
    := match ident with
       (* We also don't want empty identifier names *)
       | EmptyString =>
         String javaIdentifierInitialCharacterToAdd EmptyString
       | String a _ =>
         if in_dec ascii_dec a javaAllowedIdentifierInitialCharacters
         then ident
         else String javaIdentifierInitialCharacterToAdd ident
       end.

  Definition javaIdentifierSanitizeChar (a:ascii)
    := if in_dec ascii_dec a javaAllowedIdentifierCharacters
       then a
       else javaIdenitiferCharacterForReplacement.

  Definition javaIdentifierSanitizeBody (ident:string)
    := map_string javaIdentifierSanitizeChar ident.
  
  Definition javaIdentifierSanitize (ident:string)
    := javaIdentifierFixInitial (javaIdentifierSanitizeBody ident).

  Definition javaSafeSeparator := "_".

  (* pulled of off various lists of javascript reserved keywords 
         as well some common html/java words that should be avoided
          in case of shared context/interop *)

  Definition javaAvoidList :=
    ["abstract"; "assert"; "boolean"; "break"; "byte"; "case"; "catch"; "char"; "class"; "const"; "continue"; "default"; "do"; "double"; "else"; "enum"; "extends"; "false"; "final"; "finally"; "float"; "for"; "goto"; "if"; "implements"; "import"; "instanceof"; "int"; "interface"; "long"; "native"; "new"; "null"; "package"; "private"; "protected"; "public"; "return"; "short"; "static"; "strictfp"; "super"; "switch"; "synchronized"; "this"; "throw"; "throws"; "transient"; "true"; "try"; "void"; "volatile"; "while"].

  Definition unshadow_java {fruntime:foreign_runtime} (avoid:list var) (e:nnrc) : nnrc
    := unshadow javaSafeSeparator javaIdentifierSanitize (avoid++javaAvoidList) e.

  Definition javaSanitizeNNRC {fruntime:foreign_runtime} (e:nnrc) : nnrc
    := unshadow_java nil e.

End sanitizer.

Section NNRCtoJava.

  Context {fruntime:foreign_runtime}.

  Section javaUtil.
    Definition eol_newline := String (Ascii.ascii_of_nat 10) EmptyString.
    Definition eol_backn := "\n".

    Definition quotel_double := """".
    Definition quotel_backdouble := "\""".
    
    Fixpoint indent (i : nat) : string
      := match i with
         | 0 => ""
         | S j => "  " ++ (indent j)
         end.

  End javaUtil.

  Section DataJava.
    Definition from_java_json (obj:java_json)
      := match obj with
         | mk_java_json s => s
         end.


    (* Given a list of strings that construct objects, create a JsonArray holding them *)
    Definition mk_java_json_array (l:list java_json) : java_json
       := mk_java_json ("RuntimeUtils.createJsonArray"
                          ++ bracketString "("
                          (map_concat ", " from_java_json l)
                          ")").
    
    Definition mk_java_json_object (quotel:string) (l:list (string*java_json)) : java_json
       := mk_java_json ("new RuntimeUtils.JsonObjectBuilder()" 
                          ++ (map_concat "" (fun elem =>
                                               bracketString
                                                 ".add("
                                                 (quotel ++ (fst elem) ++ quotel ++ ", " ++
                                                         (from_java_json (snd elem)))
                                                 ")") l)
            ++ ".toJsonObject()").
               
    Definition mk_java_json_primitive (obj:string) : java_json
      := mk_java_json ("new JsonPrimitive(" ++ obj ++ ")").
    
    Definition mk_java_json_string quotel (s:string)
      := mk_java_json_primitive
           (bracketString quotel s quotel).    

    Definition mk_java_json_brands (quotel:string) (b:brands) : java_json
      := mk_java_json_array (map (mk_java_json_string quotel) b).

    Definition java_json_NULL : java_json
       := mk_java_json "JsonNull.INSTANCE".
 
    Import ListNotations.

     Definition mk_java_json_nat quotel n : java_json
       := mk_java_json_object quotel
                              [("$nat", (mk_java_json_primitive (Z_to_string10 n)))].
     
     Definition mk_java_json_number n : java_json
       := mk_java_json_primitive (float_to_string n).
     
     Definition mk_java_json_bool (b:bool) : java_json
       := mk_java_json_primitive 
            (if b then "true" else "false").

    Context {ftojavajson:foreign_to_java}.

    Fixpoint mk_java_json_data (quotel:string) (d : data) : java_json
      := match d with
         | dunit => java_json_NULL
         | dnat n => mk_java_json_nat quotel n
         | dfloat n => mk_java_json_number n
         | dbool b => mk_java_json_bool b
         | dstring s => mk_java_json_string quotel s
         | dcoll ls => mk_java_json_array (map (mk_java_json_data quotel) ls)
         | drec ls => mk_java_json_object quotel
                        (map (fun kv =>
                                let '(k,v) := kv in
                                (k, (mk_java_json_data quotel v))) ls)
         | dleft d => mk_java_json_object quotel
                                         [("$left", (mk_java_json_data quotel d))]

         | dright d => mk_java_json_object quotel
                                         [("$right", (mk_java_json_data quotel d))]

         | dbrand b d =>
           mk_java_json_object quotel
                              [("$data", mk_java_json_data quotel d)
                               ; ("$type", mk_java_json_brands quotel b)]
         | dforeign fd => foreign_to_java_data quotel fd
         end.

  End DataJava.


  Section test.
    Import ListNotations.
    
    Definition testd
      := drec (rec_sort [
                   ("hi", dcoll [dnat 3; dnat 4])
                   ; ("there", dbool false)
                   ; ("is", dstring "hi")
                   ; ("b", dbrand ["C1"; "I1"; "C2"]
                                  (dcoll [dbool true; dbool false]))]).
    Context {ftojavajson:foreign_to_java}.
    
    (* Eval vm_compute in mk_java_json_data quotel_double testd. *)
    
  End test.

  Section NNRCJava.
    Context {ftojavajson:foreign_to_java}.

    Definition mk_java_string (s:string) : string
      := quotel_double ++ s ++ quotel_double.

    Definition mk_java_unary_op0 (opname:string) (e:java_json) : java_json
      := mk_java_json ("UnaryOperators." ++ opname ++ "(" ++ (from_java_json e) ++ ")").

    Definition mk_java_unary_op1 (opname:string) (s:string) (e:java_json) : java_json
      := mk_java_json
           ("UnaryOperators."
              ++ opname
              ++ "("
              ++ s ++ ", "
              ++ (from_java_json e) ++ ")").

    Import ListNotations.
    Definition mk_java_unary_opn (opname:string) (sn:list string) (e:java_json) : java_json
      := mk_java_json
           ("UnaryOperators."
              ++ opname
              ++ "("
              ++ (concat ", " (List.app sn [(from_java_json e)]))
              ++ ")").

    Definition mk_java_collection(typ:string) (s:list string) : string
      := "new RuntimeUtils.CollectionBuilder<" ++ typ ++ ">("
           ++ (nat_to_string10 (Datatypes.length s)) ++ ")"
           ++ map_concat "" (fun elem => ".add(" ++ elem ++ ")") s
           ++ ".result()".

    Definition mk_java_string_collection(s:list string) : string
      := mk_java_collection "String" (map mk_java_string s).
    
    Definition mk_java_binary_op0 (opname:string) (e1 e2:java_json) : java_json
      := mk_java_json ("BinaryOperators." ++ opname ++ "(" ++ (from_java_json e1) ++ ", " ++ (from_java_json e2) ++ ")").

    Definition uarithToJavaMethod (u:nat_arith_unary_op) :=
      match u with
      | NatAbs => "abs"
      | NatLog2 => "log2"
      | NatSqrt =>"sqrt"
      end.

    Definition float_uarithToJavaMethod (fu:float_arith_unary_op) :=
      match fu with
      | FloatNeg => "float_neg"
      | FloatSqrt => "float_sqrt"
      | FloatExp => "float_exp"
      | FloatLog => "float_log"
      | FloatLog10 => "float_log10"
      | FloatCeil => "float_ceil"
      | FloatFloor => "float_floor"
      | FloatAbs => "float_abs"
      end.

    Definition nat_barithToJavaMethod (b:nat_arith_binary_op)  :=
      match b with
      | NatPlus => "plus"
      | NatMinus => "minus "
      | NatMult => "mult"
      | NatDiv => "divide"
      | NatRem => "rem"
      | NatMin => "min"
      | NatMax => "max"
      end.

    Definition float_barithToJavaMethod (fb:float_arith_binary_op)
      := match fb with
         | FloatPlus => "float_plus"
         | FloatMinus => "float_minus"
         | FloatMult => "float_mult"
         | FloatDiv => "float_divide"
         | FloatPow => "float_pow"
         | FloatMin => "float_min"
         | FloatMax => "float_max"
         end.

    Definition float_bcompareToJavaMethod (fb:float_compare_binary_op)
      := match fb with
         | FloatLt => "float_lt"
         | FloatLe => "float_le"
         | FloatGt => "float_gt"
         | FloatGe => "float_ge"
         end.

    Definition like_clause_to_java (lc:like_clause)
      := match lc with
         | like_literal literal => "new UnaryOperator.LiteralLikeClause(" ++ (mk_java_string literal) ++ ")"
         | like_any_char => "new UnaryOperator.AnyCharLikeClause()"
         | like_any_string => "new UnaryOperator.AnyStringLikeClause()"
         end.
    
    Fixpoint nnrcToJava
             (n : nnrc)                    (* NNRC expression to translate *)
             (t : nat)                    (* next available unused temporary *)
             (i : nat)                    (* indentation level *)
             (eol : string)               (* Choice of end of line character *)
             (quotel : string)            (* Choice of quote character *)
             (ivs : list (string * string))  (* Input variables and their corresponding string representation -- should be free in the nnrc expression *)
      : string                            (* JavaScript statements for computing result *)
        * java_json                          (* JavaScript expression holding result *)
        * nat                             (* next available unused temporary *)
      := match n with
         | NNRCGetConstant v =>
           ("", mk_java_json ("v" ++ v), t)
         | NNRCVar v =>
           match assoc_lookupr equiv_dec ivs v with
           | Some v_string => ("", mk_java_json v_string, t)
           | None => ("", mk_java_json ("v" ++ v), t)
           end
         | NNRCConst d => ("", (mk_java_json_data quotel d), t)
         | NNRCUnop op n1 =>
           let '(s1, e1, t0) := nnrcToJava n1 t i eol quotel ivs in
           let e0 := match op with
                     | OpIdentity => e1
                     | OpNeg => mk_java_unary_op0 "neg" e1
                     | OpRec s => mk_java_unary_op1 "rec" (mk_java_string s) e1
                     | OpDot s => mk_java_unary_op1 "dot" (mk_java_string s) e1
                     | OpRecRemove s => mk_java_unary_op1 "remove"  (mk_java_string s) e1
                     | OpRecProject sl => mk_java_unary_op1 "project" (mk_java_string_collection sl) e1
                     | OpBag => mk_java_unary_op0 "coll" e1
                     | OpSingleton => mk_java_unary_op0 "singleton" e1
                     | OpFlatten => mk_java_unary_op0 "flatten" e1
                     | OpDistinct => mk_java_unary_op0 "distinct" e1
                     | OpOrderBy sl => mk_java_unary_op1 "sort" (mk_java_string_collection (List.map fst sl)) e1 (* XXX TO FIX XXX *)
                     | OpCount => mk_java_unary_op0 "count" e1
                     | OpToString =>  mk_java_unary_op0 "tostring" e1
                     | OpToText =>  mk_java_unary_op0 "totext" e1
                     | OpLength =>  mk_java_unary_op0 "stringlength" e1
                     | OpSubstring start olen =>
                       match olen with
                       | Some len => mk_java_unary_opn "substring" (map toString [start; len]) e1
                       | None => mk_java_unary_op1 "substring" (toString start) e1
                       end
                     | OpLike pat oescape =>
                       let lc := make_like_clause pat oescape in
                       mk_java_unary_op1 "string_like" ("new LikeClause[]{" ++ (map_concat "," like_clause_to_java lc) ++ "}") e1
                     | OpLeft => mk_java_unary_op0 "left" e1
                     | OpRight => mk_java_unary_op0 "right" e1
                     | OpBrand b =>mk_java_unary_op1 "brand" (mk_java_string_collection b) e1
                     | OpUnbrand => mk_java_unary_op0 "unbrand" e1
                     | OpCast b => mk_java_unary_opn "cast" ["inheritance"; (mk_java_string_collection b)] e1
                     | OpNatUnary u => mk_java_unary_op0 (uarithToJavaMethod u) e1
                     | OpNatSum =>  mk_java_unary_op0 "sum" e1
                     | OpNatMin => mk_java_unary_op0 "list_min" e1
                     | OpNatMax =>  mk_java_unary_op0 "list_max" e1
                     | OpNatMean => mk_java_unary_op0 "list_mean" e1
                     | OpFloatOfNat => mk_java_unary_op0 "float_of_int" e1
                     | OpFloatUnary u => mk_java_unary_op0 (float_uarithToJavaMethod u) e1
                     | OpFloatTruncate => mk_java_unary_op0 "float_truncate" e1
                     | OpFloatSum =>  mk_java_unary_op0 "float_sum" e1
                     | OpFloatBagMin => mk_java_unary_op0 "float_list_min" e1
                     | OpFloatBagMax =>  mk_java_unary_op0 "float_list_max" e1
                     | OpFloatMean => mk_java_unary_op0 "float_list_mean" e1
                     | OpForeignUnary fu
                       => foreign_to_java_unary_op i eol quotel fu e1
                     end in
           (s1, e0, t0)
         | NNRCBinop op n1 n2 =>
           let '(s1, e1, t2) := nnrcToJava n1 t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJava n2 t2 i eol quotel ivs in
           let e0 := match op with
                     | OpEqual => mk_java_binary_op0 "equals" e1 e2
                     | OpRecConcat => mk_java_binary_op0 "concat" e1 e2
                     | OpRecMerge => mk_java_binary_op0 "mergeConcat" e1 e2
                     | OpAnd => mk_java_binary_op0 "and" e1 e2
                     | OpOr => mk_java_binary_op0 "or" e1 e2
                     | OpLt =>  mk_java_binary_op0 "lt" e1 e2
                     | OpLe =>  mk_java_binary_op0 "le" e1 e2
                     | OpBagUnion => mk_java_binary_op0 "union" e1 e2
                     | OpBagDiff =>  mk_java_binary_op0 "bag_minus" e1 e2
                     | OpBagMin =>  mk_java_binary_op0 "bag_min" e1 e2
                     | OpBagMax =>  mk_java_binary_op0 "bag_max" e1 e2
                     | OpBagNth =>  mk_java_binary_op0 "bag_nth" e1 e2
                     | OpContains =>  mk_java_binary_op0 "contains" e1 e2
                     | OpStringConcat => mk_java_binary_op0 "stringConcat" e1 e2
                     | OpStringJoin => mk_java_binary_op0 "stringJoin" e1 e2
                     | OpNatBinary b => mk_java_binary_op0 (nat_barithToJavaMethod b) e1 e2
                     | OpFloatBinary b => mk_java_binary_op0 (float_barithToJavaMethod b) e1 e2
                     | OpFloatCompare b => mk_java_binary_op0 (float_bcompareToJavaMethod b) e1 e2
                     | OpForeignBinary fb
                       => foreign_to_java_binary_op i eol quotel fb e1 e2
                     end in
           (s1 ++ s2, e0, t0)
         | NNRCLet v bind body =>
           let '(s1, e1, t2) := nnrcToJava bind t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJava body t2 i eol quotel ivs in
           let v0 := "v" ++ v in
           let ret := "vletvar$" ++ v ++ "$" ++ (nat_to_string10 t0) in
           (s1
              ++ (indent i) ++ "final JsonElement " ++ ret ++ ";" ++ eol
              ++ (indent i) ++ "{ // new scope introduced for a let statement" ++ eol
              ++ (indent (i+1)) ++ "final JsonElement " ++ v0 ++ " = " ++ (from_java_json e1) ++ ";" ++ eol
              ++ s2
              ++ (indent (i+1)) ++ ret ++ " = " ++ (from_java_json e2) ++ ";" ++ eol
              ++ (indent i) ++ "}" ++ eol,
            mk_java_json ret, t0+1)
         | NNRCFor v iter body =>
           let '(s1, e1, t2) := nnrcToJava iter t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJava body t2 (i+1) eol quotel ivs in
           let elm := "v" ++ v in
           let src := "src" ++ (nat_to_string10 t0) in
           let idx := "i" ++ (nat_to_string10 t0) in
           let dst := "dst" ++ (nat_to_string10 t0) in
           (s1 ++ (indent i) ++ "final JsonArray " ++ src ++ " = (JsonArray) " ++ (from_java_json e1) ++ ";" ++ eol
               ++ (indent i) ++ "final JsonArray " ++ dst ++ " = new JsonArray();" ++ eol
               ++ (indent i) ++ "for(int " ++ idx ++ " = 0; " ++ idx ++ " < " ++ src ++ ".size(); " ++ idx ++ "++) {" ++ eol
               ++ (indent (i+1)) ++ "final JsonElement " ++ elm ++ " = " ++ src ++ ".get(" ++ idx ++ ");" ++ eol
               ++ s2
               ++ (indent (i+1)) ++ dst ++ ".add(" ++ (from_java_json e2) ++ ");" ++ eol
               ++ (indent i) ++ "}" ++ eol,
            (mk_java_json dst), t0 + 1)
         | NNRCIf c n1 n2 =>
           let '(s1, e1, t2) := nnrcToJava c t i eol quotel ivs in
           let '(s2, e2, t3) := nnrcToJava n1 t2 (i+1) eol quotel ivs in
           let '(s3, e3, t0) := nnrcToJava n2 t3 (i+1) eol quotel ivs in
           let v0 := "t" ++ (nat_to_string10 t0) in
           (s1 ++ (indent i) ++ "final JsonElement " ++ v0 ++ ";" ++ eol
               ++ (indent i) ++ "if (RuntimeUtils.asBoolean(" ++ (from_java_json e1) ++ ")) {" ++ eol
               ++ s2
               ++ (indent (i+1)) ++ v0 ++ " = " ++ (from_java_json e2) ++ ";" ++ eol
               ++ (indent i) ++ "} else {" ++ eol
               ++ s3
               ++ (indent (i+1)) ++ v0 ++ " = " ++ (from_java_json e3) ++ ";" ++ eol
               ++ (indent i) ++ "}" ++ eol,
            (mk_java_json v0), t0 + 1)
         | NNRCEither nd xl nl xr nr =>
           let '(s1, e1, t2) := nnrcToJava nd t i eol quotel ivs in
           let '(s2, e2, t1) := nnrcToJava nl t2 (i+1) eol quotel ivs in
           let '(s3, e3, t0) := nnrcToJava nr t1 (i+1) eol quotel ivs in
           let vl := "v" ++ xl in
           let vr := "v" ++ xr in
           let res := "res" ++ (nat_to_string10 t0) in  (* Stores the result from either left or right evaluation so it can be returned *)
           (s1 ++ (indent i) ++ "final JsonElement " ++ res ++ ";" ++ eol
               ++ (indent i) ++ "if (RuntimeUtils.either(" ++ (from_java_json e1) ++ ")) {" ++ eol
               ++ (indent (i+1)) ++ "final JsonElement " ++ vl ++ eol
               ++ (indent (i+1)) ++ " = RuntimeUtils.toLeft(" ++ (from_java_json e1) ++ ");" ++ eol
               ++ s2
               ++ (indent (i+1)) ++ res ++ " = " ++ (from_java_json e2) ++ ";" ++ eol
               ++ (indent i) ++ "} else {" ++ eol
               ++ (indent (i+1)) ++ "final JsonElement " ++ vr  ++ eol
               ++ (indent (i+1)) ++ " = RuntimeUtils.toRight(" ++ (from_java_json e1) ++ ");" ++ eol
               ++ s3
               ++ (indent (i+1)) ++ res ++ " = " ++ (from_java_json e3) ++ ";" ++ eol
               ++ (indent i) ++ "}" ++ eol,
            mk_java_json res, t0 + 1)
         | NNRCGroupBy g sl n1 =>
           let '(s1, e1, t0) := nnrcToJava n1 t i eol quotel ivs in
           let e0 := mk_java_unary_opn "groupby" [(mk_java_string g);(mk_java_string_collection sl)] e1 in
           (s1, e0, t0)
       end.

    Definition nnrcToJavaunshadow (n : nnrc) (t : nat) (i : nat) (eol : string) (quotel : string) (avoid: list var) (ivs : list (string * string)) :=
      let n := unshadow_java avoid n in
      nnrcToJava n t i eol quotel ivs.

    Definition makeJavaParams (ivs: list(string*string)) :=
      map_concat ", " (fun elem => "JsonElement " ++ snd elem) ivs.

    (* Free variables are assumed to be constant lookups *)
    Definition closeFreeVars (input:string) (e:nnrc) (ivs:list(string*string)) : nnrc :=
      let all_free_vars := nnrc_global_vars e in
      let wrap_one_free_var (e':nnrc) (fv:string) : nnrc :=
          if (assoc_lookupr equiv_dec ivs fv)
          then e'
          else
            (NNRCLet fv (NNRCUnop (OpDot fv) (NNRCVar input)) e')
      in
      fold_left wrap_one_free_var all_free_vars e.
    
    Definition nnrcToJavaFun (i:nat) (input_v:string) (e:nnrc) (eol:string) (quotel:string) (ivs : list (string * string)) (fname:string) :=
      let e' := closeFreeVars input_v e ivs in
      let '(j0, v0, t0) := nnrcToJavaunshadow e' 1 (i + 1) eol quotel ("constants"::"inheritance"::(List.map fst ivs)) ivs in
      (indent i) ++ "public JsonElement " ++ fname ++ "(Inheritance inheritance, "++ (makeJavaParams ivs) ++ ") {" ++ eol
                 ++ j0
                 ++ (indent i) ++ "  return " ++ (from_java_json v0) ++ ";" ++ eol
                 ++ (indent i) ++ "}" ++ eol.

    Definition nnrcToJavaClass (class_name:string) (package_name:string) (imports:string) (input_v:string) (e:nnrc) (eol:string) (quotel:string) (ivs : list (string * string)) (fname:string) :=
      let f := nnrcToJavaFun 1 input_v e eol quotel ivs fname in
      (if(package_name == "")
      then ""
      else "package " ++ package_name ++ ";" ++ eol ++ eol)
        ++ "import com.google.gson.*;" ++ eol
        ++ (if(imports == "")
            then ""
            else "import " ++ imports ++ ";" ++ eol)
        ++ (if(package_name == "org.qcert.runtime")
            then ""
            else "import org.qcert.runtime.*;" ++ eol)
      ++ eol
      ++ "public class " ++ class_name ++ " implements JavaQuery { " ++ eol
      ++ f
      ++ "}" ++ eol
    .

    Definition nnrc_to_java_top (class_name:string) (imports:string) (e:nnrc) : string :=
      let input_f := "query" in
      let input_v := "constants" in
      nnrcToJavaClass class_name "" imports input_v e eol_newline quotel_double ((input_v, input_v)::nil) input_f.

  End NNRCJava.

End NNRCtoJava.

