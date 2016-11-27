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

Require Import Utils BasicRuntime.
Require Import NNRCRuntime ForeignToJava.
Local Open Scope string_scope.


Section sanitizer.
  Import ListNotations.
  Require Import Ascii.
  
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

  Definition unshadow_java {fruntime:foreign_runtime} (avoid:list var) (e:nrc) : nrc
    := unshadow javaSafeSeparator javaIdentifierSanitize (avoid++javaAvoidList) e.

  Definition javaSanitizeNNRC {fruntime:foreign_runtime} (e:nrc) : nrc
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

    (* Given a list of strings that construct objects, create a JsonArray holding them *)
    Definition mk_java_json_array (l:list java_json) : java_json
       := mk_java_json ("RuntimeUtils.createJsonArray"
                          ++ bracketString "("
                          (joinStrings ", " (map from_java_json l))
                          ")").
    
    Definition mk_java_json_object (quotel:string) (l:list (string*java_json)) : java_json
       := mk_java_json ("new RuntimeUtils.JsonObjectBuilder()" 
            ++ (joinStrings "" (map (fun elem =>
                                       bracketString
                                         ".add("
                                         (quotel ++ (fst elem) ++ quotel ++ ", " ++
                                                 (from_java_json (snd elem)))
                                         ")") l))
            ++ ".toJsonObject()").
               
    Definition mk_java_json_brands (quotel:string) (b:brands) : java_json
      := mk_java_json_array (map (mk_java_json_string quotel) b).

    Import ListNotations.

    Context {ftojavajson:foreign_to_java}.

    Fixpoint mk_java_json_data (quotel:string) (d : data) : java_json
      := match d with
         | dunit => java_json_NULL
         | dnat n => mk_java_json_nat n
         | dbool b => mk_java_json_bool b
         | dstring s => mk_java_json_string quotel s
         | dcoll ls => mk_java_json_array (map (mk_java_json_data quotel) ls)
         | drec ls => mk_java_json_object quotel
                        (map (fun kv =>
                                let '(k,v) := kv in
                                (k, (mk_java_json_data quotel v))) ls)
         | dleft d => mk_java_json_object quotel
                                         [("left", (mk_java_json_data quotel d))]

         | dright d => mk_java_json_object quotel
                                         [("right", (mk_java_json_data quotel d))]

         | dbrand b d =>
           mk_java_json_object quotel
                              [("data", mk_java_json_data quotel d)
                               ; ("type", mk_java_json_brands quotel b)]
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

  Section NRCJava.
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
              ++ (joinStrings ", " (List.app sn [(from_java_json e)]))
              ++ ")").

    Definition mk_java_collection(typ:string) (s:list string) : string
      := "new RuntimeUtils.CollectionBuilder<" ++ typ ++ ">("
           ++ (nat_to_string10 (Datatypes.length s)) ++ ")"
           ++ joinStrings "" (map (fun elem => ".add(" ++ elem ++ ")") s)
           ++ ".result()".

    Definition mk_java_string_collection(s:list string) : string
      := mk_java_collection "String" (map mk_java_string s).
    
    Definition mk_java_binary_op0 (opname:string) (e1 e2:java_json) : java_json
      := mk_java_json ("BinaryOperators." ++ opname ++ "(" ++ (from_java_json e1) ++ ", " ++ (from_java_json e2) ++ ")").

    Definition uarithToJavaMethod (u:ArithUOp) :=
      match u with
      | ArithAbs => "abs"
      | ArithLog2 => "log2"
      | ArithSqrt =>"sqrt"
      end.

    Definition barithToJavaMethod (b:ArithBOp)  :=
      match b with
      | ArithPlus => "plus"
      | ArithMinus => "minus "
      | ArithMult => "mult"
      | ArithDivide => "divide"
      | ArithRem => "rem"
      | ArithMin => "min"
      | ArithMax => "max"
      end.


    Definition like_clause_to_java (lc:like_clause)
      := match lc with
         | like_literal literal => "new UnaryOperator.LiteralLikeClause(" ++ (mk_java_string literal) ++ ")"
         | like_any_char => "new UnaryOperator.AnyCharLikeClause()"
         | like_any_string => "new UnaryOperator.AnyStringLikeClause()"
         end.
    
    Fixpoint nrcToJava
             (n : nrc)                    (* NNRC expression to translate *)
             (t : nat)                    (* next available unused temporary *)
             (i : nat)                    (* indentation level *)
             (eol : string)               (* Choice of end of line character *)
             (quotel : string)            (* Choice of quote character *)
             (ivs : list (string * string))  (* Input variables and their corresponding string representation -- should be free in the nrc expression *)
      : string                            (* JavaScript statements for computing result *)
        * java_json                          (* JavaScript expression holding result *)
        * nat                             (* next available unused temporary *)
      := match n with
         | NRCVar v =>
           match assoc_lookupr equiv_dec ivs v with
           | Some v_string => ("", mk_java_json v_string, t)
           | None => ("", mk_java_json ("v" ++ v), t)
           end
         | NRCConst d => ("", (mk_java_json_data quotel d), t)
         | NRCUnop op n1 =>
           let '(s1, e1, t0) := nrcToJava n1 t i eol quotel ivs in
           let e0 := match op with
                     | AIdOp => e1
                     | AUArith u => mk_java_unary_op0 (uarithToJavaMethod u) e1
                     | ANeg => mk_java_unary_op0 "neg" e1
                     | AColl => mk_java_unary_op0 "coll" e1
                     | ACount => mk_java_unary_op0 "count" e1
                     | AFlatten => mk_java_unary_op0 "flatten" e1
                     | ARec s => mk_java_unary_op1 "rec" (mk_java_string s) e1
                     | ADot s => mk_java_unary_op1 "dot" (mk_java_string s) e1
                     | ARecRemove s => mk_java_unary_op1 "remove"  (mk_java_string s) e1
                     | ARecProject sl => mk_java_unary_op1 "project" (mk_java_string_collection sl) e1
                     | ADistinct => mk_java_unary_op0 "distinct" e1
                     | AOrderBy sl => mk_java_unary_op1 "sort" (mk_java_string_collection (List.map fst sl)) e1 (* XXX TO FIX XXX *)
                     | ASum =>  mk_java_unary_op0 "sum" e1
                     | AArithMean => mk_java_unary_op0 "list_mean" e1
                     | AToString =>  mk_java_unary_op0 "tostring" e1
                     | ASubstring start olen =>
                       match olen with
                       | Some len => mk_java_unary_opn "substring" (map toString [start; len]) e1
                       | None => mk_java_unary_op1 "substring" (toString start) e1
                       end
                     | ALike pat oescape =>
                       let lc := make_like_clause pat oescape in
                       mk_java_unary_op1 "string_like" ("new LikeClause[]{" ++ (joinStrings "," (map like_clause_to_java lc)) ++ "}") e1
                     | ALeft => mk_java_unary_op0 "left" e1
                     | ARight => mk_java_unary_op0 "right" e1
                     | ABrand b =>mk_java_unary_op1 "brand" (mk_java_string_collection b) e1
                     | AUnbrand => mk_java_unary_op0 "unbrand" e1
                     | ACast b => mk_java_unary_opn "cast" ["hierarchy"; (mk_java_string_collection b)] e1
                     | ASingleton => mk_java_unary_op0 "singleton" e1
                     | ANumMin => mk_java_unary_op0 "list_min" e1
                     | ANumMax =>  mk_java_unary_op0 "list_max" e1
                     | AForeignUnaryOp fu
                       => foreign_to_java_unary_op i eol quotel fu e1
                     end in
           (s1, e0, t0)
         | NRCBinop op n1 n2 =>
           let '(s1, e1, t2) := nrcToJava n1 t i eol quotel ivs in
           let '(s2, e2, t0) := nrcToJava n2 t2 i eol quotel ivs in
           let e0 := match op with
                     | ABArith b => mk_java_binary_op0 (barithToJavaMethod b) e1 e2
                     | AEq => mk_java_binary_op0 "equals" e1 e2
                     | AUnion => mk_java_binary_op0 "union" e1 e2
                     | AConcat => mk_java_binary_op0 "concat" e1 e2
                     | AMergeConcat => mk_java_binary_op0 "mergeConcat" e1 e2
                     | AAnd => mk_java_binary_op0 "and" e1 e2
                     | AOr => mk_java_binary_op0 "or" e1 e2
                     | ALt =>  mk_java_binary_op0 "lt" e1 e2
                     | ALe =>  mk_java_binary_op0 "le" e1 e2
                     | AMinus =>  mk_java_binary_op0 "bag_minus" e1 e2
                     | AMin =>  mk_java_binary_op0 "bag_min" e1 e2
                     | AMax =>  mk_java_binary_op0 "bag_max" e1 e2
                     | AContains =>  mk_java_binary_op0 "contains" e1 e2
                     | ASConcat => mk_java_binary_op0 "stringConcat" e1 e2
                     | AForeignBinaryOp fb
                       => foreign_to_java_binary_op i eol quotel fb e1 e2
                     end in
           (s1 ++ s2, e0, t0)
         | NRCLet v bind body =>
           let '(s1, e1, t2) := nrcToJava bind t i eol quotel ivs in
           let '(s2, e2, t0) := nrcToJava body t2 i eol quotel ivs in
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
         | NRCFor v iter body =>
           let '(s1, e1, t2) := nrcToJava iter t i eol quotel ivs in
           let '(s2, e2, t0) := nrcToJava body t2 (i+1) eol quotel ivs in
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
         | NRCIf c n1 n2 =>
           let '(s1, e1, t2) := nrcToJava c t i eol quotel ivs in
           let '(s2, e2, t3) := nrcToJava n1 t2 (i+1) eol quotel ivs in
           let '(s3, e3, t0) := nrcToJava n2 t3 (i+1) eol quotel ivs in
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
         | NRCEither nd xl nl xr nr =>
           let '(s1, e1, t2) := nrcToJava nd t i eol quotel ivs in
           let '(s2, e2, t1) := nrcToJava nl t2 (i+1) eol quotel ivs in
           let '(s3, e3, t0) := nrcToJava nr t1 (i+1) eol quotel ivs in
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
       end.

    Definition nrcToJavaunshadow (n : nrc) (t : nat) (i : nat) (eol : string) (quotel : string) (avoid: list var) (ivs : list (string * string)) :=
      let n := unshadow_java avoid n in
      nrcToJava n t i eol quotel ivs.

    Definition makeJavaParams (ivs: list(string*string)) :=
      joinStrings ", " (map (fun elem => "JsonElement " ++ snd elem) ivs).

    (* Free variables are assumed to be constant lookups *)
    Require Import NShadow.
    Definition closeFreeVars (input:string) (e:nrc) (ivs:list(string*string)) : nrc :=
      let all_free_vars := nrc_free_vars e in
      let wrap_one_free_var (e':nrc) (fv:string) : nrc :=
          if (assoc_lookupr equiv_dec ivs fv)
          then e'
          else (NRCLet fv (NRCUnop (ADot fv) (NRCVar input)) e')
      in
      fold_left wrap_one_free_var all_free_vars e.
    
    Definition nrcToJavaFun (i:nat) (input_v:string) (e:nrc) (eol:string) (quotel:string) (ivs : list (string * string)) (fname:string) :=
      let e' := closeFreeVars input_v e ivs in
      let '(j0, v0, t0) := nrcToJavaunshadow e' 1 (i + 1) eol quotel ("constants"::"hierarchy"::(List.map fst ivs)) ivs in
      (indent i) ++ "public JsonElement " ++ fname ++ "(Hierarchy hierarchy, "++ (makeJavaParams ivs) ++ ") {" ++ eol
                 ++ j0
                 ++ (indent i) ++ "  return " ++ (from_java_json v0) ++ ";" ++ eol
                 ++ (indent i) ++ "}" ++ eol.

    Definition nrcToJavaClass (class_name:string) (package_name:string) (imports:string) (input_v:string) (e:nrc) (eol:string) (quotel:string) (ivs : list (string * string)) (fname:string) :=
      let f := nrcToJavaFun 1 input_v e eol quotel ivs fname in
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

    Definition nrcToJavaTop (class_name:string) (imports:string) (e:nrc) : string :=
      let input_f := "query" in
      let input_v := "constants" in
      nrcToJavaClass class_name "" imports input_v e eol_newline quotel_double ((input_v, input_v)::nil) input_f.

  End NRCJava.

End NNRCtoJava.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
