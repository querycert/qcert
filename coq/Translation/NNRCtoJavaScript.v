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
Require Import Peano_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCRuntime.
Require Import JavaScriptRuntime.
Require Import ForeignToJavaScript.

Local Open Scope string_scope.

Section sanitizer.
  Import ListNotations.
  Require Import Ascii.
  
  (* javascript allows identifiers that begin with a unicode letter, underscore, or dollar sign.
         We avoid beginning with an underscore or dollar sign to 
         avoid problems with frameworks/libraries.
         Since Coq does not seem to have a unicode library, 
         we just allow ascii characters.
   *)

  Definition jsAllowedIdentifierInitialCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]%char.

  (* javascript identifiers can have (after the first character), a unicode letter, digit, underscore, or dollar sign.
         Since Coq does not seem to have a unicode library, we just
         allow ascii characters,
   *)
  Definition jsAllowedIdentifierCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_";"$"]%char.

  Definition jsIdentifierInitialCharacterToAdd := "X"%char.
  Definition jsIdenitiferCharacterForReplacement := "X"%char.

  Definition jsIdentifierFixInitial (ident:string) : string
    := match ident with
       (* We also don't want empty identifier names *)
       | EmptyString =>
         String jsIdentifierInitialCharacterToAdd EmptyString
       | String a _ =>
         if in_dec ascii_dec a jsAllowedIdentifierInitialCharacters
         then ident
         else String jsIdentifierInitialCharacterToAdd ident
       end.

  Definition jsIdentifierSanitizeChar (a:ascii)
    := if in_dec ascii_dec a jsAllowedIdentifierCharacters
       then a
       else jsIdenitiferCharacterForReplacement.

  Definition jsIdentifierSanitizeBody (ident:string)
    := map_string jsIdentifierSanitizeChar ident.

  (* Java equivalent: JavaScriptBackend.jsIdentifierSanitize *)  
  Definition jsIdentifierSanitize (ident:string)
    := jsIdentifierFixInitial (jsIdentifierSanitizeBody ident).

  Definition jsSafeSeparator := "_".

  (* pulled of off various lists of javascript reserved keywords 
         as well some common html/java words that should be avoided
          in case of shared context/interop *)
  Definition jsAvoidList :=
    ["Array"; "Date"; "Infinity"; "JavaArray"; "JavaObject"; "JavaPackage"
     ; "Math"; "NaN"; "Number"; "Object"; "String"
     ; "abstract"; "alert" ; "all"; "anchor"; "anchors"; "area"; "arguments"
     ; "assign"; "await"
     ; "blur"; "boolean"; "break"; "button"; "byte"
     ; "case"; "catch"; "char"; "checkbox"; "class"; "clearInterval"
     ; "clearTimeout"; "clientInformation"; "close"; "closed"; "confirm"
     ; "const"; "constructor"; "continue"; "crypto"
     ; "debugger"; "decodeURI"; "decodeURIComponent"; "default"
     ; "defaultStatus"; "delete"; "do"; "document"; "double"
     ; "element"; "elements"; "else"; "embed"; "embeds"; "encodeURI"
     ; "encodeURIComponent"; "enum"; "escape"; "eval"; "eval"; "event"
     ; "export"; "extends"
     ; "false"; "fileUpload"; "final"; "finally"; "float"; "focus"; "for"
     ; "form"; "forms"; "frame"; "frameRate"; "frames"; "function"; "function"
     ; "getClass"; "goto"
     ; "hasOwnProperty"; "hidden"; "history"
     ; "if"; "image"; "images"; "implements"; "import"; "in"; "innerHeight"
     ; "innerWidth"; "instanceof"; "int"; "interface"; "isFinite"; "isNaN"
     ; "isPrototypeOf"
     ; "java"; "javaClass"
     ; "layer"; "layers"; "length"; "let"; "link"; "location"; "long"
     ; "mimeTypes"
     ; "name"; "native"; "navigate"; "navigator"; "new"; "null"
     ; "offscreenBuffering"; "open"; "opener"; "option"; "outerHeight"
     ; "outerWidth"
     ; "package"; "packages"; "pageXOffset"; "pageYOffset"; "parent"
     ; "parseFloat"; "parseInt"; "password"; "pkcs11"; "plugin"; "private"
     ; "prompt"; "propertyIsEnum"; "protected"; "prototype"; "public"
     ; "radio"; "reset"; "return"
     ; "screenX"; "screenY"; "scroll"; "secure"; "select"; "self"
     ; "setInterval"; "setTimeout"; "short"; "static"; "status"
     ; "submit"; "super"; "switch"; "synchronized"
     ; "taint"; "text"; "textarea"; "this"; "throw"; "throws"; "toString"
     ; "top"; "transient"; "true"; "try"; "typeof"
     ; "undefined"; "unescape"; "untaint"
     ; "valueOf"; "var"; "void"; "volatile"
     ; "while"; "window"; "with"
     ; "yield"].

  (* Java equivalent: JavaScriptBackend.unshadow_js *)
  Definition unshadow_js {fruntime:foreign_runtime} (avoid:list var) (e:nnrc) : nnrc
    := unshadow jsSafeSeparator jsIdentifierSanitize (avoid++jsAvoidList) e.

  Definition jsSanitizeNNRC {fruntime:foreign_runtime} (e:nnrc) : nnrc
    := unshadow_js nil e.

End sanitizer.

Section NNRCtoJavaScript.

  Context {fruntime:foreign_runtime}.
  Context {ftojavascript:foreign_to_javascript}.
  Context {ftjson:foreign_to_JSON}.

  Definition varvalue := 100.
  Definition varenv := 1.

  Section JSUtil.
    Definition eol_newline := String (Ascii.ascii_of_nat 10) EmptyString.
    Definition eol_backn := "\n".

    Definition quotel_double := """".
    Definition quotel_backdouble := "\""".
    
    (* Java equivalent: JavaScriptBackend.indent *)
    Fixpoint indent (i : nat) : string
      := match i with
         | 0 => ""
         | S j => "  " ++ (indent j)
         end.

  End JSUtil.

  Section DataJS.

    (* Java equivalent: JavaScriptBackend.brandsToJS *)
    Definition brandsToJs (quotel:string) (b:brands)
      := bracketString "[" (joinStrings "," (map (fun x => bracketString quotel x quotel) b)) "]".

    (* Java equivalent: JavaScriptBackend.dataToJS *)
    Definition dataToJS (quotel:string) (d : data) : string :=
      jsonToJS quotel (data_to_js quotel d).

    Definition dataEnhancedToJS (quotel:string) (d : data) : string :=
      jsonToJS quotel (data_enhanced_to_js quotel d).

    Definition hierarchyToJS (quotel:string) (h:list (string*string)) :=
      dataToJS quotel (dcoll (map (fun x => drec (("sub",dstring (fst x)) :: ("sup", (dstring (snd x))) :: nil)) h)).

  End DataJS.

  Section NNRCJS.
    (* Sort criteria *)
    Definition singleSortCriteriaToJson (sc: string * SortDesc) : json :=
      match snd sc with
      | Ascending => jobject (("asc", jstring (fst sc))::nil)
      | Descending => jobject (("desc", jstring (fst sc))::nil)
      end.

    Definition sortCriteriaToJson (scl:SortCriterias) : json
      := jarray (map singleSortCriteriaToJson scl).

    Definition sortCriteriaToJs (quotel:string) (scl:SortCriterias) : string
      := jsonToJS quotel (sortCriteriaToJson scl).
    
    (* Java equivalent: JavaScriptBackend.uarithToJS *)
    Definition uarithToJs (u:arith_unary_op) (e:string) :=
      match u with
      | ArithAbs => "Math.abs (" ++ e ++ ")"
      | ArithLog2 => "Math.log2(" ++ e ++ ")"
      | ArithSqrt =>"Math.sqrt(" ++ e ++ ")"
      end.

    (* Java equivalent: JavaScriptBackend.barithToJs *)
    Definition barithToJs (b:arith_binary_op) (e1 e2:string) :=
      match b with
      | ArithPlus => e1 ++ "+" ++ e2
      | ArithMinus => e1 ++ "-" ++ e2
      | ArithMult => e1 ++ "*" ++ e2
      | ArithDivide => e1 ++ "/" ++ e2
      | ArithRem => e1 ++ "%" ++ e2
      | ArithMin => "Math.min(" ++ e1 ++ ", " ++ e2 ++ ")"
      | ArithMax => "Math.max(" ++ e1 ++ ", " ++ e2 ++ ")"
      end.
    
    Definition like_clause_to_javascript (lc:like_clause)
      := match lc with
         | like_literal literal => "escapeRegExp(" ++ quotel_double ++ literal ++ quotel_double ++ ")"
         | like_any_char => quotel_double ++ "." ++ quotel_double 
         | like_any_string => quotel_double ++ ".*" ++ quotel_double 
         end.

    (* Java equivalent: JavaScript.Backend.nrcToJS *)
    Fixpoint nnrcToJS
             (n : nnrc)                      (* NNRC expression to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol : string)                  (* Choice of end of line character *)
             (quotel : string)               (* Choice of quote character *)
             (ivs : list (string * string))  (* Input variables and their corresponding string representation *)
      : javascript                           (* JavaScript statements for computing result *)
        * javascript                         (* JavaScript expression holding result *)
        * nat                                (* next available unused temporary *)
      := match n with
         | NNRCGetConstant v => ("", "vc$" ++ v, t)
         | NNRCVar v =>
           match assoc_lookupr equiv_dec ivs v with
           | Some v_string => ("", v_string, t)
           | None => ("", "v" ++ v, t)
           end
         | NNRCConst d => ("", (dataToJS quotel d), t)
         | NNRCUnop op n1 =>
           let '(s1, e1, t0) := nnrcToJS n1 t i eol quotel ivs in
           let e0 := match op with
                     | OpIdentity => e1
                     | OpNeg => "!(" ++ e1 ++ ")"
                     | OpRec s => "{" ++ quotel ++ s ++ quotel ++ ": " ++ e1 ++ "}"
                     | OpDot s => "deref(" ++ e1 ++ ", " ++ quotel ++ s  ++ quotel ++ ")"
                     | OpRecRemove s => "remove(" ++ e1 ++ ", " ++ quotel ++ "" ++ s ++ "" ++ quotel ++ ")"
                     | OpRecProject sl => "project(" ++ e1 ++ ", " ++ (brandsToJs quotel sl) ++ ")"
                     | OpBag => "[" ++ e1 ++ "]"
                     | OpSingleton => "singleton(" ++ e1 ++ ")"
                     | OpFlatten => "flatten(" ++ e1 ++ ")"
                     | OpDistinct => "distinct(" ++ e1 ++ ")"
                     | OpOrderBy scl => "sort(" ++ e1 ++ ", " ++ (sortCriteriaToJs quotel scl) ++ ")"
                     | OpCount => e1 ++ ".length"
                     | OpSum => "sum(" ++ e1 ++ ")"
                     | OpNumMin => "Math.min.apply(Math," ++ e1 ++ ")"
                     | OpNumMax => "Math.max.apply(Math," ++ e1 ++ ")"
                     | OpNumMean => "Math.floor(arithMean(" ++ e1 ++ "))" (* Casts to Z using Math.floor() *)
                     | OpToString => "toString(" ++ e1 ++ ")"
                     | OpSubstring start olen =>
                       "(" ++ e1 ++ ").substring(" ++ toString start ++
                       match olen with
                       | Some len => ", " ++ toString len
                       | None => ""
                       end ++ ")"
                     | OpLike pat oescape =>
                       let lc := make_like_clause pat oescape in
                       let regex := "new RegExp([" ++ (joinStrings "," (map like_clause_to_javascript lc)) ++ "].join(" ++ quotel ++ quotel ++ "))" in
                       regex ++ ".test(" ++ e1 ++ ")"
                     | OpLeft => "{" ++ quotel ++ "left" ++ quotel ++ " : " ++ e1 ++ "}"
                     | OpRight => "{" ++ quotel ++ "right" ++ quotel ++ " : " ++ e1 ++ "}"
                     | OpBrand b => "brand(" ++ brandsToJs quotel b ++ "," ++ e1 ++ ")"
                     | OpUnbrand => "unbrand(" ++ e1 ++ ")"
                     | OpCast b => "cast(" ++ brandsToJs quotel b ++ "," ++ e1 ++ ")"
                     | OpArithUnary u => uarithToJs u e1
                     | OpForeignUnary fu
                       => foreign_to_javascript_unary_op i eol quotel fu e1
                     end in
           (s1, e0, t0)
         | NNRCBinop op n1 n2 =>
           let '(s1, e1, t2) := nnrcToJS n1 t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS n2 t2 i eol quotel ivs in
           let e0 := match op with
                     | OpEqual => "equal(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpRecConcat => "concat(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpRecMerge => "mergeConcat(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpAnd => "(" ++ e1 ++ " && " ++ e2 ++ ")"
                     | OpOr => "(" ++ e1 ++ " || " ++ e2 ++ ")"
                     | OpLt => "(" ++ e1 ++ " < " ++ e2 ++ ")"
                     | OpLe => "(" ++ e1 ++ " <= " ++ e2 ++ ")"
                     | OpBagUnion => "bunion(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpBagDiff => "bminus(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpBagMin => "bmin(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpBagMax => "bmax(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpContains => "contains(" ++ e1 ++ ", " ++ e2 ++ ")"
                     | OpStringConcat => "(" ++ e1 ++ " + " ++ e2 ++ ")"
                     | OpArithBinary b => barithToJs b e1 e2
                     | OpForeignBinary fb
                       => foreign_to_javascript_binary_op i eol quotel fb e1 e2
                     end in
           (s1 ++ s2, e0, t0)
         | NNRCLet v bind body =>
           let '(s1, e1, t2) := nnrcToJS bind t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS body t2 i eol quotel ivs in
           let v0 := "v" ++ v in
           (s1 ++ (indent i) ++ "var " ++ v0 ++ " = " ++ e1 ++ ";" ++ eol
               ++ s2,
            e2, t0)
         | NNRCFor v iter body =>
           let '(s1, e1, t2) := nnrcToJS iter t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS body t2 (i+1) eol quotel ivs in
           let elm := "v" ++ v in
           let src := "src" ++ (nat_to_string10 t0) in
           let idx := "i" ++ (nat_to_string10 t0) in
           let dst := "dst" ++ (nat_to_string10 t0) in
           (s1 ++ (indent i) ++ "var " ++ dst ++ " = [];" ++ eol
               ++ (indent i) ++ ("for (var "
                                   ++ src ++ "=" ++ e1 ++ ", "
                                   ++ idx ++ "=0; "
                                   ++ idx ++ "<" ++ src ++ ".length; "
                                   ++ idx ++ "++) {" ++ eol)
               ++ (indent (i+1)) ++ ("var " ++ elm ++ " = " ++ src
                                            ++ "[" ++ idx ++ "];" ++ eol)
               ++ s2
               ++ (indent (i+1)) ++ dst ++ ".push(" ++ e2 ++ ");" ++ eol
               ++ (indent i) ++ "}" ++ eol,
            dst, t0 + 1)
         | NNRCIf c n1 n2 =>
           let '(s1, e1, t2) := nnrcToJS c t i eol quotel ivs in
           let '(s2, e2, t3) := nnrcToJS n1 t2 (i+1) eol quotel ivs in
           let '(s3, e3, t0) := nnrcToJS n2 t3 (i+1) eol quotel ivs in
           let v0 := "t" ++ (nat_to_string10 t0) in
           (s1 ++ (indent i) ++ "var " ++ v0 ++ ";" ++ eol
               ++ (indent i) ++ "if (" ++ e1 ++ ") {" ++ eol
               ++ s2
               ++ (indent (i+1)) ++ v0 ++ " = " ++ e2 ++ ";" ++ eol
               ++ (indent i) ++ "} else {" ++ eol
               ++ s3
               ++ (indent (i+1)) ++ v0 ++ " = " ++ e3 ++ ";" ++ eol
               ++ (indent i) ++ "}" ++ eol,
            v0, t0 + 1)
         | NNRCEither nd xl nl xr nr =>
           let '(s1, e1, t2) := nnrcToJS nd t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS nl t2 (i+1) eol quotel ivs in
           let '(s3, e3, t1) := nnrcToJS nr t0 (i+1) eol quotel ivs in
           let vl := "v" ++ xl in
           let vr := "v" ++ xr in
           let res := "res" ++ (nat_to_string10 t1) in  (* Stores the result from either left or right evaluation so it can be returned *)
           (s1 ++ (indent i) ++ "var " ++ res ++ " = null;" ++ eol
               ++ (indent i) ++ "if (either(" ++ e1 ++ ")) {" ++ eol
               ++ (indent (i+1)) ++ "var " ++ vl ++ " = null;" ++ eol
               ++ (indent (i+1)) ++ vl ++ " = toLeft(" ++ e1 ++ ");" ++ eol
               ++ s2
               ++ (indent (i+1)) ++ res ++ " = " ++ e2 ++ ";" ++ eol
               ++ (indent i) ++ "} else {" ++ eol
               ++ (indent (i+1)) ++ "var " ++ vr ++ " = null;" ++ eol
               ++ (indent (i+1)) ++ vr ++ " = toRight(" ++ e1 ++ ");" ++ eol
               ++ s3
               ++ (indent (i+1)) ++ res ++ " = " ++ e3 ++ ";" ++ eol
               ++ (indent i) ++ "}" ++ eol,
            res, t1 + 1)
         | NNRCGroupBy g sl n1 =>
           let '(s1, e1, t0) := nnrcToJS n1 t i eol quotel ivs in
           let e0 := "groupby(" ++ e1 ++ ", "
                                ++ quotel ++ g ++ quotel ++ ", "
                                ++ (brandsToJs quotel sl) ++ ")" in
           (s1, e0, t0)
       end.

    (* Java equivalent: JavaScriptBackend.nrcToJSunshadow *)
    Definition nnrcToJSunshadow
               (n : nnrc)
               (t : nat)
               (i : nat)
               (eol : string)
               (quotel : string)
               (avoid: list var)
               (ivs : list (string * string))
      := let n := unshadow_js avoid n in
         nnrcToJS n t i eol quotel ivs.

    (* Java equivalent: JavaScriptBackend.makeJSParams *)
    Definition makeJSParams (ivs: list string) :=
      joinStrings ", " ivs.

    (* Java equivalent: JavaScriptBackend.paramsToStringedParams *)
    Definition paramsToStringedParams (params : list string) :=
      map (fun x => (x,x)) params.

    (* Java equivalent: JavaScriptBackend.nrcToJSFunStub *)    
    Definition nnrcToJSFunStub
               (e:nnrc)
               (harness:bool)
               (i:nat)
               (eol:string)
               (quotel:string)
               (params : list string)
               (fname:string)
      := let '(j0, v0, t0) := nnrcToJSunshadow e 1 (i+1) eol quotel params (paramsToStringedParams params) in
         "" ++ (indent i) ++ "function " ++ fname ++ "("++ (makeJSParams params) ++ ") {" ++ eol
            ++ j0
            ++ (indent i) ++ "  return " ++ v0 ++ ";" ++ eol
            ++ (indent i) ++ "}" ++ eol
            ++ (if harness then "%HARNESS%" else "").

    Definition nnrcToJSFunStubConstants
               (e:nnrc)
               (i:nat)
               (eol:string)
               (quotel:string)
               (params : list string)
               (fname:string)
               (fprefix:string)
      := let '(j0, v0, t0) := nnrcToJSunshadow e 1 (i+1) eol quotel params (paramsToStringedParams params) in
         "" ++ (indent i) ++ fprefix ++ fname ++ "("++ (makeJSParams params) ++ ") {" ++ eol
            ++ j0
            ++ (indent i) ++ "  return " ++ v0 ++ ";" ++ eol
            ++ (indent i) ++ "}".

    (* Java equivalent: JavaScriptBackend.nrcToJSFunStubConstants *)
    Definition nnrcToJSFunStubConstantsAsFunction
               (e:nnrc)
               (i:nat)
               (eol:string)
               (quotel:string)
               (params : list string)
               (fname:string)
      := let fprefix := "function " in
         nnrcToJSFunStubConstants e i eol quotel params fname fprefix.

    Definition nnrcToJSFunStubConstantsAsMethod
               (e:nnrc)
               (i:nat)
               (eol:string)
               (quotel:string)
               (params : list string)
               (fname:string)
      := let fprefix := "" in
         nnrcToJSFunStubConstants e i eol quotel params fname fprefix.

    (* Java equivalent: JavaScriptBackend.nrcToJSFun *)
    Definition nnrcToJSFun
               (input_v:string)
               (e:nnrc)
               (i:nat)
               (eol:string)
               (quotel:string)
               (ivs : list string)
               (fname:string)
      := let e' := closeFreeVars jsSafeSeparator jsIdentifierSanitize (NNRCVar input_v) e ivs in
         nnrcToJSFunStubConstantsAsFunction e' i eol quotel ivs fname.

    Definition nnrcToJSMethod
               (input_v:string)
               (e:nnrc)
               (i:nat)
               (eol:string)
               (quotel:string)
               (ivs : list string)
               (fname:string)
      := let e' := closeFreeVars jsSafeSeparator jsIdentifierSanitize (NNRCVar input_v) e ivs in
         nnrcToJSFunStubConstantsAsMethod e' i eol quotel ivs fname.

    (* Java equivalent: JavaScriptBackend.generateJavaScript *)
    Definition nnrc_to_js_top (e:nnrc) : javascript :=
      let input_f := "query" in
      let input_v := "constants" in
      let init_indent := 0 in
      nnrcToJSFun input_v e init_indent eol_newline quotel_double (input_v::nil) input_f.

    Definition nnrc_to_js_top_with_name (e:nnrc) (fname:string) : javascript :=
      let input_v := "constants" in
      let init_indent := 0 in
      nnrcToJSFun input_v e init_indent eol_newline quotel_double (input_v::nil) fname.

  End NNRCJS.

End NNRCtoJavaScript.

