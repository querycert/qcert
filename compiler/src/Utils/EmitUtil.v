(*
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
Require Import StringAdd.
Require Import List.
Require Import Ascii.
Require Import NativeString.

Local Open Scope string_scope.
Local Open Scope nstring_scope.
Import ListNotations.

Section EmitUtil.
  Section Whitespace.
    Definition eol_newline : string := String (Ascii.ascii_of_nat 10) EmptyString.
    Definition eol_backn : string := "\n".

    Definition neol_newline : nstring := ^eol_newline.
    Definition neol_backn : nstring := ^eol_backn.

    Definition quotel_double : string := """".
    Definition quotel_backdouble : string := "\""".

    Definition nquotel_double : nstring := ^quotel_double.
    Definition nquotel_backdouble : nstring := ^quotel_backdouble.

    (* Java equivalent: JavaScriptBackend.indent *)
    Fixpoint indent (i : nat) : nstring :=
      match i with
      | 0 => ^EmptyString
      | S j => ^"  " +++ (indent j)
      end.

    Definition string_bracket (open s close:string) : string :=
      append open (append s close).

    Definition nstring_bracket (open s close:nstring) : nstring :=
      nstring_append open (nstring_append s close).

  End Whitespace.

  Section JSIdentifiers.
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

    Definition jsIdentifierFixInitial (ident:string) : string :=
      match ident with
      (* We also don't want empty identifier names *)
      | EmptyString =>
        String jsIdentifierInitialCharacterToAdd EmptyString
      | String a _ =>
        if in_dec ascii_dec a jsAllowedIdentifierInitialCharacters
        then ident
        else String jsIdentifierInitialCharacterToAdd ident
      end.

    Definition jsIdentifierSanitizeChar (a:ascii) :=
      if in_dec ascii_dec a jsAllowedIdentifierCharacters
      then a
      else jsIdenitiferCharacterForReplacement.

    Definition jsIdentifierSanitizeBody (ident:string) :=
      map_string jsIdentifierSanitizeChar ident.

    Definition jsIdentifierSanitize (ident:string) :=
      jsIdentifierFixInitial (jsIdentifierSanitizeBody ident).

    Definition jsSafeSeparator : string := "_".

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

  End JSIdentifiers.

  Section JavaIdentifiers.
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

  Definition javaIdentifierFixInitial (ident:string) : string :=
    match ident with
    (* We also don't want empty identifier names *)
    | EmptyString =>
      String javaIdentifierInitialCharacterToAdd EmptyString
    | String a _ =>
      if in_dec ascii_dec a javaAllowedIdentifierInitialCharacters
      then ident
      else String javaIdentifierInitialCharacterToAdd ident
    end.

  Definition javaIdentifierSanitizeChar (a:ascii) :=
    if in_dec ascii_dec a javaAllowedIdentifierCharacters
    then a
    else javaIdenitiferCharacterForReplacement.

  Definition javaIdentifierSanitizeBody (ident:string) :=
    map_string javaIdentifierSanitizeChar ident.
  
  Definition javaIdentifierSanitize (ident:string) : string :=
    javaIdentifierFixInitial (javaIdentifierSanitizeBody ident).

  Definition javaSafeSeparator := "_".

  (* pulled of off various lists of javascript reserved keywords 
     as well some common html/java words that should be avoided
     in case of shared context/interop *)

  Definition javaAvoidList :=
    ["abstract"; "assert"; "boolean"; "break"; "byte"; "case"; "catch"; "char"; "class"; "const"; "continue"; "default"; "do"; "double"; "else"; "enum"; "extends"; "false"; "final"; "finally"; "float"; "for"; "goto"; "if"; "implements"; "import"; "instanceof"; "int"; "interface"; "long"; "native"; "new"; "null"; "package"; "private"; "protected"; "public"; "return"; "short"; "static"; "strictfp"; "super"; "switch"; "synchronized"; "this"; "throw"; "throws"; "transient"; "true"; "try"; "void"; "volatile"; "while"].

  End JavaIdentifiers.

End EmitUtil.
