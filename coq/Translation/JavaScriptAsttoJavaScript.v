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
Require Import JavaScriptAstRuntime.
Require Import JavaScriptRuntime.

Local Open Scope string_scope.

Section ToString.

  Definition eol:string := "\n".
  Definition quotel:string := """".

  Fixpoint indent (i : nat) : string :=
    match i with
    | 0 => ""
    | S j => "  " ++ (indent j)
    end.

  Definition comma_list l := joinStrings ", " l.

  Definition string_of_funcbody
             (body: funcbody)
             (i: nat) (* indentation level *) :=
      "XXX TODO XXX".

  Definition string_of_funcdecl (f:funcdecl) : string :=
    "function " ++ f.(funcdecl_name) ++ "(" ++ comma_list f.(funcdecl_parameters) ++ ") {"++ eol
    ++ string_of_funcbody f.(funcdecl_body) 2 ++ eol
    ++ "}"
  .

End ToString.

Section JavaScriptAsttoJavaScript.

  Definition js_ast_to_js_top (f:funcdecl) : javascript :=
    string_of_funcdecl f.

End JavaScriptAsttoJavaScript.
