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

  Definition eol:string := String (Ascii.ascii_of_nat 10) EmptyString.
  Definition quotel:string := """".

  Fixpoint indent (i : nat) : string :=
    match i with
    | 0 => ""
    | S j => "  " ++ (indent j)
    end.

  Definition comma_list l := joinStrings ", " l.

  Definition string_of_literal
             (c: literal)
    : string :=
    match c with
    | literal_null => "null"
    | literal_bool true => "true"
    | literal_bool false => "false"
    | literal_number n => "XXX TODO: number XXX" (* XXX TODO XXX *)
    | literal_string s => quotel ++ s ++ quotel
    end.

  Fixpoint string_of_expr
             (e: expr)
             (i: nat) (* indentation level *)
             { struct e }
  : string :=
    match e with
    | expr_this => "this"
    | expr_identifier x => x
    | expr_literal c => string_of_literal c
    | expr_object o =>
      "XXX TODO: object XXX" (* XXX TODO XXX *)
    | expr_array a =>
      let l :=
          List.map
            (fun eopt =>
               match eopt with
               | Some e => string_of_expr e (i+2)
               | None => "null"
               end)
            a
      in
      "[ " ++ comma_list l ++ " ]"
  | expr_function fopt args body =>
  (* : option string -> list string -> funcbody -> expr *)
    let name :=
        match fopt with
        | Some f => f
        | None => ""
        end
    in
    "(function "++name++"("++ comma_list args ++") {"++eol++
               string_of_funcbody body (i+2) ++eol++
               indent i ++"})"
  | expr_access e1 e2 =>
    string_of_expr e1 i ++ "[" ++ string_of_expr e1 (i+2) ++ "]"
  | expr_member e s =>
    string_of_expr e i ++ "." ++ s
  (* | expr_new : expr -> list expr -> expr *)
  (* | expr_call : expr -> list expr -> expr *)
  (* | expr_unary_op : unary_op -> expr -> expr *)
  (* | expr_binary_op : expr -> binary_op -> expr -> expr *)
  (* | expr_conditional : expr -> expr -> expr -> expr *)
  (* | expr_assign : expr -> option binary_op -> expr -> expr *)
    | _ => "XXX TODO XXX"
    end

  with string_of_stat
             (s: stat)
             (i: nat) (* indentation level *)
             { struct s }
  : string :=
    indent i ++
    match s with
    | stat_expr e =>
      string_of_expr e i ++ ";"
    | stat_label lbl s =>
      lbl ++ ":" ++ string_of_stat s i
    | stat_block l =>
      let seq :=
          List.map (fun s => string_of_stat s (i+2)) l
      in
      "{" ++ eol ++
          joinStrings (";"++eol) seq ++ eol ++
      "}"
  (* | stat_var_decl : list (string * option expr) -> stat *)
  (* | stat_if : expr -> stat -> option stat -> stat *)
  (* | stat_do_while : label_set -> stat -> expr -> stat *)
  (* | stat_while : label_set -> expr -> stat -> stat *)
  (* | stat_with : expr -> stat -> stat *)
  (* | stat_throw : expr -> stat *)
  (* | stat_return : option expr -> stat *)
  (* | stat_break : label -> stat *)
  (* | stat_continue : label ->  stat *)
  (* | stat_try : stat -> option (string * stat) -> option stat -> stat (* Note: try s1 [catch (x) s2] [finally s3] *) *)
  (* | stat_for : label_set -> option expr -> option expr -> option expr -> stat -> stat (* Note: for (e1; e2; e3) stat *) *)
  (* | stat_for_var : label_set -> list (string * option expr) -> option expr -> option expr -> stat -> stat (* Note: for (var ...; e2; e3) stat *) *)
  (* | stat_for_in : label_set -> expr -> expr -> stat -> stat (* Note: for (e1 in e2) stat *) *)
  (* | stat_for_in_var : label_set -> string -> option expr -> expr -> stat -> stat (*  Note: for (var x [= e1] in e2) stat *) *)
  (* | stat_debugger : stat *)
  (* | stat_switch : label_set -> expr -> switchbody -> stat *)

    | _ => "XXX TODO XXX"
    end

  with string_of_element
             (e: element)
             (i: nat) (* indentation level *)
             { struct e }
  : string :=
    match e with
    | element_stat s =>
      string_of_stat s i
    | element_func_decl f params body =>
      "XXX TODO XXX"
    end

  with string_of_prog
             (p: prog)
             (i: nat) (* indentation level *)
             { struct p }
  : string :=
    match p with
    | prog_intro _ elems =>
      let elems' := List.map (fun e => string_of_element e i) elems in
      joinStrings eol elems'
    end

  with string_of_funcbody
             (body: funcbody)
             (i: nat) (* indentation level *)
             { struct body }
  : string :=
    match body with
    | funcbody_intro p _ =>
      string_of_prog p i
    end.

   Definition string_of_funcdecl
         (f:funcdecl)
       : string :=
    "function " ++ f.(funcdecl_name) ++ "(" ++ comma_list f.(funcdecl_parameters) ++ ") {"++ eol
    ++ string_of_funcbody f.(funcdecl_body) 2 ++ eol
    ++ "}"
  .

End ToString.

Section JavaScriptAsttoJavaScript.

  Definition js_ast_to_js_top (f:funcdecl) : javascript :=
    string_of_funcdecl f.

End JavaScriptAsttoJavaScript.
