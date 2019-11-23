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
Require Import JsAst.JsNumber.

Local Open Scope string_scope.

Section ToString.

  Definition eol:string := String (Ascii.ascii_of_nat 10) EmptyString.
  Definition quotel:string := """".

  Fixpoint indent (i : nat) : string :=
    match i with
    | 0 => ""
    | S j => "  " ++ (indent j)
    end.

  Definition comma_list l := concat ", " l.

  Definition string_of_literal
             (c: literal)
    : string :=
    match c with
    | literal_null => "null"
    | literal_bool true => "true"
    | literal_bool false => "false"
    | literal_number n => to_string n
    | literal_string s => quotel ++ s ++ quotel
    end.

  Definition string_of_propname (name: propname) : string :=
    match name with
    | propname_identifier n => n
    | propname_string s => quotel ++ s ++ quotel
    | propname_number n => to_string n
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
      let props :=
          List.map
            (fun (prop: (propname * propbody)) =>
               let (name, body) := prop in
               eol ++ (indent (i+1)) ++
               match body with
               | propbody_val e =>
                 quotel ++ string_of_propname name ++ quotel ++ ": " ++ "(" ++ string_of_expr e (i+1) ++ ")"
               | propbody_get funcbody =>
                 "get " ++ quotel ++ string_of_propname name ++ quotel ++ "() {" ++
                        string_of_funcbody funcbody (i+1) ++
                 "}"
               | propbody_set args funcbody =>
                 "set " ++ quotel ++ string_of_propname name ++ quotel ++ "("++ comma_list args ++") {" ++
                        string_of_funcbody funcbody (i+1) ++
                 "}"
               end)
            o
      in
      "{" ++
          comma_list props ++ eol ++
       indent i ++ "}"
    | expr_array a =>
      let l :=
          List.map
            (fun eopt =>
               match eopt with
               | Some e => string_of_expr e (i+1)
               | None => "null"
               end)
            a
      in
      "[ " ++ comma_list l ++ " ]"
  | expr_function fopt args body =>
    let name :=
        match fopt with
        | Some f => f
        | None => ""
        end
    in
    "(function "++name++"("++ comma_list args ++") {"++eol++
               indent (i+1)++string_of_funcbody body (i+1) ++eol++
               indent i ++"})"
  | expr_access e1 e2 =>
    string_of_expr e1 i ++ "[" ++ string_of_expr e2 (i+1) ++ "]"
  | expr_member e s =>
    string_of_expr e i ++ "." ++ s
  | expr_new e args =>
    let args := List.map (fun e => string_of_expr e (i+1)) args in
    "new " ++ string_of_expr e i ++ "(" ++ comma_list args ++ ")"
  | expr_call f args =>
    let args := List.map (fun e => string_of_expr e (i+1)) args in
    string_of_expr f i ++ "(" ++ comma_list args ++ ")"
  | expr_unary_op op e =>
    let e := string_of_expr e (i+1) in
    match op with
    | unary_op_delete => "(delete " ++ e ++ ")"
    | unary_op_void => "(void " ++ e ++ ")"
    | unary_op_typeof => "(typeof " ++ e ++ ")"
    | unary_op_post_incr => "(" ++ e ++ "++)"
    | unary_op_post_decr => "(" ++ e ++ "--)"
    | unary_op_pre_incr => "(++" ++ e ++ ")"
    | unary_op_pre_decr => "(--" ++ e ++ ")"
    | unary_op_add => "(+" ++ e ++ ")"
    | unary_op_neg => "(-" ++ e ++ ")"
    | unary_op_bitwise_not => "(~" ++ e ++ ")"
    | unary_op_not => "(!" ++ e ++ ")"
    end
  | expr_binary_op e1 op e2 =>
    let e1 := string_of_expr e1 (i+1) in
    let e2 := string_of_expr e2 (i+1) in
    match op with
    | binary_op_mult => "(" ++ e1 ++ " * " ++ e2 ++ ")"
    | binary_op_div => "(" ++ e1 ++ " / " ++ e2 ++ ")"
    | binary_op_mod => "(" ++ e1 ++ " % " ++ e2 ++ ")"
    | binary_op_add => "(" ++ e1 ++ " + " ++ e2 ++ ")"
    | binary_op_sub => "(" ++ e1 ++ " - " ++ e2 ++ ")"
    | binary_op_left_shift => "(" ++ e1 ++ " << " ++ e2 ++ ")"
    | binary_op_right_shift => "(" ++ e1 ++ " >> " ++ e2 ++ ")"
    | binary_op_unsigned_right_shift => "(" ++ e1 ++ " >>> " ++ e2 ++ ")"
    | binary_op_lt => "(" ++ e1 ++ " < " ++ e2 ++ ")"
    | binary_op_gt => "(" ++ e1 ++ " > " ++ e2 ++ ")"
    | binary_op_le => "(" ++ e1 ++ " <= " ++ e2 ++ ")"
    | binary_op_ge => "(" ++ e1 ++ " >= " ++ e2 ++ ")"
    | binary_op_instanceof => "(" ++ e1 ++ " instanceof " ++ e2 ++ ")"
    | binary_op_in => "(" ++ e1 ++ " in " ++ e2 ++ ")"
    | binary_op_equal => "(" ++ e1 ++ " == " ++ e2 ++ ")"
    | binary_op_disequal => "(" ++ e1 ++ " != " ++ e2 ++ ")"
    | binary_op_strict_equal => "(" ++ e1 ++ " === " ++ e2 ++ ")"
    | binary_op_strict_disequal => "(" ++ e1 ++ " !== " ++ e2 ++ ")"
    | binary_op_bitwise_and => "(" ++ e1 ++ " & " ++ e2 ++ ")"
    | binary_op_bitwise_or => "(" ++ e1 ++ " | " ++ e2 ++ ")"
    | binary_op_bitwise_xor => "(" ++ e1 ++ " ^ " ++ e2 ++ ")"
    | binary_op_and => "(" ++ e1 ++ " && " ++ e2 ++ ")"
    | binary_op_or => "(" ++ e1 ++ " || " ++ e2 ++ ")"
    | binary_op_coma => "(" ++ e1 ++ ", " ++ e2 ++ ")"
    end
  | expr_conditional e1 e2 e3 =>
    let e1 := string_of_expr e1 (i+1) in
    let e2 := string_of_expr e2 (i+1) in
    let e3 := string_of_expr e3 (i+1) in
    "(" ++ e1 ++ " ? " ++ e2 ++ " : " ++ e3 ++ ")"
  | expr_assign e1 None e2 =>
    let e1 := string_of_expr e1 (i+1) in
    let e2 := string_of_expr e2 (i+1) in
    e1 ++ " = " ++ e2
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
          List.map (fun s => string_of_stat s (i+1)) l
      in
      "{" ++ eol ++
          concat (";"++eol) seq ++ eol ++
      indent i ++ "}"
    | stat_var_decl l =>
      let decls :=
        List.map
          (fun (x_e_opt: string * option expr) =>
             let (x, e_opt) := x_e_opt in
             "let " ++ x ++
             match e_opt with
             | Some e =>
               " = " ++ string_of_expr e (i+1)
             | None => ""
             end
          )
          l
    in
    concat (";"++eol) decls
  | stat_if e s1 s2_opt =>
    "if (" ++ string_of_expr e (i+1) ++ ") {" ++ eol ++
    string_of_stat s1 (i+1) ++ eol ++
    indent i ++ "} else {" ++ eol ++
    match s2_opt with
    | Some s2 => string_of_stat s2 (i+1) ++ eol
    | None => ""
    end ++
    indent i ++ "}"
  (* | stat_do_while : label_set -> stat -> expr -> stat *)
  (* | stat_while : label_set -> expr -> stat -> stat *)
  (* | stat_with : expr -> stat -> stat *)
  (* | stat_throw : expr -> stat *)
  | stat_return None =>
    "return ;"
  | stat_return (Some e) =>
    "return " ++ (string_of_expr e (i+1)) ++ ";"
  (* | stat_break : label -> stat *)
  (* | stat_continue : label ->  stat *)
  (* | stat_try : stat -> option (string * stat) -> option stat -> stat (* Note: try s1 [catch (x) s2] [finally s3] *) *)
  (* | stat_for : label_set -> option expr -> option expr -> option expr -> stat -> stat (* Note: for (e1; e2; e3) stat *) *)
  | stat_for_var lbl vars e2_opt e3_opt s =>
    (* Note: for (var ...; e2; e3) stat *)
    let decls :=
        List.map
          (fun (decl: (string * option expr)) =>
             let (x, e1_opt) := decl in
             x ++
             match e1_opt with
             | None => ""
             | Some e1 => " = " ++ string_of_expr e1 (i+1)
             end)
          vars
    in
    (* lbl ++ *) (* TODO: print labels *)
    "for (" ++
        "let " ++ comma_list decls ++ "; " ++
        match e2_opt with
        | Some e2 => string_of_expr e2 (i+1)
        | None => ""
        end ++ "; " ++
        match e3_opt with
        | Some e3 => string_of_expr e3 (i+1)
        | None => ""
        end ++ ") {" ++ eol ++
        string_of_stat s (i+1) ++ eol ++
    indent i ++ "}" ++ eol
  (* | stat_for_in : label_set -> expr -> expr -> stat -> stat (* Note: for (e1 in e2) stat *) *)
  | stat_for_in_var lbl x e1_opt e2 s =>
    (*  Note: for (var x [= e1] in e2) stat *)
    (* lbl ++ *) (* TODO: print labels *)
    "for (let " ++ x ++
        match e1_opt with
        | Some e => " = " ++ string_of_expr e (i+1)
        | None => ""
        end ++
        " in " ++ string_of_expr e2 (i+1)  ++ ") {" ++ eol ++
        string_of_stat s (i+1) ++ eol ++
    indent i ++ "}" ++ eol
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
      concat eol elems'
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
    ++ "}" ++ eol
  .

End ToString.

Section JavaScriptAsttoJavaScript.

  Definition js_ast_to_js_top (f:funcdecl) : javascript :=
    string_of_funcdecl f.

End JavaScriptAsttoJavaScript.
