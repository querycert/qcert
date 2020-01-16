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

Require Import List.
Require Import String.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Utils.
Require Import JavaScriptAstRuntime.
Require Import JavaScriptRuntime.
Require Import JsAst.JsNumber.

Local Open Scope string_scope.
Local Open Scope nstring_scope.

Section ToString.

  Section Util.
    Definition eol:nstring := ^String (Ascii.ascii_of_nat 10) EmptyString.
    Definition quotel:nstring := ^"""".

    Fixpoint indent (i : nat) : nstring :=
      match i with
      | 0 => ^""
      | S j => ^"  " +++ (indent j)
      end.

    Definition comma_list_string l := nstring_concat (^", ") (map nstring_quote l).
    Definition comma_list l := nstring_concat (^", ") l.

    Definition js_quote_char (a:ascii) : nstring :=
      match a with
      | "008"%char => ^"\b"
      | "009"%char => ^"\t"
      | "010"%char => ^"\n"
      | "013"%char => ^"\r"
      | """"%char => ^"\"""
      | "\"%char => ^"\\"
      | _ => ^String a EmptyString
      end.

    Definition js_quote_string (s:string) : nstring :=
      nstring_flat_map js_quote_char (^s).

    Definition js_quote_number (n:number) : nstring :=
      if (float_eq n float_infinity) then ^"Infinity"
      else if (float_eq n float_neg_infinity) then ^"-Infinity"
      else if (float_eq n float_nan) then ^"NaN"
      else ^to_string n.

  End Util.

  Definition nstring_of_literal (c: literal) : nstring :=
    match c with
    | literal_null => ^"null"
    | literal_bool true => ^"true"
    | literal_bool false => ^"false"
    | literal_number n => js_quote_number n
    | literal_string s => quotel +++ js_quote_string s +++ quotel
    end.

  Definition nstring_of_propname (name: propname) : nstring :=
    match name with
    | propname_identifier n => ^n
    | propname_string s => quotel +++ ^s +++ quotel
    | propname_number n => ^ to_string n
    end.

  Fixpoint nstring_of_expr
           (e: expr)
           (i: nat) (* indentation level *)
           { struct e }
    : nstring :=
    match e with
    | expr_this => ^"this"
    | expr_identifier x => ^x
    | expr_literal c => nstring_of_literal c
    | expr_object o =>
      let props :=
          List.map
            (fun (prop: (propname * propbody)) =>
               let (name, body) := prop in
               eol +++ (indent (i+1)) +++
                   match body with
                   | propbody_val e =>
                     quotel +++ nstring_of_propname name +++ quotel
                            +++ ^": " +++ ^"(" +++ nstring_of_expr e (i+1) +++ ^")"
                   | propbody_get funcbody =>
                     ^"get " +++ quotel +++ nstring_of_propname name +++ quotel
                             +++ ^"() {" +++ (nstring_of_funcbody funcbody (i+1)) +++ ^"}"
                   | propbody_set args funcbody =>
                     ^"set " +++ quotel +++ nstring_of_propname name +++ quotel
                             +++ ^"(" +++ comma_list_string args +++ ^") {"
                             +++ nstring_of_funcbody funcbody (i+1) +++ ^"}"
                   end)
            o
      in
      ^"{" +++ comma_list props +++ eol +++ indent i +++ ^"}"
    | expr_array a =>
      let l :=
          List.map
            (fun eopt =>
               match eopt with
               | Some e => nstring_of_expr e (i+1)
               | None => ^"null"
               end)
            a
      in
      ^"[ " +++ comma_list l +++ ^" ]"
    | expr_function fopt args body =>
      let name :=
          match fopt with
          | Some f => ^f
          | None => ^""
          end
      in
      ^"(function " +++ name +++ ^"(" +++ comma_list_string args +++ ^") {" +++ eol +++
       indent (i+1) +++ nstring_of_funcbody body (i+1) +++ eol +++
       indent i +++ ^"})"
    | expr_access e1 e2 =>
      nstring_of_expr e1 i +++ ^"[" +++ nstring_of_expr e2 (i+1) +++ ^"]"
    | expr_member e s =>
      nstring_of_expr e i +++ ^"[" +++ quotel +++ ^s +++ quotel +++ ^"]"
    | expr_new e args =>
      let args := List.map (fun e => nstring_of_expr e (i+1)) args in
      ^"new " +++ nstring_of_expr e i +++ ^"(" +++ comma_list args +++ ^")"
    | expr_call f args =>
      let args := List.map (fun e => nstring_of_expr e (i+1)) args in
      nstring_of_expr f i +++ ^"(" +++ comma_list args +++ ^")"
    | expr_unary_op op e =>
      let e := nstring_of_expr e (i+1) in
      match op with
      | unary_op_delete => ^"(delete " +++ e +++ ^")"
      | unary_op_void => ^"(void " +++ e +++ ^")"
      | unary_op_typeof => ^"(typeof " +++ e +++ ^")"
      | unary_op_post_incr => ^"(" +++ e +++ ^"++)"
      | unary_op_post_decr => ^"(" +++ e +++ ^"--)"
      | unary_op_pre_incr => ^"(++" +++ e +++ ^")"
      | unary_op_pre_decr => ^"(--" +++ e +++ ^")"
      | unary_op_add => ^"(+" +++ e +++ ^")"
      | unary_op_neg => ^"(-" +++ e +++ ^")"
      | unary_op_bitwise_not => ^"(~" +++ e +++ ^")"
      | unary_op_not => ^"(!" +++ e +++ ^")"
      end
    | expr_binary_op e1 op e2 =>
      let e1 := nstring_of_expr e1 (i+1) in
      let e2 := nstring_of_expr e2 (i+1) in
      match op with
      | binary_op_mult => ^"(" +++ e1 +++ ^" * " +++ e2 +++ ^")"
      | binary_op_div => ^"(" +++ e1 +++ ^" / " +++ e2 +++ ^")"
      | binary_op_mod => ^"(" +++ e1 +++ ^" % " +++ e2 +++ ^")"
      | binary_op_add => ^"(" +++ e1 +++ ^" + " +++ e2 +++ ^")"
      | binary_op_sub => ^"(" +++ e1 +++ ^" - " +++ e2 +++ ^")"
      | binary_op_left_shift => ^"(" +++ e1 +++ ^" << " +++ e2 +++ ^")"
      | binary_op_right_shift => ^"(" +++ e1 +++ ^" >> " +++ e2 +++ ^")"
      | binary_op_unsigned_right_shift => ^"(" +++ e1 +++ ^" >>> " +++ e2 +++ ^")"
      | binary_op_lt => ^"(" +++ e1 +++ ^" < " +++ e2 +++ ^")"
      | binary_op_gt => ^"(" +++ e1 +++ ^" > " +++ e2 +++ ^")"
      | binary_op_le => ^"(" +++ e1 +++ ^" <= " +++ e2 +++ ^")"
      | binary_op_ge => ^"(" +++ e1 +++ ^" >= " +++ e2 +++ ^")"
      | binary_op_instanceof => ^"(" +++ e1 +++ ^" instanceof " +++ e2 +++ ^")"
      | binary_op_in => ^"(" +++ e1 +++ ^" in " +++ e2 +++ ^")"
      | binary_op_equal => ^"(" +++ e1 +++ ^" == " +++ e2 +++ ^")"
      | binary_op_disequal => ^"(" +++ e1 +++ ^" != " +++ e2 +++ ^")"
      | binary_op_strict_equal => ^"(" +++ e1 +++ ^" === " +++ e2 +++ ^")"
      | binary_op_strict_disequal => ^"(" +++ e1 +++ ^" !== " +++ e2 +++ ^")"
      | binary_op_bitwise_and => ^"(" +++ e1 +++ ^" & " +++ e2 +++ ^")"
      | binary_op_bitwise_or => ^"(" +++ e1 +++ ^" | " +++ e2 +++ ^")"
      | binary_op_bitwise_xor => ^"(" +++ e1 +++ ^" ^ " +++ e2 +++ ^")"
      | binary_op_and => ^"(" +++ e1 +++ ^" && " +++ e2 +++ ^")"
      | binary_op_or => ^"(" +++ e1 +++ ^" || " +++ e2 +++ ^")"
      | binary_op_coma => ^"(" +++ e1 +++ ^", " +++ e2 +++ ^")"
      end
    | expr_conditional e1 e2 e3 =>
      let e1 := nstring_of_expr e1 (i+1) in
      let e2 := nstring_of_expr e2 (i+1) in
      let e3 := nstring_of_expr e3 (i+1) in
      ^"(" +++ e1 +++ ^" ? " +++ e2 +++ ^" : " +++ e3 +++ ^")"
    | expr_assign e1 None e2 =>
      let e1 := nstring_of_expr e1 (i+1) in
      let e2 := nstring_of_expr e2 (i+1) in
      e1 +++ ^" = " +++ e2
    | _ => ^"XXX TODO XXX"
    end

  with nstring_of_stat
         (s: stat)
         (i: nat) (* indentation level *)
         { struct s }
       : nstring :=
         indent i +++
                match s with
                | stat_expr e =>
                  nstring_of_expr e i +++ ^";"
                | stat_label lbl s =>
                  ^lbl +++ ^":" +++ nstring_of_stat s i
                | stat_block l =>
                  let seq :=
                      List.map (fun s => nstring_of_stat s (i+1)) l
                  in
                  ^"{" +++ eol +++
                      nstring_concat (^";" +++ eol) seq +++ eol +++
                      indent i +++ ^"}"
                | stat_var_decl l =>
                  let decls :=
                      List.map
                        (fun (x_e_opt: string * option expr) =>
                           let (x, e_opt) := x_e_opt in
                           ^"var " +++ ^x +++
                            match e_opt with
                            | Some e =>
                              ^" = " +++ nstring_of_expr e (i+1)
                            | None => ^""
                            end
                        )
                        l
                  in
                  nstring_concat (^";" +++ eol) decls
                | stat_let_decl l =>
                  let decls :=
                      List.map
                        (fun (x_e_opt: string * option expr) =>
                           let (x, e_opt) := x_e_opt in
                           ^"let " +++ ^x +++
                            match e_opt with
                            | Some e =>
                              ^" = " +++ nstring_of_expr e (i+1)
                            | None => ^""
                            end
                        )
                        l
                  in
                  nstring_concat (^";" +++ eol) decls
                | stat_if e s1 s2_opt =>
                  ^"if (" +++ nstring_of_expr e (i+1) +++ ^") {" +++ eol +++
                   nstring_of_stat s1 (i+1) +++ eol +++
                   indent i +++ ^"} else {" +++ eol +++
                   match s2_opt with
                   | Some s2 => nstring_of_stat s2 (i+1) +++ eol
                   | None => ^""
                   end +++
                   indent i +++ ^"}"
                (* | stat_do_while : label_set -> stat -> expr -> stat *)
                (* | stat_while : label_set -> expr -> stat -> stat *)
                (* | stat_with : expr -> stat -> stat *)
                (* | stat_throw : expr -> stat *)
                | stat_return None =>
                  ^"return ;"
                | stat_return (Some e) =>
                  ^"return " +++ (nstring_of_expr e (i+1)) +++ ^";"
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
                           ^x +++
                             match e1_opt with
                             | None => ^""
                             | Some e1 => ^" = " +++ nstring_of_expr e1 (i+1)
                             end)
                        vars
                  in
                  (* lbl +++ *) (* TODO: print labels *)
                  ^"for (" +++
                   ^"var " +++ comma_list decls +++ ^"; " +++
                   match e2_opt with
                   | Some e2 => nstring_of_expr e2 (i+1)
                   | None => ^""
                   end +++ ^"; " +++
                   match e3_opt with
                   | Some e3 => nstring_of_expr e3 (i+1)
                   | None => ^""
                   end +++ ^") {" +++ eol +++
                   nstring_of_stat s (i+1) +++ eol +++
                   indent i +++ ^"}" +++ eol
                (* | stat_for_in : label_set -> expr -> expr -> stat -> stat (* Note: for (e1 in e2) stat *) *)
                | stat_for_let lbl vars e2_opt e3_opt s =>
                  (* Note: for (var ...; e2; e3) stat *)
                  let decls :=
                      List.map
                        (fun (decl: (string * option expr)) =>
                           let (x, e1_opt) := decl in
                           ^x +++
                             match e1_opt with
                             | None => ^""
                             | Some e1 => ^" = " +++ nstring_of_expr e1 (i+1)
                             end)
                        vars
                  in
                  (* lbl +++ *) (* TODO: print labels *)
                  ^"for (" +++
                   ^"let " +++ comma_list decls +++ ^"; " +++
                   match e2_opt with
                   | Some e2 => nstring_of_expr e2 (i+1)
                   | None => ^""
                   end +++ ^"; " +++
                   match e3_opt with
                   | Some e3 => nstring_of_expr e3 (i+1)
                   | None => ^""
                   end +++ ^") {" +++ eol +++
                   nstring_of_stat s (i+1) +++ eol +++
                   indent i +++ ^"}" +++ eol
                (* | stat_for_in : label_set -> expr -> expr -> stat -> stat (* Note: for (e1 in e2) stat *) *)
                | stat_for_in_var lbl x e1_opt e2 s =>
                  (*  Note: for (var x [= e1] in e2) stat *)
                  (* lbl +++ *) (* TODO: print labels *)
                  ^"for (var " +++ ^x +++
                   match e1_opt with
                   | Some e => ^" = " +++ nstring_of_expr e (i+1)
                   | None => ^""
                   end +++
                   ^" in " +++ nstring_of_expr e2 (i+1)  +++ ^") {" +++ eol +++
                   nstring_of_stat s (i+1) +++ eol +++
                   indent i +++ ^"}" +++ eol
                | stat_for_in_let lbl x e1_opt e2 s =>
                  (*  Note: for (var x [= e1] in e2) stat *)
                  (* lbl +++ *) (* TODO: print labels *)
                  ^"for (let " +++ ^x +++
                   match e1_opt with
                   | Some e => ^" = " +++ nstring_of_expr e (i+1)
                   | None => ^""
                   end +++
                   ^" in " +++ nstring_of_expr e2 (i+1)  +++ ^") {" +++ eol +++
                   nstring_of_stat s (i+1) +++ eol +++
                   indent i +++ ^"}" +++ eol
                (* | stat_debugger : stat *)
                (* | stat_switch : label_set -> expr -> switchbody -> stat *)
                | _ => ^"XXX TODO XXX"
                end

  with nstring_of_element
         (e: element)
         (i: nat) (* indentation level *)
         { struct e }
       : nstring :=
         match e with
         | element_stat s =>
           nstring_of_stat s i
         | element_func_decl f params body =>
           eol +++ indent i
               +++ ^"function " +++ ^f +++ ^"(" +++ (comma_list_string params) +++ ^") {" +++ eol
               +++ nstring_of_funcbody body (i+1) +++ eol +++ indent i +++ ^"}"
         end

  with nstring_of_prog
         (p: prog)
         (i: nat) (* indentation level *)
         { struct p }
       : nstring :=
         match p with
         | prog_intro _ elems =>
           let elems' := List.map (fun e => nstring_of_element e i) elems in
           nstring_concat eol elems'
         end

  with nstring_of_funcbody
         (body: funcbody)
         (i: nat) (* indentation level *)
         { struct body }
       : nstring :=
         match body with
         | funcbody_intro p _ =>
           nstring_of_prog p i
         end.

  Definition nstring_of_funcdecl
             (f:funcdecl)
             (i: nat) (* indentation level *)
    : nstring :=
    eol +++ indent i
        +++ ^"function " +++ ^ (f.(funcdecl_name)) +++ ^"(" +++ (comma_list_string f.(funcdecl_parameters)) +++ ^") {" +++ eol
    +++ nstring_of_funcbody f.(funcdecl_body) (i+1) +++ eol +++ indent i +++ ^"}"
  .

  Definition nstring_of_method
             (f:funcdecl)
             (i: nat) (* indentation level *)
    : nstring :=
    (* XXX All methods are declare as static *)
    eol +++ indent i +++ ^"static " +++ ^ (f.(funcdecl_name)) +++ ^"(" +++ (comma_list_string f.(funcdecl_parameters)) +++ ^") {" +++ eol
        +++ nstring_of_funcbody f.(funcdecl_body) (i+1) +++ eol +++ indent i +++ ^"}"
  .

  Definition nstring_of_decl(d:topdecl)
    : nstring :=
    match d with
    | strictmode => eol +++ ^"'use strict';"
    | comment c => eol +++ ^"/*" +++ ^c +++ ^"*/"
    | elementdecl fd => nstring_of_element fd 0
    | classdecl cn cd =>
      eol +++ ^"class " +++ ^cn +++ ^"{"
          +++ List.fold_left (fun acc q => nstring_append acc (nstring_of_method q 1)) cd (^ (""%string)) +++ eol
          +++ ^"}"
    | constdecl x e =>
      eol +++ ^"const " +++ ^x +++ ^"=" +++ nstring_of_expr e 0
    end.
End ToString.

Section JavaScriptAsttoJavaScript.

  Definition js_ast_to_js_top (ja:js_ast) : javascript :=
    List.fold_left (fun acc f => nstring_append acc (nstring_of_decl f)) ja (^ (""%string)).

End JavaScriptAsttoJavaScript.
