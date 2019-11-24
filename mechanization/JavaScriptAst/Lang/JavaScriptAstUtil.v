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
Require Import Utils.
Require Import CommonRuntime.
Require Import JsAst.JsSyntax.
Require Import JavaScriptAst.

Section JavaScriptAstUtil.
  Import ListNotations.

  Definition empty_array := expr_array nil.

  Definition array_push e1 e2 :=
    (* use [array_proto_push_function_object] ? *)
    expr_call (expr_member e1 "push") [ e2 ].

  Definition array_get e1 e2 :=
    expr_access e1 e2.

  Definition object_hasOwnProperty e1 e2 :=
    expr_call (expr_member e1 "hasOwnProperty") [ e2 ].

  Definition object_toString e1 :=
    expr_call (expr_member e1 "toString") [ ].

  (** Runtime  functions *)

  Definition brands_to_js_ast sl : expr :=
    expr_array
      (List.map
         (fun s => Some (expr_literal (literal_string s)))
         sl).

  Definition sortCriteria_to_js_ast (sc: string * SortDesc) :=
    let (lbl, c) := sc in
    match c with
    | Ascending =>
      expr_object
        [ (propname_identifier "asc", propbody_val (expr_literal (literal_string lbl))) ]
    | Descending =>
      expr_object
        [ (propname_identifier "desc", propbody_val (expr_literal (literal_string lbl))) ]
    end.

  Definition sortCriterias_to_js_ast (scl: SortCriterias) :=
    expr_array
      (List.map
         (fun sc => Some (sortCriteria_to_js_ast sc))
         scl).

  Definition call_js_function (f: string) (args: list expr) : expr:= (* TODO: review *)
    expr_call (expr_identifier f) args.

  Definition call_runtime := call_js_function.

  Fixpoint json_to_js_ast (json: json) : expr :=
    match json with
    | jnull => expr_literal literal_null
    | jnumber n =>
      expr_literal (literal_number n)
    | jbool b =>
      expr_literal (literal_bool b)
    | jstring s =>
      expr_literal (literal_string s)
    | jarray a =>
      let a :=
          List.map
            (fun v => Some (json_to_js_ast v))
            a
      in
      expr_array a
    | jobject o =>
      expr_object
        (List.map
           (fun (prop: (string * JSON.json)) =>
              let (x, v) := prop in
              (propname_identifier x, propbody_val (json_to_js_ast v)))
           o)
    end.

End JavaScriptAstUtil.

