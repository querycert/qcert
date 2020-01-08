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
Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import Equivalence.

Require Import Utils.
Require Import ForeignData.
Require Import ForeignOperators.
Require Import ForeignToJava.
Require Import JavaSystem.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope nstring_scope.

(** Log functions part of the Ergo Standard Library *)

(** Unary operators *)

(* Axioms *)
Axiom URI_encode : string -> string.
Extract Inlined Constant URI_encode => "(fun x -> Uri_component.encode x)".
Axiom URI_decode : string -> string.
Extract Inlined Constant URI_decode => "(fun x -> Uri_component.decode x)".

Section UriOperators.
  (** Ast *)
  Inductive uri_unary_op :=
  | uop_uri_encode : uri_unary_op
  | uop_uri_decode : uri_unary_op
  .

  Section toString.
    Definition uri_unary_op_tostring (f:uri_unary_op) : string :=
      match f with
      | uop_uri_encode => "uriEncode"
      | uop_uri_decode => "uriDecode"
      end.

  End toString.

  Section toJava.
    Definition cname : nstring := ^"UriComponent".

    (* Code generation *)
    Definition uri_to_java_unary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fu:uri_unary_op)
               (d:java_json) : java_json
      := match fu with
         | uop_uri_encode => mk_java_unary_op0_foreign cname (^"uriEncode") d
         | uop_uri_decode => mk_java_unary_op0_foreign cname (^"uriDecode") d
         end.

  End toJava.

  Section toEJson.
    Inductive ejson_uri_runtime_op :=
    | EJsonRuntimeUriEncode
    | EJsonRuntimeUriDecode
    .

    Definition ejson_uri_runtime_op_tostring op : string :=
      match op with
      | EJsonRuntimeUriEncode => "uriEncode"
      | EJsonRuntimeUriDecode => "uriDecode"
      end.

  End toEJson.
End UriOperators.
