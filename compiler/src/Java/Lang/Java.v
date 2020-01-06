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
Require Import Utils.

Import ListNotations.
Local Open Scope nstring_scope.

Section Java.
  (** Java programs are in serialized form *)
  Definition java := nstring.
  
  (* XXX Those should be turned into a kind of AST *)
  Section Ast.
    (* data of this type is a java expression that constructs a json element *)
    Inductive java_json : Set
      := mk_java_json : nstring -> java_json.

    Definition from_java_json (obj:java_json)
      := match obj with
         | mk_java_json s => s
         end.

    (* Given a list of strings that construct objects, create a JsonArray holding them *)
    Definition mk_java_json_array (l:list java_json) : java_json
      := mk_java_json (^"RuntimeUtils.createJsonArray"
                          +++ nstring_bracket (^"(") (nstring_map_concat (^", ") from_java_json l) (^")")).

    Definition mk_java_json_object (quotel:nstring) (l:list (nstring*java_json)) : java_json
      := mk_java_json (^"new RuntimeUtils.JsonObjectBuilder()" 
                          +++ (nstring_map_concat (^"")
                                                  (fun elem =>
                                                     nstring_bracket
                                                       (^".add(")
                                                       (quotel +++ (fst elem) +++ quotel +++ (^", ") +++
                                                               (from_java_json (snd elem)))
                                                       (^")")) l)
                          +++ ^".toJsonObject()").
               
    Definition mk_java_json_primitive (obj:nstring) : java_json
      := mk_java_json (^"new JsonPrimitive(" +++ obj +++ ^")").

    Definition mk_java_json_string quotel (s:nstring)
      := mk_java_json_primitive
           (nstring_bracket quotel s quotel).    

    Definition java_json_NULL : java_json
      := mk_java_json (^"JsonNull.INSTANCE").
 
    Definition mk_java_json_nat quotel n : java_json
      := mk_java_json_object quotel
                             [(^"$nat", (mk_java_json_primitive (^Z_to_string10 n)))].

    Definition mk_java_json_number n : java_json
      := mk_java_json_primitive (^float_to_string n).

    Definition mk_java_json_bool (b:bool) : java_json
      := mk_java_json_primitive 
           (if b then ^"true" else ^"false").

    Definition mk_java_string (s:nstring) : nstring
      := nquotel_double +++ s +++ nquotel_double.

    Definition mk_java_unary_op0 (opname:nstring) (e:java_json) : java_json
      := mk_java_json (^"UnaryOperators." +++ opname +++ ^"(" +++ (from_java_json e) +++ ^")").

    Definition mk_java_unary_op1 (opname:nstring) (s:nstring) (e:java_json) : java_json :=
      mk_java_json
        (^"UnaryOperators." +++ opname +++ ^"(" +++ s +++ ^", " +++ (from_java_json e) +++ ^")").

    Definition mk_java_unary_opn (opname:nstring) (sn:list nstring) (e:java_json) : java_json
      := mk_java_json
           (^"UnaryOperators."
              +++ opname +++ ^"(" +++ (nstring_concat (^", ") (List.app sn [(from_java_json e)])) +++ ^")").

    Definition mk_java_collection(typ:nstring) (s:list nstring) : nstring :=
      ^"new RuntimeUtils.CollectionBuilder<"
         +++ typ +++ ^">(" +++ (^nat_to_string10 (Datatypes.length s)) +++ (^")")
                           +++ nstring_map_concat (^"") (fun elem => ^".add(" +++ elem +++ ^")") s
                           +++ ^".result()".

    Definition mk_java_string_collection(s:list nstring) : nstring :=
      mk_java_collection (^"String") (map mk_java_string s).

    Definition mk_java_binary_op0 (opname:nstring) (e1 e2:java_json) : java_json :=
      mk_java_json (^"BinaryOperators."
                       +++ opname +++ ^"(" +++ (from_java_json e1) +++ ^", " +++ (from_java_json e2) +++ ^")").
  End Ast.
End Java.

