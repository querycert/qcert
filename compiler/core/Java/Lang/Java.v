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

Section Java.
  (** Java programs are in serialized form *)
  Definition java := string.
  
  (* XXX Those should be turned into a kind of AST *)
  Section Ast.
    (* data of this type is a java expression that constructs a json element *)
    Inductive java_json : Set
      := mk_java_json : string -> java_json.

    Definition from_java_json (obj:java_json)
      := match obj with
         | mk_java_json s => s
         end.

    (* Given a list of strings that construct objects, create a JsonArray holding them *)
    Definition mk_java_json_array (l:list java_json) : java_json
      := mk_java_json ("RuntimeUtils.createJsonArray"
                         ++ string_bracket "(" (map_concat ", " from_java_json l) ")").

    Definition mk_java_json_object (quotel:string) (l:list (string*java_json)) : java_json
      := mk_java_json ("new RuntimeUtils.JsonObjectBuilder()" 
                         ++ (map_concat ""
                                        (fun elem =>
                                           string_bracket
                                             ".add("
                                             (quotel ++ (fst elem) ++ quotel ++ ", " ++
                                                     (from_java_json (snd elem)))
                                             ")") l)
                         ++ ".toJsonObject()").

    Definition mk_java_json_primitive (obj:string) : java_json
      := mk_java_json ("new JsonPrimitive(" ++ obj ++ ")").

    Definition mk_java_json_string quotel (s:string)
      := mk_java_json_primitive
           (string_bracket quotel s quotel).    

    Definition java_json_NULL : java_json
      := mk_java_json "JsonNull.INSTANCE".
 
    Definition mk_java_json_nat quotel n : java_json
      := mk_java_json_object quotel
                             [("$nat"%string, (mk_java_json_primitive (Z_to_string10 n)))].

    Definition mk_java_json_number n : java_json
      := mk_java_json_primitive (float_to_string n).

    Definition mk_java_json_bool (b:bool) : java_json
      := mk_java_json_primitive 
           (if b then "true" else "false").

    Definition mk_java_string (s:string) : string
      := quotel_double ++ s ++ quotel_double.

    Definition mk_java_call (cname:string) (mname:string) (el:list java_json) : java_json
      := mk_java_json
           (cname
              ++ "." ++ mname ++ "(" ++ (String.concat ", " (map from_java_json el)) ++ ")").
    
    Definition mk_java_unary_op0 (opname:string) (e:java_json) : java_json
      := mk_java_call "UnaryOperators" opname [e].

    Definition mk_java_unary_op1 (opname:string) (s:string) (e:java_json) : java_json
      := mk_java_call "UnaryOperators" opname [mk_java_json s;e].

    Definition mk_java_unary_opn (opname:string) (sn:list string) (e:java_json) : java_json
      := mk_java_call "UnaryOperators" opname (app (map mk_java_json sn) [e]).

    Definition mk_java_binary_op0 (opname:string) (e1 e2:java_json) : java_json
      := mk_java_call "BinaryOperators" opname [e1;e2].

    Definition mk_java_binary_opn (opname:string) (sn:list string) (e1 e2:java_json) : java_json
      := mk_java_call "BinaryOperators" opname (app (map mk_java_json sn) [e1;e2]).

    Definition mk_java_unary_op0_foreign (cname:string) (opname:string) (e:java_json) : java_json
      := mk_java_call cname opname [e].

    Definition mk_java_unary_op1_foreign (cname:string) (opname:string) (s:string) (e:java_json) : java_json
      := mk_java_call cname opname [mk_java_json s;e].

    Definition mk_java_binary_op0_foreign (cname:string) (opname:string) (e1 e2:java_json) : java_json
      := mk_java_call cname opname [e1;e2].

    Definition mk_java_binary_opn_foreign (cname:string) (opname:string) (sn:list string) (e1 e2:java_json) : java_json
      := mk_java_call cname opname (app (map mk_java_json sn) [e1;e2]).

    Definition mk_java_collection(typ:string) (s:list string) : string
      := "new RuntimeUtils.CollectionBuilder<"
           ++ typ ++ ">(" ++ (nat_to_string10 (Datatypes.length s)) ++ ")"
           ++ map_concat "" (fun elem => (".add(" ++ elem ++ ")")%string) s
           ++ ".result()".

    Definition mk_java_string_collection(s:list string) : string
      := mk_java_collection "String" (map mk_java_string s).

    Definition mk_java_sort_criteria (quotel:string) (sc:SortCriteria) : string :=
      match sc with
      | (key, Ascending) =>
        "RuntimeUtils.sortEntry(" ++ quotel ++ key ++ quotel ++ "," ++ "RuntimeUtils.SortDesc.ASC" ++ ")"
      | (key, Descending) =>
        "RuntimeUtils.sortEntry(" ++ key ++ "," ++ "RuntimeUtils.SortDesc.DESC" ++ ")"
      end.
    
    Definition mk_java_sort_criterias (quotel:string) (scl:SortCriterias) : string :=
      "new Object[]{" ++ map_concat ", " (mk_java_sort_criteria quotel) scl ++ "}".

  End Ast.
End Java.
