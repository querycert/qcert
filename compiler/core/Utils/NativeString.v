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

Section NativeString.
  Parameter nstring : Set.
  Parameter nstring_quote : string -> nstring.
  Parameter nstring_unquote : nstring -> string.
  Parameter nstring_append : nstring -> nstring -> nstring.
  Parameter nstring_flat_map : (Ascii.ascii -> nstring) -> nstring -> nstring.
  Parameter nstring_map :  (Ascii.ascii -> Ascii.ascii) -> nstring -> nstring.

  Definition nstrint_multi_append {A} separator (f:A -> nstring) (elems:list A) : nstring :=
    match elems with
    | nil => nstring_quote EmptyString
    | e :: elems' => fold_left (fun acc e => nstring_append (nstring_append acc separator) (f e)) elems' (f e)
    end.

  Fixpoint nstring_concat (sep : nstring) (ls : list nstring) : nstring :=
    match ls with
    | nil => nstring_quote EmptyString
    | x :: nil => x
    | x :: (_ :: _) as xs => nstring_append (nstring_append x sep) (nstring_concat sep xs)
    end.

  Definition nstring_map_concat {A} (separator:nstring) (f:A -> nstring) (elems:list A) : nstring :=
    match elems with
    | nil => nstring_quote EmptyString
    | e :: elems' =>
      fold_left (fun acc e => nstring_append (nstring_append acc separator) (f e)) elems' (f e)
    end.

End NativeString.

Declare Scope nstring_scope.

Notation "^ e" := (nstring_quote e) (left associativity, at level 40) : nstring_scope.
Notation "& e" := (nstring_unquote e) (left associativity, at level 40) : nstring_scope.
Notation "e1 +++ e2" := (nstring_append e1 e2) (right associativity, at level 70): nstring_scope.

Extract Constant nstring => "string".
Extract Constant nstring_quote => "(fun s1 -> Util.string_of_char_list s1)".
Extract Constant nstring_unquote => "(fun s1 -> Util.char_list_of_string s1)".
Extract Constant nstring_append => "(fun s1 s2 -> s1 ^ s2)".
Extract Constant nstring_flat_map => "(fun f s -> Util.flat_map_string f s)".
Extract Constant nstring_map => "(fun f s -> Util.map_string f s)".
