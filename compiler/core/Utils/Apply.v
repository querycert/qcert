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

(** This module provides support for operators application. *)

Require Import List.

Section Apply.
  Context {A:Set}.

  Definition apply_unary (f: A -> option A) (dl: list A) : option A :=
    match dl with
    | d :: nil => f d
    | _ => None
    end.
  Definition apply_binary (f: A -> A -> option A) (dl: list A) : option A :=
    match dl with
    | d1 :: d2 :: nil => f d1 d2
    | _ => None
    end.
  Definition apply_ternary (f: A -> A -> A -> option A) (dl: list A) : option A :=
    match dl with
    | d1 :: d2 :: d3 :: nil => f d1 d2 d3
    | _ => None
    end.
End Apply.

