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

(** Interval *)
type period
val period_eq : period -> period -> bool
val period_to_string : period -> string
val period_from_string : string -> period

(** Date *)
type date

val date_to_string : date -> string
val date_from_string : string -> date
val date_from_parts : int -> int -> int -> date

(** Comparisons *)
val date_eq : date -> date -> bool
val date_neq : date -> date -> bool
val date_lt : date -> date -> bool
val date_gt : date -> date -> bool
val date_le : date -> date -> bool
val date_ge : date -> date -> bool

(** Get Components *)
val get_day : date -> int
val get_month : date -> int
val get_year : date -> int

(** Set Components *)
val set_day : date -> int -> date
val set_month : date -> int -> date
val set_year : date -> int -> date

(** Arithmetics *)
val between : date -> date -> period
val plus : date -> period -> date
val minus : date -> period -> date

