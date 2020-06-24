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

open CalendarLib

(** Misc *)
let undefined_error op =
  raise (Failure ("Operation " ^ op ^ " not defined in REPL"))

(** Interval *)
type period = Date.Period.t
let period_eq (d1:period) (d2:period) : bool = Date.Period.equal d1 d2
let period_to_string (x:period) : char list = Util.char_list_of_string "_" (* XXX To be figured out *)
let period_from_string (x:char list) : period = undefined_error "period_from_string"
    
(** Date *)
type date = Date.t

let date_to_string (d:date) : char list = Util.char_list_of_string (Printer.Date.sprint "%Y-%-m-%-d" d)
let date_from_string (x:char list) : date =
  begin try
    Printer.Date.from_fstring "%Y-%m-%d" (Util.string_of_char_list x)
  with
  | _ -> Date.make 1 1 1
  end
let date_from_parts y m d =
  Date.make y m d

(** Comparisons *)
let date_eq (x1:date) (x2:date) : bool = Date.compare x1 x2 = 0
let date_neq (x1:date) (x2:date) : bool = Date.compare x1 x2 != 0
let date_lt (x1:date) (x2:date) : bool = Date.compare x1 x2 < 0
let date_gt (x1:date) (x2:date) : bool = Date.compare x1 x2 > 0
let date_le (x1:date) (x2:date) : bool = let c = Date.compare x1 x2 in c < 0 || c = 0
let date_ge (x1:date) (x2:date) : bool = let c = Date.compare x1 x2 in c > 0 || c = 0

(** Get Components *)
let get_year (x:date) : int = Date.year x
let get_month (x:date) : int = Date.int_of_month (Date.month x)
let get_day (x:date) : int = Date.day_of_month x

(** Set Components *)
let set_year (x:date) (z:int) : date = Date.make (get_year x) (get_month x) z
let set_month (x:date) (z:int) : date = Date.make (get_year x) z (get_day x)
let set_day (x:date) (z:int) : date = Date.make (get_year x) (get_month x) z

(** Arithmetics *)
let between (x1:date) (x2:date) : period = Date.sub x1 x2
let plus (x1:date) (d1:period) : date = Date.add x1 d1
let minus (x1:date) (d1:period) : date = Date.rem x1 d1

