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

(* This module contains pretty-printers for intermediate languages *)

open Format
module Hack = Compiler


(* Character sets *)

type charkind =
  | Ascii
  | Greek

type pretty_config =
    { mutable margin : int;
      mutable charset : charkind }

let make_pretty_config greek margin =
  { margin = margin;
    charset = if greek then Greek else Ascii }

let default_pretty_config () =
  { margin = 120;
    charset = Greek }

let set_ascii conf () = conf.charset <- Ascii
let set_greek conf () = conf.charset <- Greek
let get_charset conf = conf.charset
let get_charset_bool conf =
  match conf.charset with
  | Greek -> true
  | Ascii -> false

let set_margin conf i = conf.margin <- i
let get_margin conf = conf.margin

(* Charset dependent config *)
(* Note: This should remain within the module *)

type nra_sym =
    { chi: (string*int);
      chie: (string*int);
      djoin: (string*int);
      times: (string*int);
      sigma: (string*int);
      langle: (string*int);
      rangle: (string*int);
      llangle: (string*int);
      rrangle: (string*int);
      lpangle: (string*int);
      rpangle: (string*int);
      bars: (string*int);
      lrarrow: (string*int);
      sqlrarrow: (string*int);
      lfloor: (string*int);
      rfloor: (string*int);
      circ: (string*int);
      circe: (string*int);
      sharp: (string*int);
      pi: (string*int);
      cup: (string*int);
      vee: (string*int);
      wedge: (string*int);
      leq: (string*int);
      sin: (string*int);
      neg: (string*int);
      top: (string*int);
      bot: (string*int) }

let textsym =
  { chi = ("Map", 3);
    chie = ("Map^e", 5);
    djoin = ("DJoin", 5);
    times = ("x", 1);
    sigma = ("Select", 6);
    langle = ("<", 1);
    rangle = (">", 1);
    llangle = ("<<", 2);
    rrangle = (">>", 2);
    lpangle = ("<|", 2);
    rpangle = ("|>", 2);
    bars = ("||", 2);
    lrarrow = ("<->", 3);
    sqlrarrow = ("[<->]", 5);
    lfloor = ("[", 1);
    rfloor = ("]", 1);
    circ = ("o", 1);
    circe = ("o^e", 3);
    sharp = ("#", 1);
    pi = ("Project", 7);
    cup = ("U",1);
    vee = ("\\/",2);
    wedge = ("/\\",2);
    leq = ("<=",2);
    sin = ("{in}",4);
    neg = ("~",1);
    top = ("Top",3);
    bot = ("Bot",3) }
let greeksym =
  { chi = ("χ", 1);
    chie = ("χᵉ", 2);
    djoin = ("⋈ᵈ", 2);
    times = ("×", 1);
    sigma = ("σ", 1);
    langle = ("⟨", 1);
    rangle = ("⟩", 1);
    llangle = ("⟪", 1);
    rrangle = ("⟫", 1);
    lpangle = ("⟬", 1);
    rpangle = ("⟭", 1);
    bars = ("∥", 1);
    lrarrow = ("↔", 1);
    sqlrarrow = ("[↔]", 3);
    lfloor = ("⌊", 1);
    rfloor = ("⌋", 1);
    circ = ("∘", 1);
    circe = ("∘ᵉ", 2);
    sharp = ("♯", 1);
    pi = ("π", 1);
    cup = ("∪",1);
    vee = ("∨",1);
    wedge = ("∧",1);
    leq = ("≤",1);
    sin = ("∈",1);
    neg = ("¬",1);
    top = ("⊤",1);
    bot = ("⊥",1) }

(* Data PP *)

let timescale_as_string ts =
  match ts with
  | Hack.Ts_second -> "SECOND"
  | Hack.Ts_minute ->  "MINUTE"
  | Hack.Ts_hour -> "HOUR"
  | Hack.Ts_day -> "DAY"
  | Hack.Ts_week -> "WEEK"
  | Hack.Ts_month -> "MONTH"
  | Hack.Ts_year -> "YEAR"

let pretty_timescale ff ts =
  fprintf ff "%s" (timescale_as_string ts)

let string_of_foreign_data (fd:Hack.enhanced_data) : string =
  match fd with
  | Hack.Enhancedfloat f -> string_of_float f
  | Hack.Enhancedstring s -> "S\"" ^ s ^ "\""
  | Hack.Enhancedtimescale ts -> timescale_as_string ts
  | Hack.Enhancedtimeduration td -> raise Not_found
  | Hack.Enhancedtimepoint tp -> raise Not_found

let foreign_data_of_string s =
  try
    Hack.Enhancedfloat (float_of_string s)
  with
  | Failure _ ->
      begin
	match s with
	| "SECOND" -> Hack.Enhancedtimescale Hack.Ts_second
	| "MINUTE" -> Hack.Enhancedtimescale Hack.Ts_minute
	| "HOUR" -> Hack.Enhancedtimescale Hack.Ts_hour
	| "DAY" -> Hack.Enhancedtimescale Hack.Ts_day
	| "WEEK" -> Hack.Enhancedtimescale Hack.Ts_week
	| "MONTH" -> Hack.Enhancedtimescale Hack.Ts_month
	| "YEAR" -> Hack.Enhancedtimescale Hack.Ts_year
	| _ ->
	    try
	      if (s.[0] = 'S' && s.[1] = '"')
	      then
		Hack.Enhancedstring (String.sub s 2 ((String.length s) - 3))
	      else
		raise Not_found
	    with
	    | _ ->
		raise Not_found
      end

let pretty_foreign_data ff fd =
  match fd with
  | Hack.Enhancedfloat f -> fprintf ff "%f" f
  | Hack.Enhancedstring s -> fprintf ff "S\"%s\"" s
  | Hack.Enhancedtimescale ts -> pretty_timescale ff ts
  | Hack.Enhancedtimeduration td -> raise Not_found
  | Hack.Enhancedtimepoint tp -> raise Not_found

let rec pretty_names ff nl =
  match nl with
    [] -> ()
  | n :: [] -> fprintf ff "%s" (Util.string_of_char_list n)
  | n :: nl' -> fprintf ff "%s,@ %a" (Util.string_of_char_list n) pretty_names nl'

let rec pretty_data ff d =
  match d with
  | Hack.Dunit -> fprintf ff "null"
  | Hack.Dnat n -> fprintf ff "%d" n
  | Hack.Dbool true -> fprintf ff "true"
  | Hack.Dbool false -> fprintf ff "false"
  | Hack.Dstring s -> fprintf ff "\"%s\"" (Util.string_of_char_list s)
  | Hack.Dcoll dl -> fprintf ff "{@[<hv 0>%a@]}" pretty_coll dl
  | Hack.Drec rl -> fprintf ff "[@[<hv 0>%a@]]" pretty_rec rl
  | Hack.Dleft d -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@]" pretty_data d
  | Hack.Dright d -> fprintf ff "@[<hv 2>right {@,%a@;<0 -2>}@]" pretty_data d
  | Hack.Dbrand (brands,d) -> fprintf ff "@[<hv 2>brands [@[<hv 0>%a@]] {@,%a@;<0 -2>}@]"
				      pretty_names brands
				      pretty_data d
  | Hack.Dforeign fd -> pretty_foreign_data ff (Obj.magic fd)

and pretty_coll ff dl =
  match dl with
    [] -> ()
  | d :: [] -> fprintf ff "%a" pretty_data d
  | d :: dl' -> fprintf ff "%a,@ %a" pretty_data d pretty_coll dl'

and pretty_rec ff rl =
  match rl with
    [] -> ()
  | (ra,rd) :: [] -> fprintf ff "%s : %a" (Util.string_of_char_list ra) pretty_data rd
  | (ra,rd) :: rl' -> fprintf ff "%s : %a;@ %a" (Util.string_of_char_list ra) pretty_data rd pretty_rec rl'

(* Ops PP *)

let pretty_sym ff sym =
    begin
      let (asym,asize) = sym in
      pp_print_as ff asize asym
    end

let pretty_squared_names sym ff nl =
  fprintf ff "%a@[<hv 0>%a@]%a" pretty_sym sym.lfloor pretty_names nl pretty_sym sym.rfloor

let rec pretty_sharp sym ff name =
  fprintf ff "%a%s" pretty_sym sym.sharp name

(* pouter: precedence of enclosing expression.
   pinner: precedence of current expression.
   rule: parenthesize if pouter > pinner *)
let pretty_infix_exp pouter pinner sym callb thissym ff a1 a2 =
  if pouter > pinner
  then
    fprintf ff "@[<hov 0>(%a@ %a@ %a)@]" (callb pinner sym) a1 pretty_sym thissym (callb pinner sym) a2
  else
    fprintf ff "@[<hov 0>%a@ %a@ %a@]" (callb pinner sym) a1 pretty_sym thissym (callb pinner sym) a2

(* resets precedence back to 0 *)
let pretty_unary_exp sym callb thisname ff a =
  fprintf ff "@[<hv 2>%a(@,%a@;<0 -2>)@]" (pretty_sharp sym) thisname (callb 0 sym) a

let string_of_unarith ua =
  match ua with
  | Hack.ArithAbs -> "abs"
  | Hack.ArithLog2 -> "log2"
  | Hack.ArithSqrt -> "sqrt"

let unarith_of_string s =
  match s with
  | "abs" -> Hack.ArithAbs
  | "log2" -> Hack.ArithLog2
  | "sqrt" -> Hack.ArithSqrt
  | _ -> raise Not_found

let pretty_unarith p sym callb ff ua a =
  match ua with
  | Hack.ArithAbs -> pretty_unary_exp sym callb "abs" ff a
  | Hack.ArithLog2 -> pretty_unary_exp sym callb "log2" ff a
  | Hack.ArithSqrt -> pretty_unary_exp sym callb "sqrt" ff a

let string_of_foreign_unop fu : string =
  match fu with
  | Hack.Enhanced_unary_float_op Hack.Uop_float_neg -> "Fneg"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_sqrt -> "Fsqrt"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_exp -> "Fexp"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_log -> "Flog"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_log10 -> "Flog10"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_of_int -> "Fof_int"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_ceil -> "Fceil"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_floor -> "floor"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_truncate -> "Ftruncate"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_abs -> "Fabs"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_sum -> "Fsum"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_arithmean -> "Favg"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_listmin -> "Flist_min"
  | Hack.Enhanced_unary_float_op Hack.Uop_float_listmax -> "Flist_max"
  | Hack.Enhanced_unary_time_op Hack.Uop_time_to_scale -> "TimeToScale"
  | Hack.Enhanced_unary_time_op Hack.Uop_time_from_string -> "TimeFromString"
  | Hack.Enhanced_unary_time_op Hack.Uop_time_duration_from_string -> "TimeDurationFromString"

let foreign_unop_of_string s =
  match s with
  | "Fneg" -> Hack.Enhanced_unary_float_op Hack.Uop_float_neg
  | "Fsqrt" -> Hack.Enhanced_unary_float_op Hack.Uop_float_sqrt
  | "Fexp" -> Hack.Enhanced_unary_float_op Hack.Uop_float_exp
  | "Flog" -> Hack.Enhanced_unary_float_op Hack.Uop_float_log
  | "Flog10" -> Hack.Enhanced_unary_float_op Hack.Uop_float_log10
  | "Fof_int" -> Hack.Enhanced_unary_float_op Hack.Uop_float_of_int
  | "Fceil" -> Hack.Enhanced_unary_float_op Hack.Uop_float_ceil
  | "floor" -> Hack.Enhanced_unary_float_op Hack.Uop_float_floor
  | "Ftruncate" -> Hack.Enhanced_unary_float_op Hack.Uop_float_truncate
  | "Fabs" -> Hack.Enhanced_unary_float_op Hack.Uop_float_abs
  | "Fsum" -> Hack.Enhanced_unary_float_op Hack.Uop_float_sum
  | "Favg" -> Hack.Enhanced_unary_float_op Hack.Uop_float_arithmean
  | "Flist_min" -> Hack.Enhanced_unary_float_op Hack.Uop_float_listmin
  | "Flist_max" -> Hack.Enhanced_unary_float_op Hack.Uop_float_listmax
  | "TimeToScale" -> Hack.Enhanced_unary_time_op Hack.Uop_time_to_scale
  | "TimeFromString" -> Hack.Enhanced_unary_time_op Hack.Uop_time_from_string
  | "TimeDurationFromString" -> Hack.Enhanced_unary_time_op Hack.Uop_time_duration_from_string
  | _ -> raise Not_found

let pretty_foreign_unop p sym callb ff fu a =
  match fu with
  | Hack.Enhanced_unary_float_op Hack.Uop_float_neg -> pretty_unary_exp sym callb "Fneg" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_sqrt -> pretty_unary_exp sym callb "Fsqrt" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_exp -> pretty_unary_exp sym callb "Fexp" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_log -> pretty_unary_exp sym callb "Flog" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_log10 -> pretty_unary_exp sym callb "Flog10" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_of_int -> pretty_unary_exp sym callb "Fof_int" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_ceil -> pretty_unary_exp sym callb "Fceil" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_floor -> pretty_unary_exp sym callb "floor" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_truncate -> pretty_unary_exp sym callb "Ftruncate" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_abs -> pretty_unary_exp sym callb "Fabs" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_sum -> pretty_unary_exp sym callb "Fsum" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_arithmean -> pretty_unary_exp sym callb "Favg" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_listmin -> pretty_unary_exp sym callb "Flist_min" ff a
  | Hack.Enhanced_unary_float_op Hack.Uop_float_listmax -> pretty_unary_exp sym callb "Flist_max" ff a
  | Hack.Enhanced_unary_time_op Hack.Uop_time_to_scale -> pretty_unary_exp sym callb "TimeToScale" ff a
  | Hack.Enhanced_unary_time_op Hack.Uop_time_from_string -> pretty_unary_exp sym callb "TimeFromString" ff a
  | Hack.Enhanced_unary_time_op Hack.Uop_time_duration_from_string -> pretty_unary_exp sym callb "TimeDurationFromString" ff a

let pretty_unop p sym callb ff u a =
  match u with
  | Hack.AIdOp -> pretty_unary_exp sym callb "id" ff a
  | Hack.AUArith ua -> pretty_unarith p sym callb ff ua a
  | Hack.ANeg ->
      if (p > 25)
      then
	fprintf ff "@[<hv 0>%a(%a)@]" pretty_sym sym.neg (callb 0 sym) a
      else
	fprintf ff "@[<hv 0>%a%a@]" pretty_sym sym.neg (callb 25 sym) a
  (* resets precedence back to 0 *)
  | Hack.AColl -> fprintf ff "@[<hv 2>{@,%a@;<0 -2>}@]" (callb 0 sym) a
  | Hack.ACount -> pretty_unary_exp sym callb "count" ff a
  | Hack.AFlatten -> pretty_unary_exp sym callb "flatten" ff a
  | Hack.ALeft -> pretty_unary_exp sym callb "left" ff a
  | Hack.ARight -> pretty_unary_exp sym callb "right" ff a
  (* resets precedence back to 0 *)
  | Hack.ABrand brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "brand" (pretty_squared_names sym) brands (callb 0 sym) a
  (* resets precedence back to 0 *)
  | Hack.ARec att -> fprintf ff "@[<hv 2>[ %s :@ %a ]@]" (Util.string_of_char_list att) (callb 0 sym) a
  | Hack.ADot att ->
      if p > 23
      then fprintf ff "@[<hv 0>(%a.%s)@]" (callb 23 sym) a (Util.string_of_char_list att)
      else fprintf ff "@[<hv 0>%a.%s@]" (callb 23 sym) a (Util.string_of_char_list att)
  (* resets precedence back to 0 *)
  | Hack.ARecRemove att ->
      fprintf ff "@[<hv 0>%a%a%a(%a)@]" pretty_sym sym.neg pretty_sym sym.pi (pretty_squared_names sym) [att] (callb 0 sym) a
  (* resets precedence back to 0 *)
  | Hack.ARecProject atts ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.pi (pretty_squared_names sym) atts (callb 0 sym) a
  | Hack.ADistinct -> pretty_unary_exp sym callb "distinct" ff a
  | Hack.ASum -> pretty_unary_exp sym callb "sum" ff a
  | Hack.AArithMean -> pretty_unary_exp sym callb "avg" ff a
  | Hack.AToString -> pretty_unary_exp sym callb "toString" ff a
  (* resets precedence back to 0 *)
  | Hack.ACast brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "cast" (pretty_squared_names sym) brands (callb p sym) a
  | Hack.AUnbrand ->
      if p > 24
      then fprintf ff "@[<hv 0>(!%a)@]" (callb 24 sym) a
      else fprintf ff "@[<hv 0>!%a@]" (callb 24 sym) a
  | Hack.ASingleton -> pretty_unary_exp sym callb "singleton" ff a
  | Hack.ANumMin -> pretty_unary_exp sym callb "min" ff a
  | Hack.ANumMax -> pretty_unary_exp sym callb "max" ff a
  | Hack.AForeignUnaryOp fu -> pretty_foreign_unop p sym callb ff (Obj.magic fu) a




(* Precedence:
   Higher number means binds tighter

   ID, Env, GetConstant, Const    	             27
   { Op }                  	             26
   not                                       25
   !                       	             24
   .                       	             23
   Op<Op>(Op)              	             22
   #Fun(Op)                	             21

   Binary Ops
   ----------
   nat         bags           bool   string  rec

   min, max    {min}, {max}	       	           20
   *,/,%                      \/       	     [*]   19
   +, -        U, \           /\     ^ 	     [+]   18
   < <=                                	           17
               in                      	           16
   =                       	       	           15

   Infix AlgOp
   -----------
   o^e                                             10
   o                                                9
   ||                                               8
   [<->]                                            7
   <->                                              6
   x                                                5

 *)

let string_of_binarith ba =
  match ba with
  | Hack.ArithPlus -> "plus"
  | Hack.ArithMinus -> "minus"
  | Hack.ArithMult -> "mult"
  | Hack.ArithMin -> "min"
  | Hack.ArithMax -> "max"
  | Hack.ArithDivide -> "divide"
  | Hack.ArithRem -> "rem"

let binarith_of_string s =
  match s with
  | "plus" -> Hack.ArithPlus
  | "minus" -> Hack.ArithMinus
  | "mult" -> Hack.ArithMult
  | "min" -> Hack.ArithMin
  | "max" -> Hack.ArithMax
  | "divide" -> Hack.ArithDivide
  | "rem" -> Hack.ArithRem
  | _ -> raise Not_found

let pretty_binarith p sym callb ff ba a1 a2 =
  match ba with
  | Hack.ArithPlus -> pretty_infix_exp p 18 sym callb ("+",1) ff a1 a2
  | Hack.ArithMinus -> pretty_infix_exp p 18 sym callb ("-",1) ff a1 a2
  | Hack.ArithMult -> pretty_infix_exp p 19 sym callb ("*",1) ff a1 a2
  | Hack.ArithMin -> pretty_infix_exp p 20 sym callb ("min",3) ff a1 a2
  | Hack.ArithMax -> pretty_infix_exp p 20 sym callb ("max",3) ff a1 a2
  | Hack.ArithDivide -> pretty_infix_exp p 19 sym callb ("/",1) ff a1 a2
  | Hack.ArithRem -> pretty_infix_exp p 19 sym callb ("%",1) ff a1 a2

let string_of_foreign_binop fb =
  match fb with
  | Hack.Enhanced_binary_float_op Hack.Bop_float_plus -> "float_plus"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_minus -> "float_minus"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_mult -> "float_mult"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_div -> "float_div"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_pow -> "float_pow"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_min -> "float_min"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_max -> "float_max"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_ne -> "float_ne"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_lt -> "float_lt"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_le -> "float_le"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_gt -> "float_gt"
  | Hack.Enhanced_binary_float_op Hack.Bop_float_ge -> "float_ge"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_as -> "time_as"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_shift -> "time_shift"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_ne -> "time_ne"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_lt -> "time_lt"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_le -> "time_le"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_gt -> "time_gt"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_ge -> "time_ge"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_duration_from_scale -> "time_duration_from_scale"
  | Hack.Enhanced_binary_time_op Hack.Bop_time_duration_between -> "time_duration_between"

let foreign_binop_of_string fb =
  match fb with
  | "float_plus" -> Hack.Enhanced_binary_float_op Hack.Bop_float_plus
  | "float_minus" -> Hack.Enhanced_binary_float_op Hack.Bop_float_minus
  | "float_mult" -> Hack.Enhanced_binary_float_op Hack.Bop_float_mult
  | "float_div" -> Hack.Enhanced_binary_float_op Hack.Bop_float_div
  | "float_pow" -> Hack.Enhanced_binary_float_op Hack.Bop_float_pow
  | "float_min" -> Hack.Enhanced_binary_float_op Hack.Bop_float_min
  | "float_max" -> Hack.Enhanced_binary_float_op Hack.Bop_float_max
  | "float_ne" -> Hack.Enhanced_binary_float_op Hack.Bop_float_ne
  | "float_lt" -> Hack.Enhanced_binary_float_op Hack.Bop_float_lt
  | "float_le" -> Hack.Enhanced_binary_float_op Hack.Bop_float_le
  | "float_gt" -> Hack.Enhanced_binary_float_op Hack.Bop_float_gt
  | "float_ge" -> Hack.Enhanced_binary_float_op Hack.Bop_float_ge
  | "time_as" -> Hack.Enhanced_binary_time_op Hack.Bop_time_as
  | "time_shift" -> Hack.Enhanced_binary_time_op Hack.Bop_time_shift
  | "time_ne" -> Hack.Enhanced_binary_time_op Hack.Bop_time_ne
  | "time_lt" -> Hack.Enhanced_binary_time_op Hack.Bop_time_lt
  | "time_le" -> Hack.Enhanced_binary_time_op Hack.Bop_time_le
  | "time_gt" -> Hack.Enhanced_binary_time_op Hack.Bop_time_gt
  | "time_ge" -> Hack.Enhanced_binary_time_op Hack.Bop_time_ge
  | "time_duration_from_scale" -> Hack.Enhanced_binary_time_op Hack.Bop_time_duration_from_scale
  | "time_duration_between" -> Hack.Enhanced_binary_time_op Hack.Bop_time_duration_between
  | _ -> raise Not_found

let pretty_foreign_binop p sym callb ff fb a1 a2 =
  match fb with
  | Hack.Enhanced_binary_float_op Hack.Bop_float_plus ->
     pretty_infix_exp p 18 sym callb ("F+",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_minus ->
     pretty_infix_exp p 18 sym callb ("F-",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_mult ->
     pretty_infix_exp p 18 sym callb ("F*",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_div ->
     pretty_infix_exp p 18 sym callb ("F/",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_pow ->
     pretty_infix_exp p 18 sym callb ("F^",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_min ->
     pretty_infix_exp p 20 sym callb ("Fmin",3) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_max ->
     pretty_infix_exp p 20 sym callb ("Fmax",3) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_ne ->
     pretty_infix_exp p 18 sym callb ("F!=",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_lt ->
     pretty_infix_exp p 18 sym callb ("F<",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_le ->
     pretty_infix_exp p 18 sym callb ("F<=",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_gt ->
     pretty_infix_exp p 18 sym callb ("F>",1) ff a1 a2
  | Hack.Enhanced_binary_float_op Hack.Bop_float_ge ->
     pretty_infix_exp p 18 sym callb ("F>=",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_as ->
     pretty_infix_exp p 18 sym callb ("Tas",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_shift ->
     pretty_infix_exp p 18 sym callb ("T+",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_ne ->
     pretty_infix_exp p 18 sym callb ("T!=",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_lt ->
     pretty_infix_exp p 18 sym callb ("T<",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_le ->
     pretty_infix_exp p 18 sym callb ("T<=",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_gt ->
     pretty_infix_exp p 18 sym callb ("T>",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_ge ->
     pretty_infix_exp p 18 sym callb ("T>=",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_duration_from_scale ->
     pretty_infix_exp p 18 sym callb ("TD_fs",1) ff a1 a2
  | Hack.Enhanced_binary_time_op Hack.Bop_time_duration_between ->
     pretty_infix_exp p 18 sym callb ("TD_be",1) ff a1 a2

let string_of_binop b =
  match b with
  | Hack.AEq -> "aeq"
  | Hack.AUnion -> "aunion"
  | Hack.AConcat -> "aconcat"
  | Hack.AMergeConcat -> "amergeconcat"
  | Hack.AAnd -> "aand"
  | Hack.AOr -> "aor"
  | Hack.ABArith ba -> string_of_binarith ba
  | Hack.ALt -> "alt"
  | Hack.ALe -> "ale"
  | Hack.AMinus -> "aminus"
  | Hack.AMin -> "amin"
  | Hack.AMax -> "amax"
  | Hack.AContains -> "acontains"
  | Hack.ASConcat -> "asconcat"
  | Hack.AForeignBinaryOp fb -> string_of_foreign_binop (Obj.magic fb)

let pretty_binop p sym callb ff b a1 a2 =
  match b with
  | Hack.AEq -> pretty_infix_exp p 15 sym callb ("=",1) ff a1 a2
  | Hack.AUnion -> pretty_infix_exp p 18 sym callb sym.cup ff a1 a2
  | Hack.AConcat -> pretty_infix_exp p 19 sym callb ("[*]",3) ff a1 a2
  | Hack.AMergeConcat -> pretty_infix_exp p 18 sym callb ("[+]",3) ff a1 a2
  | Hack.AAnd -> pretty_infix_exp p 19 sym callb sym.wedge ff a1 a2
  | Hack.AOr -> pretty_infix_exp p 18 sym callb sym.vee ff a1 a2
  | Hack.ABArith ba -> (pretty_binarith p sym callb) ff ba a1 a2
  | Hack.ALt -> pretty_infix_exp p 17 sym callb ("<",1) ff a1 a2
  | Hack.ALe -> pretty_infix_exp p 17 sym callb sym.leq ff a1 a2
  | Hack.AMinus -> pretty_infix_exp p 18 sym callb ("\\",1) ff a1 a2
  | Hack.AMin -> pretty_infix_exp p 20 sym callb ("{min}",5) ff a1 a2
  | Hack.AMax -> pretty_infix_exp p 20 sym callb ("{max}",5) ff a1 a2
  | Hack.AContains -> pretty_infix_exp p 16 sym callb sym.sin ff a1 a2
  | Hack.ASConcat -> pretty_infix_exp p 18 sym callb ("^",1) ff a1 a2
  | Hack.AForeignBinaryOp fb -> pretty_foreign_binop p sym callb ff (Obj.magic fb) a1 a2


(* NRAEnv PP *)

let rec pretty_nraenv_aux p sym ff a =
  match a with
  | Hack.ANID -> fprintf ff "%s" "ID"
  | Hack.ANConst d -> fprintf ff "%a" pretty_data d
  | Hack.ANBinop (b,a1,a2) -> (pretty_binop p sym pretty_nraenv_aux) ff b a1 a2
  | Hack.ANUnop (u,a1) -> (pretty_unop p sym pretty_nraenv_aux) ff u a1
  | Hack.ANMap (a1,a2) -> pretty_nra_exp p sym sym.chi ff a1 (Some a2)
  | Hack.ANMapConcat (a1,a2) -> pretty_nra_exp p sym sym.djoin ff a1 (Some a2)
  | Hack.ANProduct (a1,a2) -> pretty_infix_exp p 5 sym pretty_nraenv_aux sym.times ff a1 a2
  | Hack.ANSelect (a1,a2) -> pretty_nra_exp p sym sym.sigma ff a1 (Some a2)
  | Hack.ANDefault (a1,a2) -> pretty_infix_exp p 8 sym pretty_nraenv_aux sym.bars ff a1 a2
  | Hack.ANEither (a1,a2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ ID@;<1 -2>with@]@;<1 0>@[<hv 2>| left as ID ->@ %a@]@;<1 0>@[<hv 2>| right as ID ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	 (pretty_nraenv_aux p sym) a1
	 (pretty_nraenv_aux p sym) a2
  | Hack.ANEitherConcat (a1,a2) -> pretty_infix_exp p 7 sym pretty_nraenv_aux sym.sqlrarrow ff a1 a2
  | Hack.ANApp (a1,a2) -> pretty_infix_exp p 9 sym pretty_nraenv_aux sym.circ ff a1 a2
  | Hack.ANGetConstant s -> fprintf ff "Table%a%s%a" pretty_sym sym.lfloor (Util.string_of_char_list s) pretty_sym sym.rfloor
  | Hack.ANEnv -> fprintf ff "%s" "ENV"
  | Hack.ANAppEnv (a1,a2) ->  pretty_infix_exp p 10 sym pretty_nraenv_aux sym.circe ff a1 a2
  | Hack.ANMapEnv a1 -> pretty_nra_exp p sym sym.chie ff a1 None

(* resets precedence back to 0 *)
and pretty_nra_exp p sym thissym ff a1 oa2 =
  match oa2 with
  | None ->
      if p > 22
      then
	fprintf ff "@[<hv 1>(%a%a%a%a())@]" pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle
      else
	fprintf ff "@[<hv 0>%a%a%a%a()@]" pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle
  | Some a2 ->
      if p > 22
      then
	fprintf ff "@[<hv 3>(%a%a%a%a(@,%a@;<0 -2>))@]" pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle (pretty_nraenv_aux 0 sym) a2
      else
	fprintf ff "@[<hv 2>%a%a%a%a(@,%a@;<0 -2>)@]" pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle (pretty_nraenv_aux 0 sym) a2


let pretty_nraenv greek margin a =
  let conf = make_pretty_config greek margin in
  let ff = str_formatter in
  begin
    pp_set_margin ff (get_margin conf);
    let sym =
      match get_charset conf with
      | Greek -> greeksym
      | Ascii -> textsym
    in
    fprintf ff "@[%a@]@." (pretty_nraenv_aux 0 sym) a;
    flush_str_formatter ()
  end

(* NNRC PP *)

let rec pretty_nnrc_aux p sym ff n =
  match n with
  | Hack.NRCVar v -> fprintf ff "$v%s"  (Util.string_of_char_list v)
  | Hack.NRCConst d -> fprintf ff "%a" pretty_data d
  | Hack.NRCBinop (b,n1,n2) -> (pretty_binop p sym pretty_nnrc_aux) ff b n1 n2
  | Hack.NRCUnop (u,n1) -> (pretty_unop p sym pretty_nnrc_aux) ff u n1
  | Hack.NRCLet (v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	 (Util.string_of_char_list v)
	(pretty_nnrc_aux p sym) n1
	(pretty_nnrc_aux p sym) n2
  | Hack.NRCFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	(pretty_nnrc_aux 0 sym) n2
	 (Util.string_of_char_list v) pretty_sym sym.sin
	(pretty_nnrc_aux 0 sym) n1
  | Hack.NRCIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	(pretty_nnrc_aux p sym) n1
	(pretty_nnrc_aux p sym) n2
	(pretty_nnrc_aux p sym) n3
  | Hack.NRCEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	(pretty_nnrc_aux p sym) n0
	 (Util.string_of_char_list v1) (pretty_nnrc_aux p sym) n1
	 (Util.string_of_char_list v2) (pretty_nnrc_aux p sym) n2

let pretty_nnrc greek margin n =
  let conf = make_pretty_config greek margin in
  let ff = str_formatter in
  begin
    pp_set_margin ff (get_margin conf);
    let sym =
      match (get_charset conf) with
      | Greek -> greeksym
      | Ascii -> textsym
    in
    fprintf ff "@[%a@]@." (pretty_nnrc_aux 0 sym) n;
    flush_str_formatter ()
  end

(* NRCMR PP *)
let pretty_fun sym ff (x, n) =
  fprintf ff "@[fun ($v%s) ->@ %a@]"
    (Util.string_of_char_list x)
    (pretty_nnrc_aux 0 sym) n

let pretty_default_fun sym ff n =
  fprintf ff "@[fun db_default() ->@ %a@]"
    (pretty_nnrc_aux 0 sym) n

let pretty_enhanced_numeric_type_to_prefix typ =
  match typ with
  | Hack.Enhanced_numeric_int -> ""
  | Hack.Enhanced_numeric_float -> "F"

let pretty_reduce_op_to_string op =
  match op with
  | Hack.RedOpCount -> "count"
  | Hack.RedOpSum typ -> "+"
  | Hack.RedOpMin typ -> "min"
  | Hack.RedOpMax typ -> "max"
  | Hack.RedOpArithMean typ -> "arithmean"
  | Hack.RedOpStats typ -> "stats"


let pretty_nnrcmr_job_aux sym ff mr =
  let distributed = "distributed" in
  let scalar = "scalar" in
  let input_loc =
    match mr.Hack.mr_map with
    | Hack.MapDist _ -> distributed
    | Hack.MapDistFlatten _ -> distributed
    | Hack.MapScalar _ -> scalar
  in
  let output_loc =
    match mr.Hack.mr_reduce with
    | Hack.RedId -> distributed
    | Hack.RedCollect _ -> scalar
    | Hack.RedOp _ -> scalar
    | Hack.RedSingleton -> scalar
  in
  fprintf ff "@[<hv 0>input = $v%s : %s;@\n"
    (Util.string_of_char_list mr.Hack.mr_input) input_loc;
  fprintf ff "output = $v%s : %s;@\n"
    (Util.string_of_char_list mr.Hack.mr_output) output_loc;
  begin match mr.Hack.mr_map with
    | Hack.MapDist f -> fprintf ff "map(@[%a@]);" (pretty_fun sym) f
    | Hack.MapDistFlatten f -> fprintf ff "flatMap(@[%a@]);" (pretty_fun sym) f
    | Hack.MapScalar f -> fprintf ff "@[%a@];" (pretty_fun sym) f
  end;
  fprintf ff "@\n";
  begin match mr.Hack.mr_reduce with
  | Hack.RedId -> ()
  | Hack.RedCollect f -> fprintf ff "reduce(@[%a@]);" (pretty_fun sym) f
  | Hack.RedOp op ->
     let op_s = pretty_reduce_op_to_string (Obj.magic op)
     in
      fprintf ff "reduce(%s);" op_s
  | Hack.RedSingleton ->       fprintf ff "reduce(singleton);"
  end;
  fprintf ff "@\n";
  begin match Hack.EnhancedCompiler.CompCore.mr_reduce_empty [] mr with
  | None -> ()
  | Some f -> fprintf ff "default(@[%a@]);" (pretty_default_fun sym) f
  end

let pretty_mr_chain sym ff mr_chain =
  List.iter (fun mr ->
    fprintf ff "----------------@\n";
    fprintf ff "@[%a@]@\n" (pretty_nnrcmr_job_aux sym) mr;
    fprintf ff "----------------@\n")
    mr_chain

let rec pretty_list pp sep ff l =
  match l with
  | [] -> ()
  | d :: [] -> fprintf ff "%a" pp d
  | d :: l -> fprintf ff "%a%s@ %a" pp d sep (pretty_list pp sep) l

let pretty_mr_last sym ff mr_last =
  let ((params, n), args) = mr_last in
  let pretty_param ff x =
    fprintf ff "%s" (Util.string_of_char_list x)
  in
  let pretty_arg ff (x, loc) =
    match loc with
    | Hack.Vlocal ->  fprintf ff "(%s: Scalar)" (Util.string_of_char_list x)
    | Hack.Vdistr ->  fprintf ff "(%s: Distributed)" (Util.string_of_char_list x)
  in
  fprintf ff "@[(fun (%a) => %a) (%a)@]@\n"
    (pretty_list pretty_param ",") params
    (pretty_nnrc_aux 0 sym) n
    (pretty_list pretty_arg ",") args

let pretty_nnrcmr_aux sym ff mrl =
  pretty_mr_chain sym ff mrl.Hack.mr_chain;
  fprintf ff "@[%a@]@\n" (pretty_mr_last sym) mrl.Hack.mr_last

let pretty_nnrcmr greek margin mr_chain =
  let conf = make_pretty_config greek margin in
  let ff = str_formatter in
  begin
    pp_set_margin ff (get_margin conf);
    let sym =
      match (get_charset conf) with
      | Greek -> greeksym
      | Ascii -> textsym
    in
    fprintf ff "@[%a@]@." (pretty_nnrcmr_aux sym) mr_chain;
    flush_str_formatter ()
  end

(* dnrc PP *)

let rec pretty_dnrc_aux ann plug p sym ff n =
  match n with
  | Hack.DNRCVar (a, v) -> fprintf ff "%a$v%s" ann a (Util.string_of_char_list v)
  | Hack.DNRCConst (a, d) -> fprintf ff "%a%a" ann a pretty_data d
  | Hack.DNRCBinop (a, b,n1,n2) ->
      fprintf ff "%a(" ann a
    ; ((pretty_binop 0 sym (pretty_dnrc_aux ann plug)) ff b n1 n2)
    ; fprintf ff ")"
  | Hack.DNRCUnop (a,u,n1) ->
     fprintf ff "%a(" ann a
    ; ((pretty_unop 0 sym (pretty_dnrc_aux ann plug)) ff u n1)
    ; fprintf ff ")"
  | Hack.DNRCLet (a,v,n1,n2) ->
     fprintf ff "@[<hv 0>@[<hv 2>%a let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	     ann a
	 (Util.string_of_char_list v)
	(pretty_dnrc_aux ann plug p sym) n1
	(pretty_dnrc_aux ann plug p sym) n2
  | Hack.DNRCFor (a,v,n1,n2) ->
     fprintf ff "@[<hv 0>%a{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	     ann a
	(pretty_dnrc_aux ann plug 0 sym) n2
	 (Util.string_of_char_list v) pretty_sym sym.sin
	(pretty_dnrc_aux ann plug 0 sym) n1
  | Hack.DNRCIf (a,n1,n2,n3) ->
     fprintf ff "@[<hv 0>@[<hv 2>%a if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	     ann a
	(pretty_dnrc_aux ann plug p sym) n1
	(pretty_dnrc_aux ann plug p sym) n2
	(pretty_dnrc_aux ann plug p sym) n3
  | Hack.DNRCEither (a,n0,v1,n1,v2,n2) ->
     fprintf ff "@[<hv 0>@[<hv 2>%a match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	     ann a
	(pretty_dnrc_aux ann plug p sym) n0
	 (Util.string_of_char_list v1) (pretty_dnrc_aux ann plug p sym) n1
	 (Util.string_of_char_list v2) (pretty_dnrc_aux ann plug p sym) n2
  | Hack.DNRCCollect (a,n1) ->
     fprintf ff "@[%a%s[@[%a@]]@]"
	     ann a
	     "COLLECT"
	(pretty_dnrc_aux ann plug p sym) n1
  | Hack.DNRCDispatch (a,n1) ->
     fprintf ff "@[%a%s[@[%a@]]@]"
	     ann a
	     "DISPATCH"
	     (pretty_dnrc_aux ann plug p sym) n1
  | Hack.DNRCAlg (a,body,arglist) ->
     fprintf ff "@[%a(@[fun %a => @] %a)@[(%a)@]@]"
	     ann a
             (pretty_list (fun ff s -> fprintf ff "%s" s) ",") (List.map (fun x -> (Util.string_of_char_list (fst x))) arglist)
             plug body
	     (pretty_list (pretty_dnrc_aux ann plug p sym) ",") (List.map snd arglist)

let pretty_dnrc ann plug greek margin n =
  let conf = make_pretty_config greek margin in
  let ff = str_formatter in
  begin
    pp_set_margin ff (get_margin conf);
    let sym =
      match (get_charset conf) with
      | Greek -> greeksym
      | Ascii -> textsym
    in
    fprintf ff "@[%a@]@." (pretty_dnrc_aux ann plug 0 sym) n;
    flush_str_formatter ()
  end

let pretty_annotate_ignore ff a = ()
let pretty_plug_ignore ff a = ()

let pretty_plug_nraenv greek ff a =
  let sym = if greek then greeksym else textsym in
  pretty_nraenv_aux 0 sym ff a

(* Pretty RType *)

let rec pretty_rtype_aux sym ff rt =
  match rt with
  | Hack.Bottom__U2080_ -> fprintf ff "%a" pretty_sym sym.bot
  | Hack.Top__U2080_ ->  fprintf ff "%a" pretty_sym sym.top
  | Hack.Unit__U2080_ -> fprintf ff "Unit"
  | Hack.Nat__U2080_ -> fprintf ff "Nat"
  | Hack.Bool__U2080_ -> fprintf ff "Bool"
  | Hack.String__U2080_ -> fprintf ff "String"
  | Hack.Coll__U2080_ rc -> fprintf ff "{@[<hv 0>%a@]}" (pretty_rtype_aux sym) rc
  | Hack.Rec__U2080_ (Hack.Closed,rl) -> fprintf ff "[@[<hv 0>%a@]|]" (pretty_rec_type sym) rl
  | Hack.Rec__U2080_ (Hack.Open,rl) -> fprintf ff "[@[<hv 0>%a@]..]" (pretty_rec_type sym) rl
  | Hack.Either__U2080_ (r1,r2) -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@,| right {@,%a@;<0 -2>}@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | Hack.Arrow__U2080_ (r1,r2) -> fprintf ff "@[<hv 2>(fun %a => %a)@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | Hack.Brand__U2080_ bds -> fprintf ff "@[<hv 2>Brands [@[<hv 0>%a@]]@]" pretty_names bds
  | Hack.Foreign__U2080_ rf -> fprintf ff "Foreign"

and pretty_rec_type sym ff rl =
  match rl with
    [] -> ()
  | (ra,rd) :: [] -> fprintf ff "%s : %a" (Util.string_of_char_list ra) (pretty_rtype_aux sym) rd
  | (ra,rd) :: rl' -> fprintf ff "%s : %a;@ %a" (Util.string_of_char_list ra) (pretty_rtype_aux sym) rd (pretty_rec_type sym) rl'

let pretty_rtype greek margin rt =
  let conf = make_pretty_config greek margin in
  let ff = str_formatter in
  begin
    pp_set_margin ff (get_margin conf);
    let sym =
      match (get_charset conf) with
      | Greek -> greeksym
      | Ascii -> textsym
    in
    fprintf ff "@[%a@]@." (pretty_rtype_aux sym) rt;
    flush_str_formatter ()
  end

let pretty_annotate_rtype greek ff r =
    let sym = if greek then greeksym else textsym in
    fprintf ff "@[%a%a%a@]" pretty_sym sym.llangle (pretty_rtype_aux sym) r pretty_sym sym.rrangle

let pretty_drtype_aux sym ff drt =
  match drt with
  | Hack.Tlocal tr -> fprintf ff "L%a" (pretty_rtype_aux sym) tr
  | Hack.Tdistr tr -> fprintf ff "D%a" (pretty_rtype_aux sym) tr

let pretty_annotate_annotated_rtype greek subpr ff (at:'a Compiler.EnhancedCompiler.CompCore.type_annotation) =
  let sym = if greek then greeksym else textsym in
  let inf = Compiler.EnhancedCompiler.CompCore.ta_inferred [] at in
  let req = Compiler.EnhancedCompiler.CompCore.ta_required [] at in
  if Hack.equiv_dec (Hack.drtype_eqdec Hack.EnhancedRuntime.compiler_foreign_type []) inf req
  then
    fprintf ff "@[%a%a%a%a@]"
	    pretty_sym sym.lpangle
	    (pretty_drtype_aux sym) inf
	    pretty_sym sym.rpangle
            subpr (Compiler.EnhancedCompiler.CompCore.ta_base [] at)
  else
    fprintf ff "@[%a%a -> %a%a%a@]"
	    pretty_sym sym.lpangle
	    (pretty_drtype_aux sym) inf
	    (pretty_drtype_aux sym) req
	    pretty_sym sym.rpangle
            subpr (Compiler.EnhancedCompiler.CompCore.ta_base [] at)

(* Pretty Spark IR *)
let rec pretty_column_aux p sym ff col =
  match col with
  | Hack.CCol v -> fprintf ff "%a%s%a" pretty_sym sym.langle (Util.string_of_char_list v) pretty_sym sym.rangle
  | Hack.CDot (v,c) -> pretty_unop p sym pretty_column_aux ff (Hack.ADot v) c
  | Hack.CLit (d,rt) -> fprintf ff "@[%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle pretty_data d
  | Hack.CPlus (c1,c2) -> pretty_binop p sym pretty_column_aux ff (Hack.ABArith Hack.ArithPlus) c1 c2
  | Hack.CEq (c1,c2) -> pretty_binop p sym pretty_column_aux ff Hack.AEq c1 c2
  | Hack.CNeg c -> pretty_unop p sym pretty_column_aux ff Hack.ANeg c
  | Hack.CToString c -> pretty_unop p sym pretty_column_aux ff Hack.AToString c
  | Hack.CSConcat (c1,c2) -> pretty_binop p sym pretty_column_aux ff Hack.ASConcat c1 c2
  | Hack.CUDFCast (bs,c) -> pretty_unop p sym pretty_column_aux ff (Hack.ACast bs) c
  | Hack.CUDFUnbrand (rt,c) -> fprintf ff "@[!%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle (pretty_column_aux p sym) c

let rec pretty_spark_aggregate_aux p sym ff agg =
  match agg with
  | Hack.SACount -> fprintf ff "%s" "Count"
  | Hack.SASum -> fprintf ff "%s" "Sum"
  | Hack.SACollectList -> fprintf ff "%s" "CollectList"

let pretty_named_column_aux p sym ff (name, col) =
  fprintf ff "%s%@%a" (Util.string_of_char_list name) (pretty_column_aux p sym) col

let rec pretty_dataset_aux p sym ff ds =
  match ds with
  | Hack.DSVar v -> fprintf ff "$%s" (Util.string_of_char_list v)
  | Hack.DSSelect (cl,ds1) -> fprintf ff "@[select %a @[<hv 2>from %a@] @]"
				      (pretty_list (pretty_named_column_aux p sym) ",") cl (pretty_dataset_aux p sym) ds1
  | Hack.DSFilter (c,ds1) -> fprintf ff "@[filter %a @[<hv 2>from %a@] @]"
				      (pretty_column_aux p sym) c (pretty_dataset_aux p sym) ds1
  | Hack.DSGroupBy (cl,al,ds1) -> fprintf ff "@[group %a @[<hv 2>by %a@] @[<hv 2>using %a@]@]"
					  (pretty_dataset_aux p sym) ds1
					  (pretty_list (pretty_named_column_aux p sym) ",") cl
					  (pretty_list (fun ff ((s,a),c) ->
					       fprintf ff "%s@%a of %a"
						       (Util.string_of_char_list s)
						       (pretty_spark_aggregate_aux p sym) a
						       (pretty_column_aux p sym) c
						       ) ",") al
  | Hack.DSCartesian (ds1,ds2) ->  pretty_binop p sym pretty_dataset_aux ff Hack.AConcat ds1 ds2
  | Hack.DSExplode (s,ds) -> fprintf ff "@[explode %s @[<hv 2>from %a@] @]" (Util.string_of_char_list s) (pretty_dataset_aux p sym) ds

let pretty_dataset greek margin ds =
  let conf = make_pretty_config greek margin in
  let ff = str_formatter in
  begin
    pp_set_margin ff (get_margin conf);
    let sym =
      match (get_charset conf) with
      | Greek -> greeksym
      | Ascii -> textsym
    in
    fprintf ff "@[%a@]@." (pretty_dataset_aux 0 sym) ds;
    flush_str_formatter ()
  end

let pretty_plug_dataset greek ff a =
  let sym = if greek then greeksym else textsym in
  pretty_dataset_aux 0 sym ff a
