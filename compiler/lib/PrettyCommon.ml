(*
 * Copyright 2015-2017 IBM Corporation
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
open QcertUtils.Util
open QcertExtracted
open QcertCompiler.EnhancedCompiler

(** Character sets *)

type charkind =
  | Ascii
  | Greek

type pretty_config =
    { mutable margin : int;
      mutable charset : charkind;
      mutable type_annotations : bool;
      mutable inheritance : QData.json;
      mutable link_js_runtime : bool; }

let default_pretty_config () =
  { margin = 120;
    charset = Greek;
    type_annotations = false;
    inheritance = QcertCompiler.Jarray [];
    link_js_runtime = false; }

let set_ascii conf () = conf.charset <- Ascii
let set_greek conf () = conf.charset <- Greek
let get_charset conf = conf.charset
let get_charset_bool conf =
  begin match conf.charset with
  | Greek -> true
  | Ascii -> false
  end

let set_type_annotations conf () = conf.type_annotations <- true
let set_no_type_annotations conf () = conf.type_annotations <- false
let get_type_annotations conf = conf.type_annotations

let set_margin conf i = conf.margin <- i
let get_margin conf = conf.margin

let set_inheritance conf h = conf.inheritance <- h
let get_inheritance conf = conf.inheritance

let set_link_js_runtime conf () = conf.link_js_runtime <- true
let link_js_runtime conf = conf.link_js_runtime

(* Charset dependent config *)
(* Note: This should remain within the module *)

type symbols =
    { chi: (string*int);
      chiflat: (string*int);
      chie: (string*int);
      join: (string*int);
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
      bpi: (string*int);
      gamma: (string*int);
      rho: (string*int);
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
    chiflat = ("FlatMap", 7);
    chie = ("Map^e", 5);
    join = ("Join", 4);
    djoin = ("MapConcat", 9);
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
    pi = ("project", 7);
    bpi = ("Project", 7);
    gamma = ("Group", 5);
    rho = ("Unnest", 6);
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
    chiflat = ("χᶠ", 2);
    chie = ("χᵉ", 2);
    join = ("⋈", 1);
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
    bpi = ("Π", 1);
    gamma = ("Γ", 1);
    rho = ("ρ", 1);
    cup = ("∪",1);
    vee = ("∨",1);
    wedge = ("∧",1);
    leq = ("≤",1);
    sin = ("∈",1);
    neg = ("¬",1);
    top = ("⊤",1);
    bot = ("⊥",1) }

let pretty_sym ff sym =
  begin
    let (asym,asize) = sym in
    pp_print_as ff asize asym
  end

let rec pretty_names ff nl =
  begin match nl with
    [] -> ()
  | n :: [] -> fprintf ff "%s" (string_of_char_list n)
  | n :: nl' -> fprintf ff "%s,@ %a" (string_of_char_list n) pretty_names nl'
  end

let pretty_squared_names sym ff nl =
  fprintf ff "%a@[<hv 0>%a@]%a" pretty_sym sym.lfloor pretty_names nl pretty_sym sym.rfloor

let rec pretty_sharp sym ff name =
  fprintf ff "%a%s" pretty_sym sym.sharp name

(** Pretty data *)

let timescale_as_string ts =
  begin match ts with
  | QcertCompiler.Ts_second -> "SECOND"
  | QcertCompiler.Ts_minute ->  "MINUTE"
  | QcertCompiler.Ts_hour -> "HOUR"
  | QcertCompiler.Ts_day -> "DAY"
  | QcertCompiler.Ts_week -> "WEEK"
  | QcertCompiler.Ts_month -> "MONTH"
  | QcertCompiler.Ts_year -> "YEAR"
  end

let pretty_timescale ff ts =
  fprintf ff "%s" (timescale_as_string ts)

let string_of_foreign_data (fd:QcertCompiler.enhanced_data) : string =
  begin match fd with
  | QcertCompiler.Enhancedstring s -> "S\"" ^ s ^ "\""
  | QcertCompiler.Enhancedtimescale ts -> timescale_as_string ts
  | QcertCompiler.Enhancedtimeduration td -> raise Not_found
  | QcertCompiler.Enhancedtimepoint tp -> raise Not_found
  | QcertCompiler.Enhancedsqldate td -> raise Not_found
  | QcertCompiler.Enhancedsqldateinterval tp -> raise Not_found
  end

let foreign_data_of_string s =
  begin match s with
  | "SECOND" -> QcertCompiler.Enhancedtimescale QcertCompiler.Ts_second
  | "MINUTE" -> QcertCompiler.Enhancedtimescale QcertCompiler.Ts_minute
  | "HOUR" -> QcertCompiler.Enhancedtimescale QcertCompiler.Ts_hour
  | "DAY" -> QcertCompiler.Enhancedtimescale QcertCompiler.Ts_day
  | "WEEK" -> QcertCompiler.Enhancedtimescale QcertCompiler.Ts_week
  | "MONTH" -> QcertCompiler.Enhancedtimescale QcertCompiler.Ts_month
  | "YEAR" -> QcertCompiler.Enhancedtimescale QcertCompiler.Ts_year
  | _ ->
      try
	if (s.[0] = 'S' && s.[1] = '"')
	then
	  QcertCompiler.Enhancedstring (String.sub s 2 ((String.length s) - 3))
	else
	  raise Not_found
      with
      | _ ->
	  raise Not_found
  end

let pretty_foreign_data ff fd =
  begin match fd with
  | QcertCompiler.Enhancedstring s -> fprintf ff "S\"%s\"" s
  | QcertCompiler.Enhancedtimescale ts -> pretty_timescale ff ts
  | QcertCompiler.Enhancedtimeduration td -> raise Not_found
  | QcertCompiler.Enhancedtimepoint tp -> raise Not_found
  | QcertCompiler.Enhancedsqldate td -> raise Not_found
  | QcertCompiler.Enhancedsqldateinterval tp -> raise Not_found
  end

let rec pretty_data ff d =
  begin match d with
  | QcertCompiler.Dunit -> fprintf ff "null"
  | QcertCompiler.Dnat n -> fprintf ff "%d" n
  | QcertCompiler.Dfloat f -> fprintf ff "%f" f
  | QcertCompiler.Dbool true -> fprintf ff "true"
  | QcertCompiler.Dbool false -> fprintf ff "false"
  | QcertCompiler.Dstring s -> fprintf ff "\"%s\"" (string_of_char_list s)
  | QcertCompiler.Dcoll dl -> fprintf ff "{@[<hv 0>%a@]}" pretty_coll dl
  | QcertCompiler.Drec rl -> fprintf ff "[@[<hv 0>%a@]]" pretty_rec rl
  | QcertCompiler.Dleft d -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@]" pretty_data d
  | QcertCompiler.Dright d -> fprintf ff "@[<hv 2>right {@,%a@;<0 -2>}@]" pretty_data d
  | QcertCompiler.Dbrand (brands,d) -> fprintf ff "@[<hv 2>brands [@[<hv 0>%a@]] {@,%a@;<0 -2>}@]"
				      pretty_names brands
				      pretty_data d
  | QcertCompiler.Dforeign fd -> pretty_foreign_data ff (Obj.magic fd)
  end

and pretty_coll ff dl =
  match dl with
    [] -> ()
  | d :: [] -> fprintf ff "%a" pretty_data d
  | d :: dl' -> fprintf ff "%a,@ %a" pretty_data d pretty_coll dl'

and pretty_rec ff rl =
  match rl with
    [] -> ()
  | (ra,rd) :: [] -> fprintf ff "%s : %a" (string_of_char_list ra) pretty_data rd
  | (ra,rd) :: rl' -> fprintf ff "%s : %a;@ %a" (string_of_char_list ra) pretty_data rd pretty_rec rl'

(** Pretty rtype *)

let rec pretty_rtype_aux sym ff rt =
  begin match rt with
  | QcertCompiler.Bottom_UU2080_ -> fprintf ff "%a" pretty_sym sym.bot
  | QcertCompiler.Top_UU2080_ ->  fprintf ff "%a" pretty_sym sym.top
  | QcertCompiler.Unit_UU2080_ -> fprintf ff "Unit"
  | QcertCompiler.Nat_UU2080_ -> fprintf ff "Nat"
  | QcertCompiler.Float_UU2080_ -> fprintf ff "Float"
  | QcertCompiler.Bool_UU2080_ -> fprintf ff "Bool"
  | QcertCompiler.String_UU2080_ -> fprintf ff "String"
  | QcertCompiler.Coll_UU2080_ rc -> fprintf ff "{@[<hv 0>%a@]}" (pretty_rtype_aux sym) rc
  | QcertCompiler.Rec_UU2080_ (QcertCompiler.Closed,rl) -> fprintf ff "[@[<hv 0>%a@]|]" (pretty_rec_type sym) rl
  | QcertCompiler.Rec_UU2080_ (QcertCompiler.Open,rl) -> fprintf ff "[@[<hv 0>%a@]..]" (pretty_rec_type sym) rl
  | QcertCompiler.Either_UU2080_ (r1,r2) -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@,| right {@,%a@;<0 -2>}@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | QcertCompiler.Arrow_UU2080_ (r1,r2) -> fprintf ff "@[<hv 2>(fun %a => %a)@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | QcertCompiler.Brand_UU2080_ bds -> fprintf ff "@[<hv 2>Brands [BRANDS]@]"
  | QcertCompiler.Foreign_UU2080_ rf -> fprintf ff "Foreign"
  end

and pretty_rec_type sym ff rl =
  match rl with
    [] -> ()
  | (ra,rd) :: [] -> fprintf ff "%s : %a" (string_of_char_list ra) (pretty_rtype_aux sym) rd
  | (ra,rd) :: rl' -> fprintf ff "%s : %a;@ %a" (string_of_char_list ra) (pretty_rtype_aux sym) rd (pretty_rec_type sym) rl'

let pretty_drtype_aux sym ff drt =
  match drt with
  | QcertCompiler.Tlocal tr -> fprintf ff "L%a" (pretty_rtype_aux sym) tr
  | QcertCompiler.Tdistr tr -> fprintf ff "D%a" (pretty_rtype_aux sym) tr

let pretty_annotate_annotated_rtype greek subpr ff (at:'a QcertCompiler.type_annotation) =
  let sym = if greek then greeksym else textsym in
  let inf = QUtil.ta_inferred [] at in
  let req = QUtil.ta_required [] at in
  if QcertCompiler.equiv_dec (QcertCompiler.drtype_eqdec QcertCompiler.EnhancedRuntime.compiler_foreign_type []) inf req
  then
    fprintf ff "@[%a%a%a%a@]"
	    pretty_sym sym.lpangle
	    (pretty_drtype_aux sym) inf
	    pretty_sym sym.rpangle
            subpr (QUtil.ta_base [] at)
  else
    fprintf ff "@[%a%a -> %a%a%a@]"
	    pretty_sym sym.lpangle
	    (pretty_drtype_aux sym) inf
	    (pretty_drtype_aux sym) req
	    pretty_sym sym.rpangle
            subpr (QUtil.ta_base [] at)

(** Pretty utils *)

type 'a pretty_fun = int -> symbols -> Format.formatter -> 'a -> unit

(** Pretty operators *)

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
   *,/,%                      \/       	     [+]   19
   +, -        U, \           /\     ^ 	     [*]   18
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

let string_of_nat_arith_unary_op ua =
  begin match ua with
  | QcertCompiler.NatAbs -> "abs"
  | QcertCompiler.NatLog2 -> "log2"
  | QcertCompiler.NatSqrt -> "sqrt"
  end

let nat_arith_unary_op_of_string s =
  begin match s with
  | "abs" -> QcertCompiler.NatAbs
  | "log2" -> QcertCompiler.NatLog2
  | "sqrt" -> QcertCompiler.NatSqrt
  | _ -> raise Not_found
  end

let pretty_nat_arith_unary_op p sym callb ff ua a =
  pretty_unary_exp sym callb (string_of_nat_arith_unary_op ua) ff a

let string_of_float_arith_unary_op ua =
  begin match ua with
  | QcertCompiler.FloatNeg -> "Fneg"
  | QcertCompiler.FloatSqrt -> "Fsqrt"
  | QcertCompiler.FloatExp -> "Fexp"
  | QcertCompiler.FloatLog -> "Flog"
  | QcertCompiler.FloatLog10 -> "Flog10"
  | QcertCompiler.FloatCeil -> "Fceil"
  | QcertCompiler.FloatFloor -> "Ffloor"
  | QcertCompiler.FloatAbs -> "Fabs"
  end

let float_arith_unary_op_of_string s =
  begin match s with
  | "Fneg" -> QcertCompiler.FloatNeg
  | "Fsqrt" -> QcertCompiler.FloatSqrt
  | "Fexp" -> QcertCompiler.FloatExp
  | "Flog" -> QcertCompiler.FloatLog
  | "Flog10" -> QcertCompiler.FloatLog10
  | "Fceil" -> QcertCompiler.FloatCeil
  | "Ffloor" -> QcertCompiler.FloatFloor
  | _ -> raise Not_found
  end

let pretty_float_arith_unary_op p sym callb ff ua a =
  pretty_unary_exp sym callb (string_of_float_arith_unary_op ua) ff a

let sql_date_component_to_string part =
  begin match part with
  | QcertCompiler.Sql_date_DAY -> "DAY"
  | QcertCompiler.Sql_date_MONTH -> "MONTH"
  | QcertCompiler.Sql_date_YEAR -> "YEAR"
  end

let string_of_foreign_unary_op fu : string =
  begin match fu with
  | QcertCompiler.Enhanced_unary_time_op QcertCompiler.Uop_time_to_scale -> "TimeToScale"
  | QcertCompiler.Enhanced_unary_time_op QcertCompiler.Uop_time_from_string -> "TimeFromString"
  | QcertCompiler.Enhanced_unary_time_op QcertCompiler.Uop_time_duration_from_string -> "TimeDurationFromString"
  | QcertCompiler.Enhanced_unary_sql_date_op (QcertCompiler.Uop_sql_get_date_component part) -> "(SqlGetDateComponent " ^ (sql_date_component_to_string part) ^ ")"
  | QcertCompiler.Enhanced_unary_sql_date_op QcertCompiler.Uop_sql_date_from_string -> "SqlDateFromString"
  | QcertCompiler.Enhanced_unary_sql_date_op QcertCompiler.Uop_sql_date_interval_from_string -> "SqlDateIntervalFromString"
  end

let foreign_unary_op_of_string s =
  begin match s with
  | "TimeToScale" -> QcertCompiler.Enhanced_unary_time_op QcertCompiler.Uop_time_to_scale
  | "TimeFromString" -> QcertCompiler.Enhanced_unary_time_op QcertCompiler.Uop_time_from_string
  | "TimeDurationFromString" -> QcertCompiler.Enhanced_unary_time_op QcertCompiler.Uop_time_duration_from_string
  | "(SqlGetDateComponent DAY)"->  QcertCompiler.Enhanced_unary_sql_date_op (QcertCompiler.Uop_sql_get_date_component QcertCompiler.Sql_date_DAY)
  | "(SqlGetDateComponent MONTH)"->  QcertCompiler.Enhanced_unary_sql_date_op (QcertCompiler.Uop_sql_get_date_component QcertCompiler.Sql_date_MONTH)
  | "(SqlGetDateComponent YEAR)"->  QcertCompiler.Enhanced_unary_sql_date_op (QcertCompiler.Uop_sql_get_date_component QcertCompiler.Sql_date_YEAR)
  | "SqlDateFromString" -> QcertCompiler.Enhanced_unary_sql_date_op QcertCompiler.Uop_sql_date_from_string
  | "SqlDateIntervalFromString" -> QcertCompiler.Enhanced_unary_sql_date_op QcertCompiler.Uop_sql_date_interval_from_string
  | _ -> raise Not_found
  end

let pretty_foreign_unary_op p sym callb ff fu a =
  pretty_unary_exp sym callb (string_of_foreign_unary_op fu) ff a

let pretty_unary_op p sym callb ff u a =
  begin match u with
  | QcertCompiler.OpIdentity -> pretty_unary_exp sym callb "id" ff a
  | QcertCompiler.OpNeg ->
      if (p > 25)
      then
	fprintf ff "@[<hv 0>%a(%a)@]" pretty_sym sym.neg (callb 0 sym) a
      else
	fprintf ff "@[<hv 0>%a%a@]" pretty_sym sym.neg (callb 25 sym) a
  (* resets precedence back to 0 *)
  | QcertCompiler.OpBag -> fprintf ff "@[<hv 2>{@,%a@;<0 -2>}@]" (callb 0 sym) a
  | QcertCompiler.OpCount -> pretty_unary_exp sym callb "count" ff a
  | QcertCompiler.OpFlatten -> pretty_unary_exp sym callb "flatten" ff a
  | QcertCompiler.OpLeft -> pretty_unary_exp sym callb "left" ff a
  | QcertCompiler.OpRight -> pretty_unary_exp sym callb "right" ff a
  (* resets precedence back to 0 *)
  | QcertCompiler.OpBrand brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "brand" (pretty_squared_names sym) brands (callb 0 sym) a
  (* resets precedence back to 0 *)
  | QcertCompiler.OpRec att -> fprintf ff "@[<hv 2>[ %s :@ %a ]@]" (string_of_char_list att) (callb 0 sym) a
  | QcertCompiler.OpDot att ->
      if p > 23
      then fprintf ff "@[<hv 0>(%a.%s)@]" (callb 23 sym) a (string_of_char_list att)
      else fprintf ff "@[<hv 0>%a.%s@]" (callb 23 sym) a (string_of_char_list att)
  (* resets precedence back to 0 *)
  | QcertCompiler.OpRecRemove att ->
      fprintf ff "@[<hv 0>%a%a%a(%a)@]" pretty_sym sym.neg pretty_sym sym.pi (pretty_squared_names sym) [att] (callb 0 sym) a
  (* resets precedence back to 0 *)
  | QcertCompiler.OpRecProject atts ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.pi (pretty_squared_names sym) atts (callb 0 sym) a
  | QcertCompiler.OpDistinct -> pretty_unary_exp sym callb "distinct" ff a
  | QcertCompiler.OpOrderBy atts ->
      fprintf ff "@[<hv 0>%s%a(%a)@]" "sort" (pretty_squared_names sym) (List.map fst atts) (callb 0 sym) a
  | QcertCompiler.OpToString -> pretty_unary_exp sym callb "toString" ff a
  | QcertCompiler.OpToText -> pretty_unary_exp sym callb "toText" ff a
  | QcertCompiler.OpLength -> pretty_unary_exp sym callb "length" ff a
  | QcertCompiler.OpSubstring (n1,None) -> pretty_unary_exp sym callb ("substring["^(string_of_int n1)^"]") ff a
  | QcertCompiler.OpSubstring (n1,Some n2) -> pretty_unary_exp sym callb ("substring["^(string_of_int n1)^","^(string_of_int n2)^"]") ff a
  | QcertCompiler.OpLike (n1,None) -> pretty_unary_exp sym callb ("like["^(string_of_char_list n1)^"]") ff a
  (* for some reason using String.str gives a compile error *)
  | QcertCompiler.OpLike (n1,Some n2) -> pretty_unary_exp sym callb ("like["^(string_of_char_list n1)^" ESCAPE "^(string_of_char_list [n2])^"]") ff a
  (* resets precedence back to 0 *)
  | QcertCompiler.OpCast brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "cast" (pretty_squared_names sym) brands (callb p sym) a
  | QcertCompiler.OpUnbrand ->
      if p > 24
      then fprintf ff "@[<hv 0>(!%a)@]" (callb 24 sym) a
      else fprintf ff "@[<hv 0>!%a@]" (callb 24 sym) a
  | QcertCompiler.OpSingleton -> pretty_unary_exp sym callb "singleton" ff a
  | QcertCompiler.OpNatUnary ua -> pretty_nat_arith_unary_op p sym callb ff ua a
  | QcertCompiler.OpNatSum -> pretty_unary_exp sym callb "sum" ff a
  | QcertCompiler.OpNatMean -> pretty_unary_exp sym callb "avg" ff a
  | QcertCompiler.OpNatMin -> pretty_unary_exp sym callb "min" ff a
  | QcertCompiler.OpNatMax -> pretty_unary_exp sym callb "max" ff a
  | QcertCompiler.OpFloatOfNat -> pretty_unary_exp sym callb "Fof_int" ff a
  | QcertCompiler.OpFloatUnary ua -> pretty_float_arith_unary_op p sym callb ff ua a
  | QcertCompiler.OpFloatTruncate -> pretty_unary_exp sym callb "Ftruncate" ff a
  | QcertCompiler.OpFloatSum -> pretty_unary_exp sym callb "Fsum" ff a
  | QcertCompiler.OpFloatMean -> pretty_unary_exp sym callb "Favg" ff a
  | QcertCompiler.OpFloatBagMin -> pretty_unary_exp sym callb "Flist_min" ff a
  | QcertCompiler.OpFloatBagMax -> pretty_unary_exp sym callb "Flist_max" ff a
  | QcertCompiler.OpForeignUnary fu -> pretty_foreign_unary_op p sym callb ff (Obj.magic fu) a
  end

let string_of_nat_arith_binary_op ba =
  begin match ba with
  | QcertCompiler.NatPlus -> "plus"
  | QcertCompiler.NatMinus -> "minus"
  | QcertCompiler.NatMult -> "mult"
  | QcertCompiler.NatMin -> "min"
  | QcertCompiler.NatMax -> "max"
  | QcertCompiler.NatDiv -> "divide"
  | QcertCompiler.NatRem -> "rem"
  end

let nat_arith_binary_op_of_string s =
  begin match s with
  | "plus" -> QcertCompiler.NatPlus
  | "minus" -> QcertCompiler.NatMinus
  | "mult" -> QcertCompiler.NatMult
  | "min" -> QcertCompiler.NatMin
  | "max" -> QcertCompiler.NatMax
  | "divide" -> QcertCompiler.NatDiv
  | "rem" -> QcertCompiler.NatRem
  | _ -> raise Not_found
  end

let pretty_nat_arith_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | QcertCompiler.NatPlus -> pretty_infix_exp p 18 sym callb ("+",1) ff a1 a2
  | QcertCompiler.NatMinus -> pretty_infix_exp p 18 sym callb ("-",1) ff a1 a2
  | QcertCompiler.NatMult -> pretty_infix_exp p 19 sym callb ("*",1) ff a1 a2
  | QcertCompiler.NatMin -> pretty_infix_exp p 20 sym callb ("min",3) ff a1 a2
  | QcertCompiler.NatMax -> pretty_infix_exp p 20 sym callb ("max",3) ff a1 a2
  | QcertCompiler.NatDiv -> pretty_infix_exp p 19 sym callb ("/",1) ff a1 a2
  | QcertCompiler.NatRem -> pretty_infix_exp p 19 sym callb ("%",1) ff a1 a2
  end

let string_of_float_arith_binary_op ba =
  begin match ba with
  | QcertCompiler.FloatPlus -> "float_plus"
  | QcertCompiler.FloatMinus -> "float_minus"
  | QcertCompiler.FloatMult -> "float_mult"
  | QcertCompiler.FloatDiv -> "float_div"
  | QcertCompiler.FloatPow -> "float_pow"
  | QcertCompiler.FloatMin -> "float_min"
  | QcertCompiler.FloatMax -> "float_max"
  end

let float_arith_binary_op_of_string ba =
  begin match ba with
  | "float_plus" -> QcertCompiler.FloatPlus
  | "float_minus" -> QcertCompiler.FloatMinus
  | "float_mult" -> QcertCompiler.FloatMult
  | "float_div" -> QcertCompiler.FloatDiv
  | "float_pow" -> QcertCompiler.FloatPow
  | "float_min" -> QcertCompiler.FloatMin
  | "float_max" -> QcertCompiler.FloatMax
  | _ -> raise Not_found
  end

let string_of_float_compare_binary_op ba =
  begin match ba with
  | QcertCompiler.FloatLt -> "FloatLt"
  | QcertCompiler.FloatLe -> "FloatLe"
  | QcertCompiler.FloatGt -> "FloatGt"
  | QcertCompiler.FloatGe -> "FloatGe"
  end

let float_compare_binary_op_of_string s =
  begin match s with
  | "FloatLt" -> QcertCompiler.FloatLt
  | "FloatLe" -> QcertCompiler.FloatLe
  | "FloatGt" -> QcertCompiler.FloatGt
  | "FloatGe" -> QcertCompiler.FloatGe
  | _ -> raise Not_found
  end

let pretty_float_arith_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | QcertCompiler.FloatPlus ->
     pretty_infix_exp p 18 sym callb ("F+",1) ff a1 a2
  | QcertCompiler.FloatMinus ->
     pretty_infix_exp p 18 sym callb ("F-",1) ff a1 a2
  | QcertCompiler.FloatMult ->
     pretty_infix_exp p 18 sym callb ("F*",1) ff a1 a2
  | QcertCompiler.FloatDiv ->
     pretty_infix_exp p 18 sym callb ("F/",1) ff a1 a2
  | QcertCompiler.FloatPow ->
     pretty_infix_exp p 18 sym callb ("F^",1) ff a1 a2
  | QcertCompiler.FloatMin ->
     pretty_infix_exp p 20 sym callb ("Fmin",3) ff a1 a2
  | QcertCompiler.FloatMax ->
     pretty_infix_exp p 20 sym callb ("Fmax",3) ff a1 a2
  end

let pretty_float_compare_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | QcertCompiler.FloatLt ->
    pretty_infix_exp p 18 sym callb ("F<",1) ff a1 a2
  | QcertCompiler.FloatLe ->
    pretty_infix_exp p 18 sym callb ("F<=",1) ff a1 a2
  | QcertCompiler.FloatGt ->
    pretty_infix_exp p 18 sym callb ("F>",1) ff a1 a2
  | QcertCompiler.FloatGe ->
    pretty_infix_exp p 18 sym callb ("F>=",1) ff a1 a2
  end

let string_of_foreign_binary_op fb =
  begin match fb with
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_as -> "time_as"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_shift -> "time_shift"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_ne -> "time_ne"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_lt -> "time_lt"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_le -> "time_le"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_gt -> "time_gt"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_ge -> "time_ge"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_duration_from_scale -> "time_duration_from_scale"
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_duration_between -> "time_duration_between"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_plus -> "sql_date_plus"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_minus -> "sql_date_minus"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_ne -> "sql_date_ne"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_lt -> "sql_date_lt"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_le -> "sql_date_le"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_gt -> "sql_date_gt"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_ge -> "sql_date_ge"
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_interval_between -> "sql_date_interval_between"
  end

let foreign_binary_op_of_string fb =
  match fb with
  | "time_as" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_as
  | "time_shift" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_shift
  | "time_ne" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_ne
  | "time_lt" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_lt
  | "time_le" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_le
  | "time_gt" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_gt
  | "time_ge" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_ge
  | "time_duration_from_scale" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_duration_from_scale
  | "time_duration_between" -> QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_duration_between
  | "sql_date_plus" -> QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_plus
  | "sql_date_ne" -> QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_ne
  | "sql_date_lt" -> QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_lt
  | "sql_date_le" -> QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_le
  | "sql_date_gt" -> QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_gt
  | "sql_date_ge" -> QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_ge
  | "sql_date_interval_between" -> QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_interval_between
  | _ -> raise Not_found

let pretty_foreign_binary_op p sym callb ff fb a1 a2 =
  match fb with
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_as ->
     pretty_infix_exp p 18 sym callb ("Tas",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_shift ->
     pretty_infix_exp p 18 sym callb ("T+",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_ne ->
     pretty_infix_exp p 18 sym callb ("T!=",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_lt ->
     pretty_infix_exp p 18 sym callb ("T<",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_le ->
     pretty_infix_exp p 18 sym callb ("T<=",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_gt ->
     pretty_infix_exp p 18 sym callb ("T>",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_ge ->
     pretty_infix_exp p 18 sym callb ("T>=",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_duration_from_scale ->
     pretty_infix_exp p 18 sym callb ("TD_fs",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_time_op QcertCompiler.Bop_time_duration_between ->
     pretty_infix_exp p 18 sym callb ("TD_be",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_plus ->
     pretty_infix_exp p 18 sym callb ("SD+",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_minus ->
     pretty_infix_exp p 18 sym callb ("SD-",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_ne ->
     pretty_infix_exp p 18 sym callb ("SD!=",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_lt ->
     pretty_infix_exp p 18 sym callb ("SD<",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_le ->
     pretty_infix_exp p 18 sym callb ("SD<=",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_gt ->
     pretty_infix_exp p 18 sym callb ("SD>",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_ge ->
     pretty_infix_exp p 18 sym callb ("SD>=",1) ff a1 a2
  | QcertCompiler.Enhanced_binary_sql_date_op QcertCompiler.Bop_sql_date_interval_between ->
     pretty_infix_exp p 18 sym callb ("SDD_be",1) ff a1 a2

let string_of_binary_op b =
  begin match b with
  | QcertCompiler.OpEqual -> "aeq"
  | QcertCompiler.OpBagUnion -> "aunion"
  | QcertCompiler.OpRecConcat -> "aconcat"
  | QcertCompiler.OpRecMerge -> "amergeconcat"
  | QcertCompiler.OpAnd -> "aand"
  | QcertCompiler.OpOr -> "aor"
  | QcertCompiler.OpNatBinary ba -> string_of_nat_arith_binary_op ba
  | QcertCompiler.OpFloatBinary ba -> string_of_float_arith_binary_op ba
  | QcertCompiler.OpFloatCompare ba -> string_of_float_compare_binary_op ba
  | QcertCompiler.OpLt -> "alt"
  | QcertCompiler.OpLe -> "ale"
  | QcertCompiler.OpBagDiff -> "aminus"
  | QcertCompiler.OpBagMin -> "amin"
  | QcertCompiler.OpBagMax -> "amax"
  | QcertCompiler.OpBagNth -> "anth"
  | QcertCompiler.OpContains -> "acontains"
  | QcertCompiler.OpStringConcat -> "asconcat"
  | QcertCompiler.OpStringJoin -> "asjoin"
  | QcertCompiler.OpForeignBinary fb -> string_of_foreign_binary_op (Obj.magic fb)
  end

let pretty_binary_op p sym callb ff b a1 a2 =
  begin match b with
  | QcertCompiler.OpEqual -> pretty_infix_exp p 15 sym callb ("=",1) ff a1 a2
  | QcertCompiler.OpBagUnion -> pretty_infix_exp p 18 sym callb sym.cup ff a1 a2
  | QcertCompiler.OpRecConcat -> pretty_infix_exp p 19 sym callb ("[+]",3) ff a1 a2
  | QcertCompiler.OpRecMerge -> pretty_infix_exp p 18 sym callb ("[*]",3) ff a1 a2
  | QcertCompiler.OpAnd -> pretty_infix_exp p 19 sym callb sym.wedge ff a1 a2
  | QcertCompiler.OpOr -> pretty_infix_exp p 18 sym callb sym.vee ff a1 a2
  | QcertCompiler.OpNatBinary ba -> (pretty_nat_arith_binary_op p sym callb) ff ba a1 a2
  | QcertCompiler.OpFloatBinary ba -> (pretty_float_arith_binary_op p sym callb) ff ba a1 a2
  | QcertCompiler.OpFloatCompare ba -> (pretty_float_compare_binary_op p sym callb) ff ba a1 a2
  | QcertCompiler.OpLt -> pretty_infix_exp p 17 sym callb ("<",1) ff a1 a2
  | QcertCompiler.OpLe -> pretty_infix_exp p 17 sym callb sym.leq ff a1 a2
  | QcertCompiler.OpBagDiff -> pretty_infix_exp p 18 sym callb ("\\",1) ff a1 a2
  | QcertCompiler.OpBagMin -> pretty_infix_exp p 20 sym callb ("{min}",5) ff a1 a2
  | QcertCompiler.OpBagMax -> pretty_infix_exp p 20 sym callb ("{max}",5) ff a1 a2
  | QcertCompiler.OpBagNth -> pretty_infix_exp p 20 sym callb ("{nth}",5) ff a1 a2
  | QcertCompiler.OpContains -> pretty_infix_exp p 16 sym callb sym.sin ff a1 a2
  | QcertCompiler.OpStringConcat -> pretty_infix_exp p 18 sym callb ("^",1) ff a1 a2
  | QcertCompiler.OpStringJoin -> pretty_infix_exp p 16 sym callb ("{join}",5) ff a1 a2
  | QcertCompiler.OpForeignBinary fb -> pretty_foreign_binary_op p sym callb ff (Obj.magic fb) a1 a2
  end


