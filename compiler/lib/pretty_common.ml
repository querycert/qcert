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

open Util
open Compiler.EnhancedCompiler

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
    inheritance = Compiler.Jarray [];
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

let string_of_foreign_data (fd:Compiler.enhanced_data) : string =
  begin match fd with
  | Compiler.Enhancedsqldate td -> raise Not_found
  | Compiler.Enhancedsqldateinterval tp -> raise Not_found
  end

let foreign_data_of_string s =
	raise Not_found

let pretty_foreign_data ff fd =
  begin match fd with
  | Compiler.Enhancedsqldate td -> raise Not_found
  | Compiler.Enhancedsqldateinterval tp -> raise Not_found
  end

let rec pretty_data ff d =
  begin match d with
  | Compiler.Dunit -> fprintf ff "null"
  | Compiler.Dnat n -> fprintf ff "%d" n
  | Compiler.Dfloat f -> fprintf ff "%f" f
  | Compiler.Dbool true -> fprintf ff "true"
  | Compiler.Dbool false -> fprintf ff "false"
  | Compiler.Dstring s -> fprintf ff "\"%s\"" (string_of_char_list s)
  | Compiler.Dcoll dl -> fprintf ff "{@[<hv 0>%a@]}" pretty_coll dl
  | Compiler.Drec rl -> fprintf ff "[@[<hv 0>%a@]]" pretty_rec rl
  | Compiler.Dleft d -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@]" pretty_data d
  | Compiler.Dright d -> fprintf ff "@[<hv 2>right {@,%a@;<0 -2>}@]" pretty_data d
  | Compiler.Dbrand (brands,d) -> fprintf ff "@[<hv 2>brands [@[<hv 0>%a@]] {@,%a@;<0 -2>}@]"
				      pretty_names brands
				      pretty_data d
  | Compiler.Dforeign fd -> pretty_foreign_data ff (Obj.magic fd)
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
  | Compiler.Bottom_UU2080_ -> fprintf ff "%a" pretty_sym sym.bot
  | Compiler.Top_UU2080_ ->  fprintf ff "%a" pretty_sym sym.top
  | Compiler.Unit_UU2080_ -> fprintf ff "Unit"
  | Compiler.Nat_UU2080_ -> fprintf ff "Nat"
  | Compiler.Float_UU2080_ -> fprintf ff "Float"
  | Compiler.Bool_UU2080_ -> fprintf ff "Bool"
  | Compiler.String_UU2080_ -> fprintf ff "String"
  | Compiler.Coll_UU2080_ rc -> fprintf ff "{@[<hv 0>%a@]}" (pretty_rtype_aux sym) rc
  | Compiler.Rec_UU2080_ (Compiler.Closed,rl) -> fprintf ff "[@[<hv 0>%a@]|]" (pretty_rec_type sym) rl
  | Compiler.Rec_UU2080_ (Compiler.Open,rl) -> fprintf ff "[@[<hv 0>%a@]..]" (pretty_rec_type sym) rl
  | Compiler.Either_UU2080_ (r1,r2) -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@,| right {@,%a@;<0 -2>}@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | Compiler.Arrow_UU2080_ (r1,r2) -> fprintf ff "@[<hv 2>(fun %a => %a)@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | Compiler.Brand_UU2080_ bds -> fprintf ff "@[<hv 2>Brands [BRANDS]@]"
  | Compiler.Foreign_UU2080_ rf -> fprintf ff "Foreign"
  end

and pretty_rec_type sym ff rl =
  match rl with
    [] -> ()
  | (ra,rd) :: [] -> fprintf ff "%s : %a" (string_of_char_list ra) (pretty_rtype_aux sym) rd
  | (ra,rd) :: rl' -> fprintf ff "%s : %a;@ %a" (string_of_char_list ra) (pretty_rtype_aux sym) rd (pretty_rec_type sym) rl'

let pretty_drtype_aux sym ff drt =
  match drt with
  | Compiler.Tlocal tr -> fprintf ff "L%a" (pretty_rtype_aux sym) tr
  | Compiler.Tdistr tr -> fprintf ff "D%a" (pretty_rtype_aux sym) tr

let pretty_annotate_annotated_rtype greek subpr ff (at:'a Compiler.type_annotation) =
  let sym = if greek then greeksym else textsym in
  let inf = QUtil.ta_inferred [] at in
  let req = QUtil.ta_required [] at in
  if Compiler.equiv_dec (Compiler.drtype_eqdec Compiler.EnhancedRuntime.compiler_foreign_type []) inf req
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
  | Compiler.NatAbs -> "abs"
  | Compiler.NatLog2 -> "log2"
  | Compiler.NatSqrt -> "sqrt"
  end

let nat_arith_unary_op_of_string s =
  begin match s with
  | "abs" -> Compiler.NatAbs
  | "log2" -> Compiler.NatLog2
  | "sqrt" -> Compiler.NatSqrt
  | _ -> raise Not_found
  end

let pretty_nat_arith_unary_op p sym callb ff ua a =
  pretty_unary_exp sym callb (string_of_nat_arith_unary_op ua) ff a

let string_of_float_arith_unary_op ua =
  begin match ua with
  | Compiler.FloatNeg -> "Fneg"
  | Compiler.FloatSqrt -> "Fsqrt"
  | Compiler.FloatExp -> "Fexp"
  | Compiler.FloatLog -> "Flog"
  | Compiler.FloatLog10 -> "Flog10"
  | Compiler.FloatCeil -> "Fceil"
  | Compiler.FloatFloor -> "Ffloor"
  | Compiler.FloatAbs -> "Fabs"
  end

let float_arith_unary_op_of_string s =
  begin match s with
  | "Fneg" -> Compiler.FloatNeg
  | "Fsqrt" -> Compiler.FloatSqrt
  | "Fexp" -> Compiler.FloatExp
  | "Flog" -> Compiler.FloatLog
  | "Flog10" -> Compiler.FloatLog10
  | "Fceil" -> Compiler.FloatCeil
  | "Ffloor" -> Compiler.FloatFloor
  | _ -> raise Not_found
  end

let pretty_float_arith_unary_op p sym callb ff ua a =
  pretty_unary_exp sym callb (string_of_float_arith_unary_op ua) ff a

let sql_date_component_to_string part =
  begin match part with
  | Compiler.Sql_date_DAY -> "DAY"
  | Compiler.Sql_date_MONTH -> "MONTH"
  | Compiler.Sql_date_YEAR -> "YEAR"
  end

let string_of_foreign_unary_op fu : string =
  begin match fu with
  | Compiler.Enhanced_unary_sql_date_op (Compiler.Uop_sql_date_get_component part) -> "(sql_date_get_component " ^ (sql_date_component_to_string part) ^ ")"
  | Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_from_string -> "sql_date_from_string"
  | Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_interval_from_string -> "sql_date_interval_from_string"
  | Compiler.Enhanced_unary_uri_op Compiler.Uop_uri_encode -> "uri_encode"
  | Compiler.Enhanced_unary_uri_op Compiler.Uop_uri_decode -> "uri_decode"
  end

let foreign_unary_op_of_string s =
  begin match s with
  | "(sql_date_get_component DAY)"->  Compiler.Enhanced_unary_sql_date_op (Compiler.Uop_sql_date_get_component Compiler.Sql_date_DAY)
  | "(sql_date_get_component MONTH)"->  Compiler.Enhanced_unary_sql_date_op (Compiler.Uop_sql_date_get_component Compiler.Sql_date_MONTH)
  | "(sql_date_get_component YEAR)"->  Compiler.Enhanced_unary_sql_date_op (Compiler.Uop_sql_date_get_component Compiler.Sql_date_YEAR)
  | "sql_date_from_string" -> Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_from_string
  | "sql_date_interval_from_string" -> Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_interval_from_string
  | "uri_encode" -> Compiler.Enhanced_unary_uri_op Compiler.Uop_uri_encode
  | "uri_decode" -> Compiler.Enhanced_unary_uri_op Compiler.Uop_uri_decode
  | _ -> raise Not_found
  end

let pretty_foreign_unary_op p sym callb ff fu a =
  pretty_unary_exp sym callb (string_of_foreign_unary_op fu) ff a

let pretty_unary_op p sym callb ff u a =
  begin match u with
  | Compiler.OpIdentity -> pretty_unary_exp sym callb "id" ff a
  | Compiler.OpNeg ->
      if (p > 25)
      then
	fprintf ff "@[<hv 0>%a(%a)@]" pretty_sym sym.neg (callb 0 sym) a
      else
	fprintf ff "@[<hv 0>%a%a@]" pretty_sym sym.neg (callb 25 sym) a
  (* resets precedence back to 0 *)
  | Compiler.OpBag -> fprintf ff "@[<hv 2>{@,%a@;<0 -2>}@]" (callb 0 sym) a
  | Compiler.OpCount -> pretty_unary_exp sym callb "count" ff a
  | Compiler.OpFlatten -> pretty_unary_exp sym callb "flatten" ff a
  | Compiler.OpLeft -> pretty_unary_exp sym callb "left" ff a
  | Compiler.OpRight -> pretty_unary_exp sym callb "right" ff a
  (* resets precedence back to 0 *)
  | Compiler.OpBrand brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "brand" (pretty_squared_names sym) brands (callb 0 sym) a
  (* resets precedence back to 0 *)
  | Compiler.OpRec att -> fprintf ff "@[<hv 2>[ %s :@ %a ]@]" (string_of_char_list att) (callb 0 sym) a
  | Compiler.OpDot att ->
      if p > 23
      then fprintf ff "@[<hv 0>(%a.%s)@]" (callb 23 sym) a (string_of_char_list att)
      else fprintf ff "@[<hv 0>%a.%s@]" (callb 23 sym) a (string_of_char_list att)
  (* resets precedence back to 0 *)
  | Compiler.OpRecRemove att ->
      fprintf ff "@[<hv 0>%a%a%a(%a)@]" pretty_sym sym.neg pretty_sym sym.pi (pretty_squared_names sym) [att] (callb 0 sym) a
  (* resets precedence back to 0 *)
  | Compiler.OpRecProject atts ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.pi (pretty_squared_names sym) atts (callb 0 sym) a
  | Compiler.OpDistinct -> pretty_unary_exp sym callb "distinct" ff a
  | Compiler.OpOrderBy atts ->
      fprintf ff "@[<hv 0>%s%a(%a)@]" "sort" (pretty_squared_names sym) (List.map fst atts) (callb 0 sym) a
  | Compiler.OpToString -> pretty_unary_exp sym callb "toString" ff a
  | Compiler.OpToText -> pretty_unary_exp sym callb "toText" ff a
  | Compiler.OpLength -> pretty_unary_exp sym callb "length" ff a
  | Compiler.OpSubstring (n1,None) -> pretty_unary_exp sym callb ("substring["^(string_of_int n1)^"]") ff a
  | Compiler.OpSubstring (n1,Some n2) -> pretty_unary_exp sym callb ("substring["^(string_of_int n1)^","^(string_of_int n2)^"]") ff a
  | Compiler.OpLike n1 -> pretty_unary_exp sym callb ("like["^(string_of_char_list n1)^"]") ff a
  (* resets precedence back to 0 *)
  | Compiler.OpCast brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "cast" (pretty_squared_names sym) brands (callb p sym) a
  | Compiler.OpUnbrand ->
      if p > 24
      then fprintf ff "@[<hv 0>(!%a)@]" (callb 24 sym) a
      else fprintf ff "@[<hv 0>!%a@]" (callb 24 sym) a
  | Compiler.OpSingleton -> pretty_unary_exp sym callb "singleton" ff a
  | Compiler.OpNatUnary ua -> pretty_nat_arith_unary_op p sym callb ff ua a
  | Compiler.OpNatSum -> pretty_unary_exp sym callb "sum" ff a
  | Compiler.OpNatMean -> pretty_unary_exp sym callb "avg" ff a
  | Compiler.OpNatMin -> pretty_unary_exp sym callb "min" ff a
  | Compiler.OpNatMax -> pretty_unary_exp sym callb "max" ff a
  | Compiler.OpFloatOfNat -> pretty_unary_exp sym callb "Fof_int" ff a
  | Compiler.OpFloatUnary ua -> pretty_float_arith_unary_op p sym callb ff ua a
  | Compiler.OpFloatTruncate -> pretty_unary_exp sym callb "Ftruncate" ff a
  | Compiler.OpFloatSum -> pretty_unary_exp sym callb "Fsum" ff a
  | Compiler.OpFloatMean -> pretty_unary_exp sym callb "Favg" ff a
  | Compiler.OpFloatBagMin -> pretty_unary_exp sym callb "Flist_min" ff a
  | Compiler.OpFloatBagMax -> pretty_unary_exp sym callb "Flist_max" ff a
  | Compiler.OpForeignUnary fu -> pretty_foreign_unary_op p sym callb ff (Obj.magic fu) a
  end

let string_of_nat_arith_binary_op ba =
  begin match ba with
  | Compiler.NatPlus -> "plus"
  | Compiler.NatMinus -> "minus"
  | Compiler.NatMult -> "mult"
  | Compiler.NatMin -> "min"
  | Compiler.NatMax -> "max"
  | Compiler.NatDiv -> "divide"
  | Compiler.NatRem -> "rem"
  end

let nat_arith_binary_op_of_string s =
  begin match s with
  | "plus" -> Compiler.NatPlus
  | "minus" -> Compiler.NatMinus
  | "mult" -> Compiler.NatMult
  | "min" -> Compiler.NatMin
  | "max" -> Compiler.NatMax
  | "divide" -> Compiler.NatDiv
  | "rem" -> Compiler.NatRem
  | _ -> raise Not_found
  end

let pretty_nat_arith_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | Compiler.NatPlus -> pretty_infix_exp p 18 sym callb ("+",1) ff a1 a2
  | Compiler.NatMinus -> pretty_infix_exp p 18 sym callb ("-",1) ff a1 a2
  | Compiler.NatMult -> pretty_infix_exp p 19 sym callb ("*",1) ff a1 a2
  | Compiler.NatMin -> pretty_infix_exp p 20 sym callb ("min",3) ff a1 a2
  | Compiler.NatMax -> pretty_infix_exp p 20 sym callb ("max",3) ff a1 a2
  | Compiler.NatDiv -> pretty_infix_exp p 19 sym callb ("/",1) ff a1 a2
  | Compiler.NatRem -> pretty_infix_exp p 19 sym callb ("%",1) ff a1 a2
  end

let string_of_float_arith_binary_op ba =
  begin match ba with
  | Compiler.FloatPlus -> "float_plus"
  | Compiler.FloatMinus -> "float_minus"
  | Compiler.FloatMult -> "float_mult"
  | Compiler.FloatDiv -> "float_div"
  | Compiler.FloatPow -> "float_pow"
  | Compiler.FloatMin -> "float_min"
  | Compiler.FloatMax -> "float_max"
  end

let float_arith_binary_op_of_string ba =
  begin match ba with
  | "float_plus" -> Compiler.FloatPlus
  | "float_minus" -> Compiler.FloatMinus
  | "float_mult" -> Compiler.FloatMult
  | "float_div" -> Compiler.FloatDiv
  | "float_pow" -> Compiler.FloatPow
  | "float_min" -> Compiler.FloatMin
  | "float_max" -> Compiler.FloatMax
  | _ -> raise Not_found
  end

let string_of_float_compare_binary_op ba =
  begin match ba with
  | Compiler.FloatLt -> "FloatLt"
  | Compiler.FloatLe -> "FloatLe"
  | Compiler.FloatGt -> "FloatGt"
  | Compiler.FloatGe -> "FloatGe"
  end

let float_compare_binary_op_of_string s =
  begin match s with
  | "FloatLt" -> Compiler.FloatLt
  | "FloatLe" -> Compiler.FloatLe
  | "FloatGt" -> Compiler.FloatGt
  | "FloatGe" -> Compiler.FloatGe
  | _ -> raise Not_found
  end

let pretty_float_arith_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | Compiler.FloatPlus ->
     pretty_infix_exp p 18 sym callb ("F+",1) ff a1 a2
  | Compiler.FloatMinus ->
     pretty_infix_exp p 18 sym callb ("F-",1) ff a1 a2
  | Compiler.FloatMult ->
     pretty_infix_exp p 18 sym callb ("F*",1) ff a1 a2
  | Compiler.FloatDiv ->
     pretty_infix_exp p 18 sym callb ("F/",1) ff a1 a2
  | Compiler.FloatPow ->
     pretty_infix_exp p 18 sym callb ("F^",1) ff a1 a2
  | Compiler.FloatMin ->
     pretty_infix_exp p 20 sym callb ("Fmin",3) ff a1 a2
  | Compiler.FloatMax ->
     pretty_infix_exp p 20 sym callb ("Fmax",3) ff a1 a2
  end

let pretty_float_compare_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | Compiler.FloatLt ->
    pretty_infix_exp p 18 sym callb ("F<",1) ff a1 a2
  | Compiler.FloatLe ->
    pretty_infix_exp p 18 sym callb ("F<=",1) ff a1 a2
  | Compiler.FloatGt ->
    pretty_infix_exp p 18 sym callb ("F>",1) ff a1 a2
  | Compiler.FloatGe ->
    pretty_infix_exp p 18 sym callb ("F>=",1) ff a1 a2
  end

let string_of_foreign_binary_op fb =
  begin match fb with
  | Compiler.Bop_sql_date_plus -> "sql_date_plus"
  | Compiler.Bop_sql_date_minus -> "sql_date_minus"
  | Compiler.Bop_sql_date_ne -> "sql_date_ne"
  | Compiler.Bop_sql_date_lt -> "sql_date_lt"
  | Compiler.Bop_sql_date_le -> "sql_date_le"
  | Compiler.Bop_sql_date_gt -> "sql_date_gt"
  | Compiler.Bop_sql_date_ge -> "sql_date_ge"
  | Compiler.Bop_sql_date_interval_between -> "sql_date_interval_between"
  | Compiler.Bop_sql_date_set_component part -> "(sql_date_set_component " ^ (sql_date_component_to_string part) ^ ")"
  end

let foreign_binary_op_of_string fb =
  begin match fb with
  | "sql_date_plus" -> Compiler.Bop_sql_date_plus
  | "sql_date_ne" -> Compiler.Bop_sql_date_ne
  | "sql_date_lt" -> Compiler.Bop_sql_date_lt
  | "sql_date_le" -> Compiler.Bop_sql_date_le
  | "sql_date_gt" -> Compiler.Bop_sql_date_gt
  | "sql_date_ge" -> Compiler.Bop_sql_date_ge
  | "sql_date_interval_between" -> Compiler.Bop_sql_date_interval_between
  | "(sql_date_set_component DAY)"->  Compiler.Bop_sql_date_set_component Compiler.Sql_date_DAY
  | "(sql_date_set_component MONTH)"->  Compiler.Bop_sql_date_set_component Compiler.Sql_date_MONTH
  | "(sql_date_set_component YEAR)"->  Compiler.Bop_sql_date_set_component Compiler.Sql_date_YEAR
  | _ -> raise Not_found
  end

let pretty_foreign_binary_op p sym callb ff fb a1 a2 =
  begin match fb with
  | Compiler.Bop_sql_date_plus ->
      pretty_infix_exp p 18 sym callb ("SD+",1) ff a1 a2
  | Compiler.Bop_sql_date_minus ->
      pretty_infix_exp p 18 sym callb ("SD-",1) ff a1 a2
  | Compiler.Bop_sql_date_ne ->
      pretty_infix_exp p 18 sym callb ("SD!=",1) ff a1 a2
  | Compiler.Bop_sql_date_lt ->
      pretty_infix_exp p 18 sym callb ("SD<",1) ff a1 a2
  | Compiler.Bop_sql_date_le ->
      pretty_infix_exp p 18 sym callb ("SD<=",1) ff a1 a2
  | Compiler.Bop_sql_date_gt ->
      pretty_infix_exp p 18 sym callb ("SD>",1) ff a1 a2
  | Compiler.Bop_sql_date_ge ->
      pretty_infix_exp p 18 sym callb ("SD>=",1) ff a1 a2
  | Compiler.Bop_sql_date_interval_between ->
      pretty_infix_exp p 18 sym callb ("SDD_be",1) ff a1 a2
  | Compiler.Bop_sql_date_set_component Compiler.Sql_date_YEAR ->
      pretty_infix_exp p 18 sym callb ("SDsY",1) ff a1 a2
  | Compiler.Bop_sql_date_set_component Compiler.Sql_date_MONTH ->
      pretty_infix_exp p 18 sym callb ("SDsM",1) ff a1 a2
  | Compiler.Bop_sql_date_set_component Compiler.Sql_date_DAY ->
      pretty_infix_exp p 18 sym callb ("SDsD",1) ff a1 a2
  end

let string_of_binary_op b =
  begin match b with
  | Compiler.OpEqual -> "aeq"
  | Compiler.OpBagUnion -> "aunion"
  | Compiler.OpRecConcat -> "aconcat"
  | Compiler.OpRecMerge -> "amergeconcat"
  | Compiler.OpAnd -> "aand"
  | Compiler.OpOr -> "aor"
  | Compiler.OpNatBinary ba -> string_of_nat_arith_binary_op ba
  | Compiler.OpFloatBinary ba -> string_of_float_arith_binary_op ba
  | Compiler.OpFloatCompare ba -> string_of_float_compare_binary_op ba
  | Compiler.OpLt ->  "alt"
  | Compiler.OpLe -> "ale"
  | Compiler.OpBagDiff -> "aminus"
  | Compiler.OpBagMin -> "amin"
  | Compiler.OpBagMax -> "amax"
  | Compiler.OpBagNth -> "anth"
  | Compiler.OpContains -> "acontains"
  | Compiler.OpStringConcat -> "asconcat"
  | Compiler.OpStringJoin -> "asjoin"
  | Compiler.OpForeignBinary fb -> string_of_foreign_binary_op (Obj.magic fb)
  end

let pretty_binary_op p sym callb ff b a1 a2 =
  begin match b with
  | Compiler.OpEqual -> pretty_infix_exp p 15 sym callb ("=",1) ff a1 a2
  | Compiler.OpBagUnion -> pretty_infix_exp p 18 sym callb sym.cup ff a1 a2
  | Compiler.OpRecConcat -> pretty_infix_exp p 19 sym callb ("[+]",3) ff a1 a2
  | Compiler.OpRecMerge -> pretty_infix_exp p 18 sym callb ("[*]",3) ff a1 a2
  | Compiler.OpAnd -> pretty_infix_exp p 19 sym callb sym.wedge ff a1 a2
  | Compiler.OpOr -> pretty_infix_exp p 18 sym callb sym.vee ff a1 a2
  | Compiler.OpNatBinary ba -> (pretty_nat_arith_binary_op p sym callb) ff ba a1 a2
  | Compiler.OpFloatBinary ba -> (pretty_float_arith_binary_op p sym callb) ff ba a1 a2
  | Compiler.OpFloatCompare ba -> (pretty_float_compare_binary_op p sym callb) ff ba a1 a2
  | Compiler.OpLt -> pretty_infix_exp p 17 sym callb ("<",1) ff a1 a2
  | Compiler.OpLe -> pretty_infix_exp p 17 sym callb sym.leq ff a1 a2
  | Compiler.OpBagDiff -> pretty_infix_exp p 18 sym callb ("\\",1) ff a1 a2
  | Compiler.OpBagMin -> pretty_infix_exp p 20 sym callb ("{min}",5) ff a1 a2
  | Compiler.OpBagMax -> pretty_infix_exp p 20 sym callb ("{max}",5) ff a1 a2
  | Compiler.OpBagNth -> pretty_infix_exp p 20 sym callb ("{nth}",5) ff a1 a2
  | Compiler.OpContains -> pretty_infix_exp p 16 sym callb sym.sin ff a1 a2
  | Compiler.OpStringConcat -> pretty_infix_exp p 18 sym callb ("^",1) ff a1 a2
  | Compiler.OpStringJoin -> pretty_infix_exp p 16 sym callb ("{join}",5) ff a1 a2
  | Compiler.OpForeignBinary fb -> pretty_foreign_binary_op p sym callb ff (Obj.magic fb) a1 a2
  end


