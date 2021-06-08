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

(* This module contains pretty-printers for intermediate languages *)

open Format

open Util
open RType
open UnaryOperators
open BinaryOperators
open SqlDateComponent
open EnhancedCompiler.EnhancedCompiler
open EnhancedData

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
    inheritance = Coq_jarray [];
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

let string_of_foreign_data (fd:EnhancedData.enhanced_data) : string =
  begin match fd with
  | Coq_enhancedsqldate td -> raise Not_found
  | Coq_enhancedsqldateperiod tp -> raise Not_found
  end

let foreign_data_of_string s =
	raise Not_found

let pretty_foreign_data ff (fd:EnhancedData.enhanced_data) =
  begin match fd with
  | Coq_enhancedsqldate td -> raise Not_found
  | Coq_enhancedsqldateperiod tp -> raise Not_found
  end

let rec pretty_data ff (d:Data.data) =
  begin match d with
  | Coq_dunit -> fprintf ff "null"
  | Coq_dnat n -> fprintf ff "%d" n
  | Coq_dfloat f -> fprintf ff "%f" f
  | Coq_dbool true -> fprintf ff "true"
  | Coq_dbool false -> fprintf ff "false"
  | Coq_dstring s -> fprintf ff "\"%s\"" (string_of_char_list s)
  | Coq_dcoll dl -> fprintf ff "{@[<hv 0>%a@]}" pretty_coll dl
  | Coq_drec rl -> fprintf ff "[@[<hv 0>%a@]]" pretty_rec rl
  | Coq_dleft d -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@]" pretty_data d
  | Coq_dright d -> fprintf ff "@[<hv 2>right {@,%a@;<0 -2>}@]" pretty_data d
  | Coq_dbrand (brands,d) -> fprintf ff "@[<hv 2>brands [@[<hv 0>%a@]] {@,%a@;<0 -2>}@]"
				      pretty_names brands
				      pretty_data d
  | Coq_dforeign fd -> pretty_foreign_data ff (Obj.magic fd)
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
  | Bottom_UU2080_ -> fprintf ff "%a" pretty_sym sym.bot
  | Top_UU2080_ ->  fprintf ff "%a" pretty_sym sym.top
  | Unit_UU2080_ -> fprintf ff "Unit"
  | Nat_UU2080_ -> fprintf ff "Nat"
  | Float_UU2080_ -> fprintf ff "Float"
  | Bool_UU2080_ -> fprintf ff "Bool"
  | String_UU2080_ -> fprintf ff "String"
  | Coll_UU2080_ rc -> fprintf ff "{@[<hv 0>%a@]}" (pretty_rtype_aux sym) rc
  | Rec_UU2080_ (Closed,rl) -> fprintf ff "[@[<hv 0>%a@]|]" (pretty_rec_type sym) rl
  | Rec_UU2080_ (Open,rl) -> fprintf ff "[@[<hv 0>%a@]..]" (pretty_rec_type sym) rl
  | Either_UU2080_ (r1,r2) -> fprintf ff "@[<hv 2>left {@,%a@;<0 -2>}@,| right {@,%a@;<0 -2>}@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | Arrow_UU2080_ (r1,r2) -> fprintf ff "@[<hv 2>(fun %a => %a)@]" (pretty_rtype_aux sym) r1 (pretty_rtype_aux sym) r2
  | Brand_UU2080_ bds -> fprintf ff "@[<hv 2>Brands [BRANDS]@]"
  | Foreign_UU2080_ rf -> fprintf ff "Foreign"
  end

and pretty_rec_type sym ff rl =
  match rl with
    [] -> ()
  | (ra,rd) :: [] -> fprintf ff "%s : %a" (string_of_char_list ra) (pretty_rtype_aux sym) rd
  | (ra,rd) :: rl' -> fprintf ff "%s : %a;@ %a" (string_of_char_list ra) (pretty_rtype_aux sym) rd (pretty_rec_type sym) rl'

let pretty_drtype_aux sym ff drt =
  match drt with
  | DType.Tlocal tr -> fprintf ff "L%a" (pretty_rtype_aux sym) tr
  | DType.Tdistr tr -> fprintf ff "D%a" (pretty_rtype_aux sym) tr

let pretty_annotate_annotated_rtype greek subpr ff (at:'a TDNNRC.type_annotation) =
  let sym = if greek then greeksym else textsym in
  let inf = QUtil.ta_inferred [] at in
  let req = QUtil.ta_required [] at in
  if EquivDec.equiv_dec (DType.drtype_eqdec EnhancedRuntime.EnhancedRuntime.compiler_foreign_type []) inf req
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
  | NatAbs -> "abs"
  | NatLog2 -> "log2"
  | NatSqrt -> "sqrt"
  end

let nat_arith_unary_op_of_string s =
  begin match s with
  | "abs" -> NatAbs
  | "log2" -> NatLog2
  | "sqrt" -> NatSqrt
  | _ -> raise Not_found
  end

let pretty_nat_arith_unary_op p sym callb ff ua a =
  pretty_unary_exp sym callb (string_of_nat_arith_unary_op ua) ff a

let string_of_float_arith_unary_op ua =
  begin match ua with
  | FloatNeg -> "Fneg"
  | FloatSqrt -> "Fsqrt"
  | FloatExp -> "Fexp"
  | FloatLog -> "Flog"
  | FloatLog10 -> "Flog10"
  | FloatCeil -> "Fceil"
  | FloatFloor -> "Ffloor"
  | FloatAbs -> "Fabs"
  end

let float_arith_unary_op_of_string s =
  begin match s with
  | "Fneg" -> FloatNeg
  | "Fsqrt" -> FloatSqrt
  | "Fexp" -> FloatExp
  | "Flog" -> FloatLog
  | "Flog10" -> FloatLog10
  | "Fceil" -> FloatCeil
  | "Ffloor" -> FloatFloor
  | _ -> raise Not_found
  end

let pretty_float_arith_unary_op p sym callb ff ua a =
  pretty_unary_exp sym callb (string_of_float_arith_unary_op ua) ff a

let sql_date_component_to_string part =
  begin match part with
  | Coq_sql_date_DAY -> "DAY"
  | Coq_sql_date_MONTH -> "MONTH"
  | Coq_sql_date_YEAR -> "YEAR"
  end

let string_of_foreign_unary_op fu : string =
  begin match fu with
  | Coq_enhanced_unary_sql_date_op (Coq_uop_sql_date_get_component part) -> "(sql_date_get_component " ^ (sql_date_component_to_string part) ^ ")"
  | Coq_enhanced_unary_sql_date_op Coq_uop_sql_date_from_string -> "sql_date_from_string"
  | Coq_enhanced_unary_sql_date_op Coq_uop_sql_date_period_from_string -> "sql_date_period_from_string"
  | Coq_enhanced_unary_uri_op Coq_uop_uri_encode -> "uri_encode"
  | Coq_enhanced_unary_uri_op Coq_uop_uri_decode -> "uri_decode"
  end

let foreign_unary_op_of_string s =
  begin match s with
  | "(sql_date_get_component DAY)"->  Coq_enhanced_unary_sql_date_op (Coq_uop_sql_date_get_component Coq_sql_date_DAY)
  | "(sql_date_get_component MONTH)"->  Coq_enhanced_unary_sql_date_op (Coq_uop_sql_date_get_component Coq_sql_date_MONTH)
  | "(sql_date_get_component YEAR)"->  Coq_enhanced_unary_sql_date_op (Coq_uop_sql_date_get_component Coq_sql_date_YEAR)
  | "sql_date_from_string" -> Coq_enhanced_unary_sql_date_op Coq_uop_sql_date_from_string
  | "sql_date_period_from_string" -> Coq_enhanced_unary_sql_date_op Coq_uop_sql_date_period_from_string
  | "uri_encode" -> Coq_enhanced_unary_uri_op Coq_uop_uri_encode
  | "uri_decode" -> Coq_enhanced_unary_uri_op Coq_uop_uri_decode
  | _ -> raise Not_found
  end

let pretty_foreign_unary_op p sym callb ff fu a =
  pretty_unary_exp sym callb (string_of_foreign_unary_op fu) ff a

let pretty_unary_op p sym callb ff u a =
  begin match u with
  | OpIdentity -> pretty_unary_exp sym callb "id" ff a
  | OpNeg ->
      if (p > 25)
      then
	fprintf ff "@[<hv 0>%a(%a)@]" pretty_sym sym.neg (callb 0 sym) a
      else
	fprintf ff "@[<hv 0>%a%a@]" pretty_sym sym.neg (callb 25 sym) a
  (* resets precedence back to 0 *)
  | OpBag -> fprintf ff "@[<hv 2>{@,%a@;<0 -2>}@]" (callb 0 sym) a
  | OpCount -> pretty_unary_exp sym callb "count" ff a
  | OpFlatten -> pretty_unary_exp sym callb "flatten" ff a
  | OpLeft -> pretty_unary_exp sym callb "left" ff a
  | OpRight -> pretty_unary_exp sym callb "right" ff a
  (* resets precedence back to 0 *)
  | OpBrand brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "brand" (pretty_squared_names sym) brands (callb 0 sym) a
  (* resets precedence back to 0 *)
  | OpRec att -> fprintf ff "@[<hv 2>[ %s :@ %a ]@]" (string_of_char_list att) (callb 0 sym) a
  | OpDot att ->
      if p > 23
      then fprintf ff "@[<hv 0>(%a.%s)@]" (callb 23 sym) a (string_of_char_list att)
      else fprintf ff "@[<hv 0>%a.%s@]" (callb 23 sym) a (string_of_char_list att)
  (* resets precedence back to 0 *)
  | OpRecRemove att ->
      fprintf ff "@[<hv 0>%a%a%a(%a)@]" pretty_sym sym.neg pretty_sym sym.pi (pretty_squared_names sym) [att] (callb 0 sym) a
  (* resets precedence back to 0 *)
  | OpRecProject atts ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.pi (pretty_squared_names sym) atts (callb 0 sym) a
  | OpDistinct -> pretty_unary_exp sym callb "distinct" ff a
  | OpOrderBy atts ->
      fprintf ff "@[<hv 0>%s%a(%a)@]" "sort" (pretty_squared_names sym) (List.map fst atts) (callb 0 sym) a
  | OpToString -> pretty_unary_exp sym callb "toString" ff a
  | OpToText -> pretty_unary_exp sym callb "toText" ff a
  | OpLength -> pretty_unary_exp sym callb "length" ff a
  | OpSubstring (n1,None) -> pretty_unary_exp sym callb ("substring["^(string_of_int n1)^"]") ff a
  | OpSubstring (n1,Some n2) -> pretty_unary_exp sym callb ("substring["^(string_of_int n1)^","^(string_of_int n2)^"]") ff a
  | OpLike n1 -> pretty_unary_exp sym callb ("like["^(string_of_char_list n1)^"]") ff a
  (* resets precedence back to 0 *)
  | OpCast brands -> fprintf ff "@[<hv 0>%a%a(%a)@]" (pretty_sharp sym) "cast" (pretty_squared_names sym) brands (callb p sym) a
  | OpUnbrand ->
      if p > 24
      then fprintf ff "@[<hv 0>(!%a)@]" (callb 24 sym) a
      else fprintf ff "@[<hv 0>!%a@]" (callb 24 sym) a
  | OpSingleton -> pretty_unary_exp sym callb "singleton" ff a
  | OpNatUnary ua -> pretty_nat_arith_unary_op p sym callb ff ua a
  | OpNatSum -> pretty_unary_exp sym callb "sum" ff a
  | OpNatMean -> pretty_unary_exp sym callb "avg" ff a
  | OpNatMin -> pretty_unary_exp sym callb "min" ff a
  | OpNatMax -> pretty_unary_exp sym callb "max" ff a
  | OpFloatOfNat -> pretty_unary_exp sym callb "Fof_int" ff a
  | OpFloatUnary ua -> pretty_float_arith_unary_op p sym callb ff ua a
  | OpFloatTruncate -> pretty_unary_exp sym callb "Ftruncate" ff a
  | OpFloatSum -> pretty_unary_exp sym callb "Fsum" ff a
  | OpFloatMean -> pretty_unary_exp sym callb "Favg" ff a
  | OpFloatBagMin -> pretty_unary_exp sym callb "Flist_min" ff a
  | OpFloatBagMax -> pretty_unary_exp sym callb "Flist_max" ff a
  | OpForeignUnary fu -> pretty_foreign_unary_op p sym callb ff (Obj.magic fu) a
  end

let string_of_nat_arith_binary_op ba =
  begin match ba with
  | NatPlus -> "plus"
  | NatMinus -> "minus"
  | NatMult -> "mult"
  | NatMin -> "min"
  | NatMax -> "max"
  | NatDiv -> "divide"
  | NatRem -> "rem"
  end

let nat_arith_binary_op_of_string s =
  begin match s with
  | "plus" -> NatPlus
  | "minus" -> NatMinus
  | "mult" -> NatMult
  | "min" -> NatMin
  | "max" -> NatMax
  | "divide" -> NatDiv
  | "rem" -> NatRem
  | _ -> raise Not_found
  end

let pretty_nat_arith_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | NatPlus -> pretty_infix_exp p 18 sym callb ("+",1) ff a1 a2
  | NatMinus -> pretty_infix_exp p 18 sym callb ("-",1) ff a1 a2
  | NatMult -> pretty_infix_exp p 19 sym callb ("*",1) ff a1 a2
  | NatMin -> pretty_infix_exp p 20 sym callb ("min",3) ff a1 a2
  | NatMax -> pretty_infix_exp p 20 sym callb ("max",3) ff a1 a2
  | NatDiv -> pretty_infix_exp p 19 sym callb ("/",1) ff a1 a2
  | NatRem -> pretty_infix_exp p 19 sym callb ("%",1) ff a1 a2
  end

let string_of_float_arith_binary_op ba =
  begin match ba with
  | FloatPlus -> "float_plus"
  | FloatMinus -> "float_minus"
  | FloatMult -> "float_mult"
  | FloatDiv -> "float_div"
  | FloatPow -> "float_pow"
  | FloatMin -> "float_min"
  | FloatMax -> "float_max"
  end

let float_arith_binary_op_of_string ba =
  begin match ba with
  | "float_plus" -> FloatPlus
  | "float_minus" -> FloatMinus
  | "float_mult" -> FloatMult
  | "float_div" -> FloatDiv
  | "float_pow" -> FloatPow
  | "float_min" -> FloatMin
  | "float_max" -> FloatMax
  | _ -> raise Not_found
  end

let string_of_float_compare_binary_op ba =
  begin match ba with
  | FloatLt -> "FloatLt"
  | FloatLe -> "FloatLe"
  | FloatGt -> "FloatGt"
  | FloatGe -> "FloatGe"
  end

let float_compare_binary_op_of_string s =
  begin match s with
  | "FloatLt" -> FloatLt
  | "FloatLe" -> FloatLe
  | "FloatGt" -> FloatGt
  | "FloatGe" -> FloatGe
  | _ -> raise Not_found
  end

let pretty_float_arith_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | FloatPlus ->
     pretty_infix_exp p 18 sym callb ("F+",1) ff a1 a2
  | FloatMinus ->
     pretty_infix_exp p 18 sym callb ("F-",1) ff a1 a2
  | FloatMult ->
     pretty_infix_exp p 18 sym callb ("F*",1) ff a1 a2
  | FloatDiv ->
     pretty_infix_exp p 18 sym callb ("F/",1) ff a1 a2
  | FloatPow ->
     pretty_infix_exp p 18 sym callb ("F^",1) ff a1 a2
  | FloatMin ->
     pretty_infix_exp p 20 sym callb ("Fmin",3) ff a1 a2
  | FloatMax ->
     pretty_infix_exp p 20 sym callb ("Fmax",3) ff a1 a2
  end

let pretty_float_compare_binary_op p sym callb ff ba a1 a2 =
  begin match ba with
  | FloatLt ->
    pretty_infix_exp p 18 sym callb ("F<",1) ff a1 a2
  | FloatLe ->
    pretty_infix_exp p 18 sym callb ("F<=",1) ff a1 a2
  | FloatGt ->
    pretty_infix_exp p 18 sym callb ("F>",1) ff a1 a2
  | FloatGe ->
    pretty_infix_exp p 18 sym callb ("F>=",1) ff a1 a2
  end

let string_of_foreign_binary_op fb =
  begin match fb with
  | Coq_bop_sql_date_plus -> "sql_date_plus"
  | Coq_bop_sql_date_minus -> "sql_date_minus"
  | Coq_bop_sql_date_ne -> "sql_date_ne"
  | Coq_bop_sql_date_lt -> "sql_date_lt"
  | Coq_bop_sql_date_le -> "sql_date_le"
  | Coq_bop_sql_date_gt -> "sql_date_gt"
  | Coq_bop_sql_date_ge -> "sql_date_ge"
  | Coq_bop_sql_date_period_between -> "sql_date_period_between"
  | Coq_bop_sql_date_set_component part -> "(sql_date_set_component " ^ (sql_date_component_to_string part) ^ ")"
  end

let foreign_binary_op_of_string fb =
  begin match fb with
  | "sql_date_plus" -> Coq_bop_sql_date_plus
  | "sql_date_ne" -> Coq_bop_sql_date_ne
  | "sql_date_lt" -> Coq_bop_sql_date_lt
  | "sql_date_le" -> Coq_bop_sql_date_le
  | "sql_date_gt" -> Coq_bop_sql_date_gt
  | "sql_date_ge" -> Coq_bop_sql_date_ge
  | "sql_date_period_between" -> Coq_bop_sql_date_period_between
  | "(sql_date_set_component DAY)"->  Coq_bop_sql_date_set_component Coq_sql_date_DAY
  | "(sql_date_set_component MONTH)"->  Coq_bop_sql_date_set_component Coq_sql_date_MONTH
  | "(sql_date_set_component YEAR)"->  Coq_bop_sql_date_set_component Coq_sql_date_YEAR
  | _ -> raise Not_found
  end

let pretty_foreign_binary_op p sym callb ff fb a1 a2 =
  begin match fb with
  | Coq_bop_sql_date_plus ->
      pretty_infix_exp p 18 sym callb ("SD+",1) ff a1 a2
  | Coq_bop_sql_date_minus ->
      pretty_infix_exp p 18 sym callb ("SD-",1) ff a1 a2
  | Coq_bop_sql_date_ne ->
      pretty_infix_exp p 18 sym callb ("SD!=",1) ff a1 a2
  | Coq_bop_sql_date_lt ->
      pretty_infix_exp p 18 sym callb ("SD<",1) ff a1 a2
  | Coq_bop_sql_date_le ->
      pretty_infix_exp p 18 sym callb ("SD<=",1) ff a1 a2
  | Coq_bop_sql_date_gt ->
      pretty_infix_exp p 18 sym callb ("SD>",1) ff a1 a2
  | Coq_bop_sql_date_ge ->
      pretty_infix_exp p 18 sym callb ("SD>=",1) ff a1 a2
  | Coq_bop_sql_date_period_between ->
      pretty_infix_exp p 18 sym callb ("SDD_be",1) ff a1 a2
  | Coq_bop_sql_date_set_component Coq_sql_date_YEAR ->
      pretty_infix_exp p 18 sym callb ("SDsY",1) ff a1 a2
  | Coq_bop_sql_date_set_component Coq_sql_date_MONTH ->
      pretty_infix_exp p 18 sym callb ("SDsM",1) ff a1 a2
  | Coq_bop_sql_date_set_component Coq_sql_date_DAY ->
      pretty_infix_exp p 18 sym callb ("SDsD",1) ff a1 a2
  end

let string_of_binary_op b =
  begin match b with
  | OpEqual -> "aeq"
  | OpBagUnion -> "aunion"
  | OpRecConcat -> "aconcat"
  | OpRecMerge -> "amergeconcat"
  | OpAnd -> "aand"
  | OpOr -> "aor"
  | OpNatBinary ba -> string_of_nat_arith_binary_op ba
  | OpFloatBinary ba -> string_of_float_arith_binary_op ba
  | OpFloatCompare ba -> string_of_float_compare_binary_op ba
  | OpLt ->  "alt"
  | OpLe -> "ale"
  | OpBagDiff -> "aminus"
  | OpBagMin -> "amin"
  | OpBagMax -> "amax"
  | OpBagNth -> "anth"
  | OpContains -> "acontains"
  | OpStringConcat -> "asconcat"
  | OpStringJoin -> "asjoin"
  | OpForeignBinary fb -> string_of_foreign_binary_op (Obj.magic fb)
  end

let pretty_binary_op p sym callb ff b a1 a2 =
  begin match b with
  | OpEqual -> pretty_infix_exp p 15 sym callb ("=",1) ff a1 a2
  | OpBagUnion -> pretty_infix_exp p 18 sym callb sym.cup ff a1 a2
  | OpRecConcat -> pretty_infix_exp p 19 sym callb ("[+]",3) ff a1 a2
  | OpRecMerge -> pretty_infix_exp p 18 sym callb ("[*]",3) ff a1 a2
  | OpAnd -> pretty_infix_exp p 19 sym callb sym.wedge ff a1 a2
  | OpOr -> pretty_infix_exp p 18 sym callb sym.vee ff a1 a2
  | OpNatBinary ba -> (pretty_nat_arith_binary_op p sym callb) ff ba a1 a2
  | OpFloatBinary ba -> (pretty_float_arith_binary_op p sym callb) ff ba a1 a2
  | OpFloatCompare ba -> (pretty_float_compare_binary_op p sym callb) ff ba a1 a2
  | OpLt -> pretty_infix_exp p 17 sym callb ("<",1) ff a1 a2
  | OpLe -> pretty_infix_exp p 17 sym callb sym.leq ff a1 a2
  | OpBagDiff -> pretty_infix_exp p 18 sym callb ("\\",1) ff a1 a2
  | OpBagMin -> pretty_infix_exp p 20 sym callb ("{min}",5) ff a1 a2
  | OpBagMax -> pretty_infix_exp p 20 sym callb ("{max}",5) ff a1 a2
  | OpBagNth -> pretty_infix_exp p 20 sym callb ("{nth}",5) ff a1 a2
  | OpContains -> pretty_infix_exp p 16 sym callb sym.sin ff a1 a2
  | OpStringConcat -> pretty_infix_exp p 18 sym callb ("^",1) ff a1 a2
  | OpStringJoin -> pretty_infix_exp p 16 sym callb ("{join}",5) ff a1 a2
  | OpForeignBinary fb -> pretty_foreign_binary_op p sym callb ff (Obj.magic fb) a1 a2
  end

