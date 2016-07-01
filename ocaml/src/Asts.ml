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

(* This module contains parsing utilities *)

open Compiler.EnhancedCompiler
open Compiler
open SExp


(********)
(* ASTs *)
(********)

type sexp_ast = sexp

type io_ast = Data.data
type json_ast = Data.data

type rule_ast = string * Rule.rule
type camp = Pattern.pat
type algenv = Compiler.algenv
type nrc = Compiler.nrc
type dnrc = (Compiler.__, algenv) Compiler.dnrc
type nrcmr = (Compiler.var * Compiler.dlocalization) list * Compiler.nrcmr
type cldmr = Compiler.cld_mrl

type rORc_ast =
  | RuleAst of Rule.rule
  | CampAst of Pattern.pat
      
type oql_ast = OQL.expr

(****************
 * AST <-> SExp *
 ****************)

let coq_string_to_sstring (cl:char list) : sexp =
  SString (Util.string_of_char_list cl)
let dbrands_to_sexp (bs:(char list) list) : sexp list =
  List.map coq_string_to_sstring bs
let coq_string_list_to_sstring_list = dbrands_to_sexp
    
let sstring_to_coq_string (se:sexp) : char list =
  match se with
  | SString s -> Util.char_list_of_string s
  | _ -> raise (Util.CACo_Error "Not well-formed S-expr for Coq string")
let sexp_to_dbrands (bs:sexp list) : (char list) list =
  List.map sstring_to_coq_string bs
let sstring_list_to_coq_string_list = sexp_to_dbrands

(* Data Section *)
      
let rec data_to_sexp (d : Data.data) : sexp =
  match d with
  | Dunit -> STerm ("dunit", [])
  | Dnat n -> SInt n
  | Dbool b -> SBool b
  | Dstring s -> SString (Util.string_of_char_list s)
  | Dcoll dl -> STerm ("dcoll", List.map data_to_sexp dl)
  | Drec adl -> STerm ("drec", List.map drec_to_sexp adl)
  | Dleft d -> STerm ("dleft", data_to_sexp d :: [])
  | Dright d -> STerm ("dright", data_to_sexp d :: [])
  | Dbrand (bs,d) -> STerm ("dbrand", (STerm ("brands", dbrands_to_sexp bs)) :: (STerm ("value", (data_to_sexp d) :: [])) :: [])
  | Dforeign fdt -> STerm ("dtime_scale", (SString (PrettyIL.string_of_foreign_data (Obj.magic fdt))) :: [])
and drec_to_sexp (ad : char list * Data.data) : sexp =
  STerm ("datt", (SString (Util.string_of_char_list (fst ad))) :: (data_to_sexp (snd ad)) :: [])

let rec sexp_to_data (se:sexp) : Data.data =
  match se with
  | STerm ("dunit", []) -> Dunit
  | SBool b -> Dbool b
  | SInt n -> Dnat n
  | SString s -> Dstring (Util.char_list_of_string s)
  | STerm ("dcoll", sel) ->
      Dcoll (List.map sexp_to_data sel)
  | STerm ("drec", asel) ->
      Drec (List.map sexp_to_drec asel)
  | STerm ("dleft", se' :: []) ->
      Dleft (sexp_to_data se')
  | STerm ("dright", se' :: []) ->
      Dright (sexp_to_data se')
  | STerm ("dbrand", (STerm ("brands", bs)) :: (STerm ("value", se' :: [])) :: []) ->
      Dbrand (sexp_to_dbrands bs, sexp_to_data se')
  | STerm ("dtime_scale", [SString s]) ->
      Dforeign (Obj.magic (PrettyIL.foreign_data_of_string s))
  | STerm (t, _) ->
      raise (Util.CACo_Error ("Not well-formed S-expr with name " ^ t))
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr")
and sexp_to_drec (sel:sexp) : (char list * Data.data) =
  match sel with
  | STerm ("datt", (SString s) :: se :: []) ->
      (Util.char_list_of_string s, sexp_to_data se)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside drec")

(* Operators Section *)

let arithbop_to_sexp (b:arithBOp) : sexp =
  STerm (PrettyIL.string_of_binarith b,[])
  
let sexp_to_arithbop (se:sexp) : arithBOp =
  match se with
  | STerm (s,[]) -> PrettyIL.binarith_of_string s
  | _ ->
      raise  (Util.CACo_Error "Not well-formed S-expr inside arith binop")
  
let binop_to_sexp (b:binOp) : sexp =
  match b with
  | AEq -> STerm ("AEq",[])
  | AUnion -> STerm ("AUnion",[])
  | AConcat -> STerm ("AConcat",[])
  | AMergeConcat -> STerm ("AMergeConcat",[])
  | AAnd -> STerm ("AAnd",[])
  | AOr -> STerm ("AOr",[])
  | ABArith ab -> STerm ("ABArith",[arithbop_to_sexp ab])
  | ALt -> STerm ("ALt",[])
  | ALe -> STerm ("ALe",[])
  | AMinus -> STerm ("AMinus",[])
  | AMin -> STerm ("AMin",[])
  | AMax -> STerm ("AMax",[])
  | AContains -> STerm ("AContains",[])
  | ASConcat -> STerm ("ASConcat",[])
  | AForeignBinaryOp fbop -> SString (PrettyIL.string_of_foreign_binop (Obj.magic fbop))

let sexp_to_binop (se:sexp) : binOp =
  match se with
  | STerm ("AEq",[]) -> AEq
  | STerm ("AUnion",[]) -> AUnion
  | STerm ("AConcat",[]) -> AConcat
  | STerm ("AMergeConcat",[]) -> AMergeConcat
  | STerm ("AAnd",[]) -> AAnd
  | STerm ("AOr",[]) -> AOr
  | STerm ("ABArith",[se']) -> ABArith (sexp_to_arithbop se')
  | STerm ("ALt",[]) -> ALt
  | STerm ("ALe",[]) -> ALe
  | STerm ("AMinus",[]) -> AMinus
  | STerm ("AMin",[]) -> AMin
  | STerm ("AMax",[]) -> AMax
  | STerm ("AContains",[]) -> AContains
  | STerm ("ASConcat",[]) -> ASConcat
  | SString fbop -> AForeignBinaryOp (Obj.magic (PrettyIL.foreign_binop_of_string fbop))
  (* WARNING: Those are not printed, only parsed *)
  | STerm ("AFloatPlus",[]) -> Enhanced.Ops.Binary.coq_AFloatPlus
  | STerm ("AFloatMinus",[]) -> Enhanced.Ops.Binary.coq_AFloatMinus
  | STerm ("AFloatMult",[]) -> Enhanced.Ops.Binary.coq_AFloatMult
  | STerm ("AFloatDiv",[]) -> Enhanced.Ops.Binary.coq_AFloatDiv
  | STerm ("AFloatPow",[]) -> Enhanced.Ops.Binary.coq_AFloatPow
  | STerm ("AFloatMin",[]) -> Enhanced.Ops.Binary.coq_AFloatMin
  | STerm ("AFloatMax",[]) -> Enhanced.Ops.Binary.coq_AFloatMax
  | STerm ("AFloatNe",[]) -> Enhanced.Ops.Binary.coq_AFloatNe
  | STerm ("AFloatLt",[]) -> Enhanced.Ops.Binary.coq_AFloatLt
  | STerm ("AFloatLe",[]) -> Enhanced.Ops.Binary.coq_AFloatLe
  | STerm ("AFloatGt",[]) -> Enhanced.Ops.Binary.coq_AFloatGt
  | STerm ("AFloatGe",[]) -> Enhanced.Ops.Binary.coq_AFloatGe
  | STerm ("ATimeAs",[]) -> Enhanced.Ops.Binary.coq_ATimeAs
  | STerm ("ATimeShift",[]) -> Enhanced.Ops.Binary.coq_ATimeShift
  | STerm ("ATimeNe",[]) -> Enhanced.Ops.Binary.coq_ATimeNe
  | STerm ("ATimeLt",[]) -> Enhanced.Ops.Binary.coq_ATimeLt
  | STerm ("ATimeLe",[]) -> Enhanced.Ops.Binary.coq_ATimeLe
  | STerm ("ATimeGt",[]) -> Enhanced.Ops.Binary.coq_ATimeGt
  | STerm ("ATimeGe",[]) -> Enhanced.Ops.Binary.coq_ATimeGe
  | STerm ("ATimeDurationFromScale",[]) -> Enhanced.Ops.Binary.coq_ATimeDurationFromScale
  | STerm ("ATimeDurationBetween",[]) -> Enhanced.Ops.Binary.coq_ATimeDurationBetween
  | STerm (t, _) ->
      raise (Util.CACo_Error ("Not well-formed S-expr inside arith binop with name " ^ t))
  | _ -> raise  (Util.CACo_Error "Not well-formed S-expr inside arith binop")

let arithuop_to_sexp (b:arithUOp) : sexp =
  STerm (PrettyIL.string_of_unarith b,[])

let sexp_to_arithuop (se:sexp) : arithUOp =
  match se with
  | STerm (s,[]) -> PrettyIL.unarith_of_string s
  | _ ->
      raise  (Util.CACo_Error "Not well-formed S-expr inside arith unop")

let unop_to_sexp (u:unaryOp) : sexp =
  match u with
  | AIdOp -> STerm ("AIdOp",[])
  | AUArith au -> STerm ("AUArith", [arithuop_to_sexp au])
  | ANeg -> STerm ("ANeg",[])
  | AColl -> STerm ("AColl",[])
  | ACount -> STerm ("ACount",[])
  | AFlatten -> STerm ("AFlatten",[])
  | ALeft -> STerm ("ALeft",[])
  | ARight -> STerm ("ARight",[])
  | ABrand bl -> STerm ("ABrand", dbrands_to_sexp bl)
  | ARec s -> STerm ("ARec", [coq_string_to_sstring s])
  | ADot s -> STerm ("ADot", [coq_string_to_sstring s])
  | ARecRemove s -> STerm ("ARecRemove", [coq_string_to_sstring s])
  | ARecProject sl -> STerm ("ARecProject", coq_string_list_to_sstring_list sl)
  | ADistinct -> STerm ("ADistinct",[])
  | ASum -> STerm ("ASum",[])
  | AArithMean -> STerm ("AArithMean",[])
  | AToString -> STerm ("AToString",[])
  | ACast bl -> STerm ("ACast", dbrands_to_sexp bl)
  | AUnbrand -> STerm ("AUnbrand",[])
  | ASingleton -> STerm ("ASingleton",[])
  | ANumMin -> STerm ("ANumMin",[])
  | ANumMax -> STerm ("ANumMax",[])
  | AForeignUnaryOp fuop -> SString (PrettyIL.string_of_foreign_unop (Obj.magic fuop))
	
let sexp_to_unop (se:sexp) : unaryOp =
  match se with
  | STerm ("AIdOp",[]) -> AIdOp
  | STerm ("AUArith", [se']) ->
      let au = sexp_to_arithuop se' in
      AUArith au
  | STerm ("ANeg",[]) -> ANeg
  | STerm ("AColl",[]) -> AColl
  | STerm ("ACount",[]) -> ACount
  | STerm ("AFlatten",[]) -> AFlatten
  | STerm ("ALeft",[]) -> ALeft
  | STerm ("ARight",[]) -> ARight
  | STerm ("ABrand", bl) -> ABrand (sexp_to_dbrands bl)
  | STerm ("ARec", [se']) -> ARec (sstring_to_coq_string se')
  | STerm ("ADot", [se']) -> ADot (sstring_to_coq_string se')
  | STerm ("ARecRemove", [se']) -> ARecRemove (sstring_to_coq_string se')
  | STerm ("ARecProject", sl) -> ARecProject (sstring_list_to_coq_string_list sl)
  | STerm ("ADistinct",[]) -> ADistinct
  | STerm ("ASum",[]) -> ASum
  | STerm ("AArithMean",[]) -> AArithMean
  | STerm ("AToString",[]) -> AToString
  | STerm ("ACast", bl) -> ACast (sexp_to_dbrands bl)
  | STerm ("AUnbrand",[]) -> AUnbrand
  | STerm ("ASingleton",[]) -> ASingleton
  | STerm ("ANumMin",[]) -> ANumMin
  | STerm ("ANumMax",[]) -> ANumMax
  | SString s -> AForeignUnaryOp (Obj.magic (PrettyIL.foreign_unop_of_string s))
  (* WARNING: Those are not printed, only parsed *)
  | STerm ("AFloatNeg",[]) -> Enhanced.Ops.Unary.coq_AFloatNeg
  | STerm ("AFloatSqrt",[]) -> Enhanced.Ops.Unary.coq_AFloatSqrt
  | STerm ("AFloatExp",[]) -> Enhanced.Ops.Unary.coq_AFloatExp
  | STerm ("AFloatLog",[]) -> Enhanced.Ops.Unary.coq_AFloatLog
  | STerm ("AFloatLog10",[]) -> Enhanced.Ops.Unary.coq_AFloatLog10
  | STerm ("AFloatOfInt",[]) -> Enhanced.Ops.Unary.coq_AFloatOfInt
  | STerm ("AFloatCeil",[]) -> Enhanced.Ops.Unary.coq_AFloatCeil
  | STerm ("AFloatFloor",[]) -> Enhanced.Ops.Unary.coq_AFloatFloor
  | STerm ("AFloatTruncate",[]) -> Enhanced.Ops.Unary.coq_AFloatTruncate
  | STerm ("AFloatAbs",[]) -> Enhanced.Ops.Unary.coq_AFloatAbs
  | STerm ("AFloatSum",[]) -> Enhanced.Ops.Unary.coq_AFloatSum
  | STerm ("AFloatArithMean",[]) -> Enhanced.Ops.Unary.coq_AFloatArithMean
  | STerm ("AFloatListMin",[]) -> Enhanced.Ops.Unary.coq_AFloatListMin
  | STerm ("AFloatListMax",[]) -> Enhanced.Ops.Unary.coq_AFloatListMax
  | STerm ("ATimeToSscale",[]) -> Enhanced.Ops.Unary.coq_ATimeToSscale
  | STerm ("ATimeFromString",[]) -> Enhanced.Ops.Unary.coq_ATimeFromString
  | STerm ("ATimeDurationFromString",[]) -> Enhanced.Ops.Unary.coq_ATimeDurationFromString
  | STerm (t, _) ->
      raise (Util.CACo_Error ("Not well-formed S-expr inside unop with name " ^ t))
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside unop")

(* CAMP Section *)
(* TBD *)

(* NRA Section *)

let rec alg_to_sexp (op : algenv) : sexp =
  match op with
  | ANID -> STerm ("ANID",[])
  | ANConst d -> STerm ("ANConst", [data_to_sexp d])
  | ANBinop (b, op1, op2) -> STerm ("ANBinop", (binop_to_sexp b) :: [alg_to_sexp op1;alg_to_sexp op2])
  | ANUnop (u, op1) -> STerm ("ANUnop", (unop_to_sexp u) :: [alg_to_sexp op1])
  | ANMap (op1,op2) -> STerm ("ANMap", [alg_to_sexp op1;alg_to_sexp op2])
  | ANMapConcat (op1,op2) -> STerm ("ANMapConcat", [alg_to_sexp op1;alg_to_sexp op2])
  | ANProduct (op1,op2) -> STerm ("ANProduct", [alg_to_sexp op1;alg_to_sexp op2])
  | ANSelect (op1,op2) -> STerm ("ANSelect", [alg_to_sexp op1;alg_to_sexp op2])
  | ANDefault (op1,op2) -> STerm ("ANDefault", [alg_to_sexp op1;alg_to_sexp op2])
  | ANEither (op1,op2) -> STerm ("ANEither", [alg_to_sexp op1;alg_to_sexp op2])
  | ANEitherConcat (op1,op2) -> STerm ("ANEitherConcat", [alg_to_sexp op1;alg_to_sexp op2])
  | ANApp (op1,op2) -> STerm ("ANApp", [alg_to_sexp op1;alg_to_sexp op2])
  | ANGetConstant sl -> STerm ("ANGetConstant", [coq_string_to_sstring sl])
  | ANEnv -> STerm ("ANEnv",[])
  | ANAppEnv (op1,op2) -> STerm ("ANAppEnv", [alg_to_sexp op1;alg_to_sexp op2])
  | ANMapEnv op1 -> STerm ("ANMapEnv", [alg_to_sexp op1])

let rec sexp_to_alg (se : sexp) : algenv =
  match se with
  | STerm ("ANID",[]) -> ANID
  | STerm ("ANConst", [d]) -> ANConst (sexp_to_data d)
  | STerm ("ANBinop", bse :: [se1;se2]) ->
      let b = sexp_to_binop bse in
      ANBinop (b, sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANUnop", use :: [se1]) ->
      let u = sexp_to_unop use in
      ANUnop (u, sexp_to_alg se1)
  | STerm ("ANMap", [se1;se2]) -> ANMap (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANMapConcat", [se1;se2]) -> ANMapConcat (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANProduct", [se1;se2]) -> ANProduct (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANSelect", [se1;se2]) -> ANSelect (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANDefault", [se1;se2]) -> ANDefault (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANEither", [se1;se2]) -> ANEither (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANEitherConcat", [se1;se2]) -> ANEitherConcat (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANApp", [se1;se2]) -> ANApp (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANGetConstant", [sl]) -> ANGetConstant (sstring_to_coq_string sl)
  | STerm ("ANEnv",[]) -> ANEnv
  | STerm ("ANAppEnv", [se1;se2]) -> ANAppEnv (sexp_to_alg se1, sexp_to_alg se2)
  | STerm ("ANMapEnv", [se1]) -> ANMapEnv (sexp_to_alg se1)
  | STerm (t, _) ->
      raise (Util.CACo_Error ("Not well-formed S-expr inside alg with name " ^ t))
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside alg")

(* NNRC Section *)

let rec nrc_to_sexp (n : nrc) : sexp =
  match n with
  | NRCVar v -> STerm ("NRCVar", [SString (Util.string_of_char_list v)])
  | NRCConst d -> STerm ("NRCConst", [data_to_sexp d])
  | NRCBinop (b, n1, n2) -> STerm ("NRCBinop", (binop_to_sexp b) :: [nrc_to_sexp n1;nrc_to_sexp n2])
  | NRCUnop (u, n1) -> STerm ("NRCUnop", (unop_to_sexp u) :: [nrc_to_sexp n1])
  | NRCLet (v, n1, n2) -> STerm ("NRCLet", (SString (Util.string_of_char_list v)) :: [nrc_to_sexp n1;nrc_to_sexp n2])
  | NRCFor (v, n1, n2) -> STerm ("NRCFor", (SString (Util.string_of_char_list v)) :: [nrc_to_sexp n1;nrc_to_sexp n2])
  | NRCIf (n1, n2, n3) -> STerm ("NRCIf", [nrc_to_sexp n1;nrc_to_sexp n2;nrc_to_sexp n3])
  | NRCEither (n1,v1,n2,v2,n3) -> STerm ("NRCEither",
					 (SString (Util.string_of_char_list v1))
					 :: (SString (Util.string_of_char_list v2))
					 :: [nrc_to_sexp n1;nrc_to_sexp n2;nrc_to_sexp n3])

let rec sexp_to_nrc (se:sexp) : nrc =
  match se with
  | STerm ("NRCVar", [SString v]) -> NRCVar (Util.char_list_of_string v)
  | STerm ("NRCConst", [d]) -> NRCConst (sexp_to_data d)
  | STerm ("NRCBinop", b :: [n1;n2]) -> NRCBinop (sexp_to_binop b, sexp_to_nrc n1, sexp_to_nrc n2)
  | STerm ("NRCUnop", u :: [n1]) -> NRCUnop (sexp_to_unop u, sexp_to_nrc n1)
  | STerm ("NRCLet", (SString v) :: [n1;n2]) -> NRCLet (Util.char_list_of_string v, sexp_to_nrc n1, sexp_to_nrc n2)
  | STerm ("NRCFor", (SString v) :: [n1;n2]) -> NRCFor (Util.char_list_of_string v, sexp_to_nrc n1, sexp_to_nrc n2)
  | STerm ("NRCIf", [n1;n2;n3]) -> NRCIf (sexp_to_nrc n1, sexp_to_nrc n2, sexp_to_nrc n3)
  | STerm ("NRCEither", (SString v1) :: (SString v2) :: [n1;n2;n3]) ->
      NRCEither (sexp_to_nrc n1,Util.char_list_of_string v1,sexp_to_nrc n2,Util.char_list_of_string v2,sexp_to_nrc n3)
  | STerm (t, _) ->
      raise (Util.CACo_Error ("Not well-formed S-expr inside nrc with name " ^ t))
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside nrc")

(* NNRCMR section *)

let var_to_sexp (v:var) : sexp =
  SString (Util.string_of_char_list v)

let opt_var_to_sexp (vo:var option) : sexp list =
  match vo with
  | None -> []
  | Some v -> [var_to_sexp v]
    
let sexp_to_var (se:sexp) : var =
  match se with
  | SString v -> Util.char_list_of_string v
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside var")

let sexp_to_var_opt (sel:sexp list) : var option =
  match sel with
  | [] -> None
  | [se] -> Some (sexp_to_var se)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside optional var")

let var_list_to_sexp (vl:var list) : sexp list =
  map (fun v -> (SString (Util.string_of_char_list v))) vl

let sexp_to_var_list (sel:sexp list) =
  List.map sexp_to_var sel

let params_to_sexp (vl:var list) : sexp =
  STerm ("params", var_list_to_sexp vl)

let sexp_to_params (se:sexp) =
  match se with
  | STerm ("params", vars) -> sexp_to_var_list vars
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside var list")

let fun_to_sexp (f:(var list * nrc)) : sexp =
  STerm ("lambda", (params_to_sexp (fst f)) :: (nrc_to_sexp (snd f)) :: [])

let sexp_to_fun (se:sexp) : (var list * nrc) =
  match se with
  | STerm ("lambda", params :: sen :: []) ->
      (sexp_to_params params, sexp_to_nrc sen)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside lambda")

let unary_fun_to_sexp (f:var * nrc) : sexp =
  fun_to_sexp ([fst f], snd f)

let sexp_to_unary_fun (se:sexp) : var * nrc =
  match sexp_to_fun se with
  | ([var], n) -> (var, n)
  | _ ->
      raise (Util.CACo_Error "Map or Reduce lambda isn't unary")
  
let binary_fun_to_sexp (f:(var * var) * nrc) : sexp =
  fun_to_sexp ([fst (fst f); (snd (fst f))], snd f)

let sexp_to_binary_fun (se:sexp) : (var * var) * nrc =
  match sexp_to_fun se with
  | ([var1; var2], n) -> ((var1, var2), n)
  | _ ->
      raise (Util.CACo_Error "Map or Reduce lambda isn't binary")
  
    
let map_fun_to_sexp (mf:map_fun) =
  match mf with
  | MapDist f -> STerm ("MapDist", (unary_fun_to_sexp f)::[])
  | MapDistFlatten f -> STerm ("MapDistFlatten", (unary_fun_to_sexp f)::[])
  | MapScalar f -> STerm ("MapScalar", (unary_fun_to_sexp f)::[])

let sexp_to_map_fun (se:sexp) =
  match se with
  | STerm ("MapDist", sef::[]) -> MapDist (sexp_to_unary_fun sef)
  | STerm ("MapDistFlatten", sef::[]) -> MapDistFlatten (sexp_to_unary_fun sef)
  | STerm ("MapScalar", sef::[]) -> MapScalar (sexp_to_unary_fun sef)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside map_fun")


let numeric_type_to_sexp nt =
  match nt with
  | Enhanced_numeric_int -> SString "Enhanced_numeric_int"
  | Enhanced_numeric_float -> SString "Enhanced_numeric_float"

let sexp_to_numeric_type se =
  match se with
  | SString "Enhanced_numeric_int" -> Enhanced_numeric_int
  | SString "Enhanced_numeric_float" -> Enhanced_numeric_float
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside numeric_type")


let reduce_op_to_sexp se =
  match se with
  | RedOpCount -> STerm ("RedOpCount",[])
  | RedOpSum nt -> STerm ("RedOpSum", (numeric_type_to_sexp nt)::[])
  | RedOpMin nt -> STerm ("RedOpMin", (numeric_type_to_sexp nt)::[])
  | RedOpMax nt -> STerm ("RedOpMax", (numeric_type_to_sexp nt)::[])
  | RedOpArithMean nt -> STerm ("RedOpArithMean", (numeric_type_to_sexp nt)::[])
  | RedOpStats nt -> STerm ("RedOpStats", (numeric_type_to_sexp nt)::[])

let sexp_to_reduce_op se =
  match se with
  | STerm ("RedOpCount",[]) -> RedOpCount
  | STerm ("RedOpSum", nt::[]) -> RedOpSum (sexp_to_numeric_type nt)
  | STerm ("RedOpMin", nt::[]) -> RedOpMin (sexp_to_numeric_type nt)
  | STerm ("RedOpMax", nt::[]) -> RedOpMax (sexp_to_numeric_type nt)
  | STerm ("RedOpArithMean", nt::[]) -> RedOpArithMean (sexp_to_numeric_type nt)
  | STerm ("RedOpStats", nt::[]) -> RedOpStats (sexp_to_numeric_type nt)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside reduce_op")


let reduce_fun_to_sexp (rf:reduce_fun) =
  match rf with
  | RedId -> STerm ("RedId", [])
  | RedCollect f -> STerm ("RedCollect", (unary_fun_to_sexp f)::[])
  | RedOp ro -> STerm ("foreign_reduce_op", (reduce_op_to_sexp (Obj.magic ro))::[])
  | RedSingleton -> STerm ("RedSingleton", [])

let sexp_to_reduce_fun (se:sexp) =
  match se with
  | STerm ("RedId", []) -> RedId
  | STerm ("RedCollect", f::[]) -> RedCollect (sexp_to_unary_fun f)
  | STerm ("foreign_reduce_op", ro::[]) -> RedOp (Obj.magic (sexp_to_reduce_op ro))
  | STerm ("RedSingleton", []) -> RedSingleton
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside reduce_fun")


let mr_to_sexp (mr:mr) : sexp =
  STerm ("mr",
	 (STerm ("mr_input", (SString (Util.string_of_char_list mr.mr_input))::[]))
	 :: (STerm ("mr_output", (SString (Util.string_of_char_list mr.mr_output))::[]))
	 :: (map_fun_to_sexp mr.mr_map)
	 :: (reduce_fun_to_sexp mr.mr_reduce)
	 :: [])

let sexp_to_mr (se:sexp) : mr =
  match se with
  | STerm ("mr",
	   (STerm ("mr_input", (SString input)::[]))
	   :: (STerm ("mr_output", (SString output)::[]))
	   :: map
	   :: reduce
	   :: [])
    ->
      { mr_input = Util.char_list_of_string input;
	mr_output = Util.char_list_of_string output;
	mr_map = sexp_to_map_fun map;
	mr_reduce = sexp_to_reduce_fun reduce }
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside mr")


let mr_chain_to_sexp (mrl:mr list) : sexp list =
  List.map mr_to_sexp mrl

let sexp_to_mr_chain (sel:sexp list) : mr list =
  List.map sexp_to_mr sel


let loc_to_sexp l =
  match l with
  | Vlocal -> SString "Vscalar"
  | Vdistr -> SString "Vdistributed"

let sexp_to_loc (se:sexp) =
  match se with
  | SString "Vscalar" -> Vlocal
  | SString "Vdistributed" -> Vdistr
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside dlocalization")


let var_loc_to_sexp (v,l) =
  STerm ("var_loc", (SString (Util.string_of_char_list v))::(loc_to_sexp l)::[])
    
let sexp_to_var_loc (se:sexp) =
  match se with
  | STerm ("var_loc", (SString v)::l::[]) ->
      (Util.char_list_of_string v, sexp_to_loc l)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside var-dlocalization pair")
    
let var_locs_to_sexp env : sexp list =
  map var_loc_to_sexp env

let sexp_to_var_locs (se:sexp list) =
  map sexp_to_var_loc se


let mr_last_to_sexp (last: (var list * nrc) * (var * dlocalization) list) =
  match last with
  | (f, var_locs)
    ->
      (STerm ("mr_last",
	      (fun_to_sexp f) :: (var_locs_to_sexp var_locs)))

let sexp_to_mr_last (se:sexp) : (var list * nrc) * (var * dlocalization) list =
  match se with
  | STerm ("mr_last", f :: var_locs) ->
      (sexp_to_fun f, sexp_to_var_locs var_locs)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside mr_last")

let nrcmr_to_sexp (n:nrcmr) : sexp =
  let (env,nrcmr) = n in
  STerm ("nrcmr",
	 (STerm ("mr_env", var_locs_to_sexp env))
	 :: (STerm ("mr_chain", mr_chain_to_sexp (nrcmr.mr_chain)))
	 :: (mr_last_to_sexp nrcmr.mr_last)
	 :: [])

let sexp_to_nrcmr (se:sexp) : nrcmr =
  match se with
  | STerm ("nrcmr",
	   (STerm ("mr_env", env))
	   :: (STerm ("mr_chain", chain))
	   :: last
	   :: [])
    ->
      (sexp_to_var_locs env,
       { mr_chain = sexp_to_mr_chain chain;
	 mr_last = sexp_to_mr_last last })
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside nrcmr")

(* CldMR section *)

let cld_map_fun_to_sexp (mf:cld_map_fun) =
  match mf with
  | CldMapId f -> STerm ("CldMapId", (unary_fun_to_sexp f)::[])
  | CldMapFlatten f -> STerm ("CldMapFlatten", (unary_fun_to_sexp f)::[])

let sexp_to_cld_map_fun (se:sexp) : cld_map_fun =
  match se with
  | STerm ("CldMapId", sef::[]) -> CldMapId (sexp_to_unary_fun sef)
  | STerm ("CldMapFlatten", sef::[]) -> CldMapFlatten (sexp_to_unary_fun sef)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_map_fun")


let cld_map_emit_to_sexp (me:cld_map_emit) =
  match me with
  | CldEmitDist -> STerm ("CldEmitDist", [])
  | CldEmitCollect i -> STerm ("CldEmitCollect", (SInt i)::[])

let sexp_to_cld_map_emit (se:sexp) : cld_map_emit =
  match se with
  | STerm ("CldEmitDist", []) -> CldEmitDist
  | STerm ("CldEmitCollect", (SInt i)::[]) -> CldEmitCollect i
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_map_emit")


let cld_numeric_type_to_sexp nt =
  match nt with
  | Cld_int -> SString "Cld_int"
  | Cld_float -> SString "Cld_float"

let sexp_to_cld_numeric_type se =
  match se with
  | SString "Cld_int" -> Cld_int
  | SString "Cld_float" -> Cld_float
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_numeric_type")


let cld_reduce_op_to_sexp se =
  match se with
  | CldRedOpCount -> STerm ("CldRedOpCount",[])
  | CldRedOpSum nt -> STerm ("CldRedOpSum", (cld_numeric_type_to_sexp nt)::[])
  | CldRedOpStats nt -> STerm ("CldRedOpStats", (cld_numeric_type_to_sexp nt)::[])

let sexp_to_cld_reduce_op se =
  match se with
  | STerm ("CldRedOpCount",[]) -> CldRedOpCount
  | STerm ("CldRedOpSum", nt::[]) -> CldRedOpSum (sexp_to_cld_numeric_type nt)
  | STerm ("CldRedOpStats", nt::[]) -> CldRedOpStats (sexp_to_cld_numeric_type nt)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_reduce_op")


let cld_reduce_fun_to_sexp (rf:cld_reduce_fun) =
  match rf with
  | CldRedId -> STerm ("CldRedId", [])
  | CldRedAggregate (fred,frered) -> STerm ("CldRedAggregate", (binary_fun_to_sexp fred)::(unary_fun_to_sexp frered)::[])
  | CldRedOp ro -> STerm ("CldRedOp", (cld_reduce_op_to_sexp (Obj.magic ro))::[])

let sexp_to_cld_reduce_fun (se:sexp) : cld_reduce_fun =
  match se with
  | STerm ("CldRedId", []) -> CldRedId
  | STerm ("CldRedAggregate", fred::frered::[]) -> CldRedAggregate (sexp_to_binary_fun fred, sexp_to_unary_fun frered)
  | STerm ("CldRedOp", ro::[]) -> CldRedOp (Obj.magic (sexp_to_cld_reduce_op ro))
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_reduce_fun")


let cld_red_opt_to_sexp red =
  match red with
  | None -> []
  | Some ff ->
      (cld_reduce_fun_to_sexp ff.reduce_fun0) :: (STerm ("reduce_output", opt_var_to_sexp ff.reduce_output)) :: []

let sexp_to_cld_red_opt sel =
  match sel with
  | [] -> None
  | reduce :: (STerm ("reduce_output", reduce_out)) :: [] ->
      Some { reduce_fun0 = sexp_to_cld_reduce_fun reduce;
	     reduce_output = sexp_to_var_opt reduce_out }
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_reduce")


let cld_reduce_default_to_sexp def =
  match def with
  | None -> []
  | Some n -> (nrc_to_sexp n) :: []

let sexp_to_cld_reduce_default se =
  match se with
  | [] -> None
  | n :: [] -> Some (sexp_to_nrc n)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_reduce_default")


let cld_mr_to_sexp (mr:cld_mr) : sexp =
  STerm ("cld_mr",
	 (STerm ("cld_mr_input", (SString (Util.string_of_char_list mr.cld_mr_input))::[]))
	 :: (STerm ("cld_mr_map", (cld_map_fun_to_sexp mr.cld_mr_map.map_fun0)
		    :: (cld_map_emit_to_sexp mr.cld_mr_map.map_emit) :: []))
	 :: (STerm ("cld_mr_reduce", cld_red_opt_to_sexp mr.cld_mr_reduce))
	 :: (STerm ("cld_mr_reduce_default", cld_reduce_default_to_sexp mr.cld_mr_reduce_default))
	 :: [])

let sexp_to_cld_mr (se:sexp) : cld_mr =
  match se with
  | STerm ("cld_mr",
	   (STerm ("cld_mr_input", (SString input)::[]))
	   :: (STerm ("cld_mr_map", mapf::mape::[]))
	   :: (STerm ("cld_mr_reduce", reduce_opt))
	   :: (STerm ("cld_mr_reduce_default", default))
	   :: [])
    ->
      { cld_mr_input = Util.char_list_of_string input;
	cld_mr_map = { map_fun0 = sexp_to_cld_map_fun mapf;
		       map_emit = sexp_to_cld_map_emit mape };
	cld_mr_reduce = sexp_to_cld_red_opt reduce_opt;
        cld_mr_reduce_default = sexp_to_cld_reduce_default default }
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_mr")


let cld_mr_chain_to_sexp (mrl:cld_mr list) : sexp list =
  List.map cld_mr_to_sexp mrl

let sexp_to_cld_mr_chain (sel:sexp list) : cld_mr list =
  List.map sexp_to_cld_mr sel


let cld_mr_last_to_sexp (last: (var list * nrc) * var list) : sexp list =
  match last with
  | (f, vars)
    ->
      (fun_to_sexp f) :: (var_list_to_sexp vars)

let sexp_to_cld_mr_last (sel:sexp list) : (var list * nrc) * var list =
  match sel with
  | f :: vars ->
      (sexp_to_fun f, sexp_to_var_list vars)
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cld_mr_last")


let cldmr_to_sexp (c:cldmr) : sexp =
  STerm ("cld_mrl",
	  (STerm ("cld_mr_chain", cld_mr_chain_to_sexp c.cld_mr_chain))
	  :: (STerm ("cld_mr_last", cld_mr_last_to_sexp c.cld_mr_last))
	  :: [])

let sexp_to_cldmr (se:sexp) : cldmr =
  match se with
  | STerm ("cld_mrl",
	   (STerm ("cld_mr_chain", chain))
	   :: (STerm ("cld_mr_last", last))
	   :: [])
    ->
      { cld_mr_chain = sexp_to_cld_mr_chain chain;
	cld_mr_last = sexp_to_cld_mr_last last }
  | _ ->
      raise (Util.CACo_Error "Not well-formed S-expr inside cldmr")

