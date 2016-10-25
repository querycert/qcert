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

open Util
open Compiler.EnhancedCompiler
open Compiler

open SExp


(****************
 * AST <-> SExp *
 ****************)

let coq_string_to_sstring (cl:char list) : sexp =
  SString (string_of_char_list cl)
let dbrands_to_sexp (bs:(char list) list) : sexp list =
  List.map coq_string_to_sstring bs
let coq_string_list_to_sstring_list = dbrands_to_sexp

let coq_sort_desc_to_sstring x =
  begin match x with
  | Compiler.Ascending -> SString "asc"
  | Compiler.Descending -> SString "desc"
  end
let coq_string_list_to_sstring_list_with_order l =
  List.concat (List.map (fun x -> [coq_string_to_sstring (fst x);coq_sort_desc_to_sstring (snd x)]) l)

let sstring_to_coq_string (se:sexp) : char list =
  begin match se with
  | SString s -> char_list_of_string s
  | _ -> raise (Qcert_Error "Not well-formed S-expr for Coq string")
  end
let sexp_to_dbrands (bs:sexp list) : (char list) list =
  List.map sstring_to_coq_string bs
let sstring_list_to_coq_string_list = sexp_to_dbrands
let rec sstring_list_with_order_to_coq_string_list sl =
  begin match sl with
  | [] -> []
  | SString att :: SString "asc" :: sl' -> (char_list_of_string att, Ascending) :: (sstring_list_with_order_to_coq_string_list sl')
  | SString att :: SString "desc" :: sl' -> (char_list_of_string att, Descending) :: (sstring_list_with_order_to_coq_string_list sl')
  | _ -> raise (Qcert_Error "Not well-formed S-expr for Coq orderBy")
  end

(* Data Section *)

let rec data_to_sexp (d : QData.data) : sexp =
  match d with
  | Dunit -> STerm ("dunit", [])
  | Dnat n -> SInt n
  | Dbool b -> SBool b
  | Dstring s -> SString (string_of_char_list s)
  | Dcoll dl -> STerm ("dcoll", List.map data_to_sexp dl)
  | Drec adl -> STerm ("drec", List.map drec_to_sexp adl)
  | Dleft d -> STerm ("dleft", data_to_sexp d :: [])
  | Dright d -> STerm ("dright", data_to_sexp d :: [])
  | Dbrand (bs,d) -> STerm ("dbrand", (STerm ("brands", dbrands_to_sexp bs)) :: (STerm ("value", (data_to_sexp d) :: [])) :: [])
  | Dforeign fdt -> STerm ("dtime_scale", (SString (PrettyIL.string_of_foreign_data (Obj.magic fdt))) :: [])
and drec_to_sexp (ad : char list * QData.data) : sexp =
  STerm ("datt", (SString (string_of_char_list (fst ad))) :: (data_to_sexp (snd ad)) :: [])

let rec sexp_to_data (se:sexp) : QData.data =
  match se with
  | STerm ("dunit", []) -> Dunit
  | SBool b -> Dbool b
  | SInt n -> Dnat n
  | SString s -> Dstring (char_list_of_string s)
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
      raise (Qcert_Error ("Not well-formed S-expr with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr")
and sexp_to_drec (sel:sexp) : (char list * QData.data) =
  match sel with
  | STerm ("datt", (SString s) :: se :: []) ->
      (char_list_of_string s, sexp_to_data se)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside drec")

(* Operators Section *)

let arithbop_to_sexp (b:arithBOp) : sexp =
  STerm (PrettyIL.string_of_binarith b,[])
  
let sexp_to_arithbop (se:sexp) : arithBOp =
  match se with
  | STerm (s,[]) -> PrettyIL.binarith_of_string s
  | _ ->
      raise  (Qcert_Error "Not well-formed S-expr inside arith binop")
  
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
  | STerm ("ASqlDatePlus",[]) -> Enhanced.Ops.Binary.coq_ASqlDatePlus
  | STerm ("ASqlDateMinus",[]) -> Enhanced.Ops.Binary.coq_ASqlDateMinus
  | STerm ("ASqlDateNe",[]) -> Enhanced.Ops.Binary.coq_ASqlDateNe
  | STerm ("ASqlDateLt",[]) -> Enhanced.Ops.Binary.coq_ASqlDateLt
  | STerm ("ASqlDateLe",[]) -> Enhanced.Ops.Binary.coq_ASqlDateLe
  | STerm ("ASqlDateGt",[]) -> Enhanced.Ops.Binary.coq_ASqlDateGt
  | STerm ("ASqlDateGe",[]) -> Enhanced.Ops.Binary.coq_ASqlDateGe
  | STerm ("ASqlDateIntervalBetween",[]) -> Enhanced.Ops.Binary.coq_ASqlDateIntervalBetween
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside arith binop with name " ^ t))
  | _ -> raise  (Qcert_Error "Not well-formed S-expr inside arith binop")

let arithuop_to_sexp (b:arithUOp) : sexp =
  STerm (PrettyIL.string_of_unarith b,[])

let sexp_to_arithuop (se:sexp) : arithUOp =
  match se with
  | STerm (s,[]) -> PrettyIL.unarith_of_string s
  | _ ->
      raise  (Qcert_Error "Not well-formed S-expr inside arith unop")

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
  | AOrderBy sl -> STerm ("AOrderBy", coq_string_list_to_sstring_list_with_order sl)
  | ASum -> STerm ("ASum",[])
  | AArithMean -> STerm ("AArithMean",[])
  | AToString -> STerm ("AToString",[])
  | ASubstring (n,None) -> STerm ("ASubstring",[SInt n])
  | ASubstring (n1,(Some n2)) -> STerm ("ASubstring",[SInt n1;SInt n2])
  | ALike (p,None) -> STerm ("ALike",[coq_string_to_sstring p])
  | ALike (p,(Some esc)) -> STerm ("ALike",[coq_string_to_sstring p;coq_string_to_sstring [esc]])
  | ACast bl -> STerm ("ACast", dbrands_to_sexp bl)
  | AUnbrand -> STerm ("AUnbrand",[])
  | ASingleton -> STerm ("ASingleton",[])
  | ANumMin -> STerm ("ANumMin",[])
  | ANumMax -> STerm ("ANumMax",[])
  | AForeignUnaryOp fuop -> SString (PrettyIL.string_of_foreign_unop (Obj.magic fuop))

let sstring_to_sql_date_component (part:sexp) : Enhanced.Data.sql_date_part =
  match part with
  | SString "DAY" ->   Enhanced.Data.sql_date_day
  | SString "MONTH" -> Enhanced.Data.sql_date_month
  | SString "YEAR" ->  Enhanced.Data.sql_date_year
  | _ -> raise (Qcert_Error "Not well-formed S-expr for sql date component")
			  
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
  | STerm ("AOrderBy",sl) -> AOrderBy (sstring_list_with_order_to_coq_string_list sl)
  | STerm ("ASum",[]) -> ASum
  | STerm ("AArithMean",[]) -> AArithMean
  | STerm ("AToString",[]) -> AToString
  | STerm ("ASubstring",[SInt n1]) -> ASubstring (n1,None)
  | STerm ("ASubstring",[SInt n1;SInt n2]) -> ASubstring (n1,Some n2)
  | STerm ("ALike",[p]) -> ALike (sstring_to_coq_string p,None)
  | STerm ("ALike",[p;SString esc]) ->
     ALike (sstring_to_coq_string p,Some (esc.[0]))
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
  | STerm ("ASqlDateFromString",[]) -> Enhanced.Ops.Unary.coq_ASqlDateFromString
  | STerm ("ASqlDateIntervalromString",[]) -> Enhanced.Ops.Unary.coq_ASqlDateIntervalFromString
  | STerm ("ASqlGetDateComponent",[part]) -> Enhanced.Ops.Unary.coq_ASqlGetDateComponent (sstring_to_sql_date_component part)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside unop with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside unop")

(* CAMP Section *)

let rec camp_to_sexp (p : QLang.camp) : sexp =
  match p with
  | Pconst d -> STerm ("Pconst", [data_to_sexp d])
  | Punop (u, p1) -> STerm ("Punop", (unop_to_sexp u) :: [camp_to_sexp p1])
  | Pbinop (b, p1, p2) -> STerm ("Pbinop", (binop_to_sexp b) :: [camp_to_sexp p1; camp_to_sexp p2])
  | Pmap p1 -> STerm ("Pmap", [camp_to_sexp p1])
  | Passert p1 -> STerm ("Passert", [camp_to_sexp p1]) 
  | PorElse (p1,p2) -> STerm ("PorElse", [camp_to_sexp p1; camp_to_sexp p2])
  | Pit -> STerm ("Pit", [])
  | PletIt (p1,p2) -> STerm ("PletIt", [camp_to_sexp p1; camp_to_sexp p2])
  | Pgetconstant sl -> STerm ("Pgetconstant", [coq_string_to_sstring sl])
  | Penv -> STerm ("Penv", [])
  | PletEnv (p1,p2) -> STerm ("PletEnv", [camp_to_sexp p1; camp_to_sexp p2])
  | Pleft -> STerm ("Pleft", [])
  | Pright -> STerm ("Pright", [])

let rec sexp_to_camp (se : sexp) : QLang.camp =
  match se with
  | STerm ("Pconst", [d]) -> Pconst (sexp_to_data d)
  | STerm ("Punop", use :: [se1]) ->
      let u = sexp_to_unop use in
      Punop (u, sexp_to_camp se1)
  | STerm ("Pbinop", bse :: [se1;se2]) ->
      let b = sexp_to_binop bse in
      Pbinop (b, sexp_to_camp se1, sexp_to_camp se2)
  | STerm ("Pmap", [se1]) -> Pmap (sexp_to_camp se1)
  | STerm ("Passert", [se1])  -> Passert (sexp_to_camp se1)
  | STerm ("PorElse", [se1;se2]) -> PorElse (sexp_to_camp se1,sexp_to_camp se2)
  | STerm ("Pit", []) -> Pit
  | STerm ("PletIt", [se1;se2]) -> PletIt (sexp_to_camp se1,sexp_to_camp se2)
  | STerm ("Pgetconstant", [sl]) -> Pgetconstant (sstring_to_coq_string sl)
  | STerm ("Penv", []) -> Penv
  | STerm ("PletEnv", [se1;se2]) -> PletEnv (sexp_to_camp se1,sexp_to_camp se2)
  | STerm ("Pleft", []) -> Pleft
  | STerm ("Pright", []) -> Pright
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside camp with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside camp")

(* NRA Section *)

let rec nraenv_to_sexp (op : QLang.nraenv) : sexp =
  match op with
  | ANID -> STerm ("ANID",[])
  | ANConst d -> STerm ("ANConst", [data_to_sexp d])
  | ANBinop (b, op1, op2) -> STerm ("ANBinop", (binop_to_sexp b) :: [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANUnop (u, op1) -> STerm ("ANUnop", (unop_to_sexp u) :: [nraenv_to_sexp op1])
  | ANMap (op1,op2) -> STerm ("ANMap", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANMapConcat (op1,op2) -> STerm ("ANMapConcat", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANProduct (op1,op2) -> STerm ("ANProduct", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANSelect (op1,op2) -> STerm ("ANSelect", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANDefault (op1,op2) -> STerm ("ANDefault", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANEither (op1,op2) -> STerm ("ANEither", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANEitherConcat (op1,op2) -> STerm ("ANEitherConcat", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANApp (op1,op2) -> STerm ("ANApp", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANGetConstant sl -> STerm ("ANGetConstant", [coq_string_to_sstring sl])
  | ANEnv -> STerm ("ANEnv",[])
  | ANAppEnv (op1,op2) -> STerm ("ANAppEnv", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | ANMapEnv op1 -> STerm ("ANMapEnv", [nraenv_to_sexp op1])

let rec sexp_to_nraenv (se : sexp) : QLang.nraenv =
  match se with
  | STerm ("ANID",[]) -> ANID
  | STerm ("ANConst", [d]) -> ANConst (sexp_to_data d)
  | STerm ("ANBinop", bse :: [se1;se2]) ->
      let b = sexp_to_binop bse in
      ANBinop (b, sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANUnop", use :: [se1]) ->
      let u = sexp_to_unop use in
      ANUnop (u, sexp_to_nraenv se1)
  | STerm ("ANMap", [se1;se2]) -> ANMap (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANMapConcat", [se1;se2]) -> ANMapConcat (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANProduct", [se1;se2]) -> ANProduct (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANSelect", [se1;se2]) -> ANSelect (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANDefault", [se1;se2]) -> ANDefault (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANEither", [se1;se2]) -> ANEither (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANEitherConcat", [se1;se2]) -> ANEitherConcat (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANApp", [se1;se2]) -> ANApp (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANGetConstant", [sl]) -> ANGetConstant (sstring_to_coq_string sl)
  | STerm ("ANEnv",[]) -> ANEnv
  | STerm ("ANAppEnv", [se1;se2]) -> ANAppEnv (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANMapEnv", [se1]) -> ANMapEnv (sexp_to_nraenv se1)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside NRAEnv with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside NRAEnv")

(* NNRC Section *)

let rec nnrc_to_sexp (n : QLang.nnrc) : sexp =
  match n with
  | NRCVar v -> STerm ("NRCVar", [SString (string_of_char_list v)])
  | NRCConst d -> STerm ("NRCConst", [data_to_sexp d])
  | NRCBinop (b, n1, n2) -> STerm ("NRCBinop", (binop_to_sexp b) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NRCUnop (u, n1) -> STerm ("NRCUnop", (unop_to_sexp u) :: [nnrc_to_sexp n1])
  | NRCLet (v, n1, n2) -> STerm ("NRCLet", (SString (string_of_char_list v)) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NRCFor (v, n1, n2) -> STerm ("NRCFor", (SString (string_of_char_list v)) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NRCIf (n1, n2, n3) -> STerm ("NRCIf", [nnrc_to_sexp n1;nnrc_to_sexp n2;nnrc_to_sexp n3])
  | NRCEither (n1,v1,n2,v2,n3) -> STerm ("NRCEither",
					 (SString (string_of_char_list v1))
					 :: (SString (string_of_char_list v2))
					 :: [nnrc_to_sexp n1;nnrc_to_sexp n2;nnrc_to_sexp n3])

let rec sexp_to_nnrc (se:sexp) : QLang.nnrc =
  match se with
  | STerm ("NRCVar", [SString v]) -> NRCVar (char_list_of_string v)
  | STerm ("NRCConst", [d]) -> NRCConst (sexp_to_data d)
  | STerm ("NRCBinop", b :: [n1;n2]) -> NRCBinop (sexp_to_binop b, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("NRCUnop", u :: [n1]) -> NRCUnop (sexp_to_unop u, sexp_to_nnrc n1)
  | STerm ("NRCLet", (SString v) :: [n1;n2]) -> NRCLet (char_list_of_string v, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("NRCFor", (SString v) :: [n1;n2]) -> NRCFor (char_list_of_string v, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("NRCIf", [n1;n2;n3]) -> NRCIf (sexp_to_nnrc n1, sexp_to_nnrc n2, sexp_to_nnrc n3)
  | STerm ("NRCEither", (SString v1) :: (SString v2) :: [n1;n2;n3]) ->
      NRCEither (sexp_to_nnrc n1,char_list_of_string v1,sexp_to_nnrc n2,char_list_of_string v2,sexp_to_nnrc n3)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside nnrc with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nnrc")

(* NNRCMR section *)

let var_to_sexp (v:var) : sexp =
  SString (string_of_char_list v)

let opt_var_to_sexp (vo:var option) : sexp list =
  match vo with
  | None -> []
  | Some v -> [var_to_sexp v]
    
let sexp_to_var (se:sexp) : var =
  match se with
  | SString v -> char_list_of_string v
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside var")

let sexp_to_var_opt (sel:sexp list) : var option =
  match sel with
  | [] -> None
  | [se] -> Some (sexp_to_var se)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside optional var")

let var_list_to_sexp (vl:var list) : sexp list =
  map (fun v -> (SString (string_of_char_list v))) vl

let sexp_to_var_list (sel:sexp list) =
  List.map sexp_to_var sel

let params_to_sexp (vl:var list) : sexp =
  STerm ("params", var_list_to_sexp vl)

let sexp_to_params (se:sexp) =
  match se with
  | STerm ("params", vars) -> sexp_to_var_list vars
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside var list")

let fun_to_sexp (f:(var list * nrc)) : sexp =
  STerm ("lambda", (params_to_sexp (fst f)) :: (nnrc_to_sexp (snd f)) :: [])

let sexp_to_fun (se:sexp) : (var list * nrc) =
  match se with
  | STerm ("lambda", params :: sen :: []) ->
      (sexp_to_params params, sexp_to_nnrc sen)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside lambda")

let unary_fun_to_sexp (f:var * nrc) : sexp =
  fun_to_sexp ([fst f], snd f)

let sexp_to_unary_fun (se:sexp) : var * nrc =
  match sexp_to_fun se with
  | ([var], n) -> (var, n)
  | _ ->
      raise (Qcert_Error "Map or Reduce lambda isn't unary")
  
let binary_fun_to_sexp (f:(var * var) * nrc) : sexp =
  fun_to_sexp ([fst (fst f); (snd (fst f))], snd f)

let sexp_to_binary_fun (se:sexp) : (var * var) * nrc =
  match sexp_to_fun se with
  | ([var1; var2], n) -> ((var1, var2), n)
  | _ ->
      raise (Qcert_Error "Map or Reduce lambda isn't binary")
  
    
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
      raise (Qcert_Error "Not well-formed S-expr inside map_fun")


let numeric_type_to_sexp nt =
  match nt with
  | Enhanced_numeric_int -> SString "Enhanced_numeric_int"
  | Enhanced_numeric_float -> SString "Enhanced_numeric_float"

let sexp_to_numeric_type se =
  match se with
  | SString "Enhanced_numeric_int" -> Enhanced_numeric_int
  | SString "Enhanced_numeric_float" -> Enhanced_numeric_float
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside numeric_type")


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
      raise (Qcert_Error "Not well-formed S-expr inside reduce_op")


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
      raise (Qcert_Error "Not well-formed S-expr inside reduce_fun")


let mr_to_sexp (mr:mr) : sexp =
  STerm ("mr",
	 (STerm ("mr_input", (SString (string_of_char_list mr.mr_input))::[]))
	 :: (STerm ("mr_output", (SString (string_of_char_list mr.mr_output))::[]))
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
      { mr_input = char_list_of_string input;
	mr_output = char_list_of_string output;
	mr_map = sexp_to_map_fun map;
	mr_reduce = sexp_to_reduce_fun reduce }
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside mr")


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
      raise (Qcert_Error "Not well-formed S-expr inside dlocalization")


let var_loc_to_sexp (v,l) =
  STerm ("var_loc", (SString (string_of_char_list v))::(loc_to_sexp l)::[])
    
let sexp_to_var_loc (se:sexp) =
  match se with
  | STerm ("var_loc", (SString v)::l::[]) ->
      (char_list_of_string v, sexp_to_loc l)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside var-dlocalization pair")
    
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
      raise (Qcert_Error "Not well-formed S-expr inside mr_last")

let nnrcmr_to_sexp (n:QLang.nnrcmr) : sexp =
  STerm ("nrcmr",
	 (STerm ("mr_env", var_locs_to_sexp n.mr_inputs_loc))
	 :: (STerm ("mr_chain", mr_chain_to_sexp (n.mr_chain)))
	 :: (mr_last_to_sexp n.mr_last)
	 :: [])

let sexp_to_nnrcmr (se:sexp) : QLang.nnrcmr =
  match se with
  | STerm ("nrcmr",
	   (STerm ("mr_env", env))
	   :: (STerm ("mr_chain", chain))
	   :: last
	   :: [])
    ->
      { mr_inputs_loc = sexp_to_var_locs env;
        mr_chain = sexp_to_mr_chain chain;
	mr_last = sexp_to_mr_last last }
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nrcmr")

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
      raise (Qcert_Error "Not well-formed S-expr inside cld_map_fun")


let cld_map_emit_to_sexp (me:cld_map_emit) =
  match me with
  | CldEmitDist -> STerm ("CldEmitDist", [])
  | CldEmitCollect i -> STerm ("CldEmitCollect", (SInt i)::[])

let sexp_to_cld_map_emit (se:sexp) : cld_map_emit =
  match se with
  | STerm ("CldEmitDist", []) -> CldEmitDist
  | STerm ("CldEmitCollect", (SInt i)::[]) -> CldEmitCollect i
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cld_map_emit")


let cld_numeric_type_to_sexp nt =
  match nt with
  | Cld_int -> SString "Cld_int"
  | Cld_float -> SString "Cld_float"

let sexp_to_cld_numeric_type se =
  match se with
  | SString "Cld_int" -> Cld_int
  | SString "Cld_float" -> Cld_float
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cld_numeric_type")


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
      raise (Qcert_Error "Not well-formed S-expr inside cld_reduce_op")


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
      raise (Qcert_Error "Not well-formed S-expr inside cld_reduce_fun")


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
      raise (Qcert_Error "Not well-formed S-expr inside cld_reduce")


let cld_reduce_default_to_sexp def =
  match def with
  | None -> []
  | Some n -> (nnrc_to_sexp n) :: []

let sexp_to_cld_reduce_default se =
  match se with
  | [] -> None
  | n :: [] -> Some (sexp_to_nnrc n)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cld_reduce_default")


let cld_mr_to_sexp (mr:cld_mr) : sexp =
  STerm ("cld_mr",
	 (STerm ("cld_mr_input", (SString (string_of_char_list mr.cld_mr_input))::[]))
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
      { cld_mr_input = char_list_of_string input;
	cld_mr_map = { map_fun0 = sexp_to_cld_map_fun mapf;
		       map_emit = sexp_to_cld_map_emit mape };
	cld_mr_reduce = sexp_to_cld_red_opt reduce_opt;
        cld_mr_reduce_default = sexp_to_cld_reduce_default default }
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cld_mr")


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
      raise (Qcert_Error "Not well-formed S-expr inside cld_mr_last")


let cldmr_to_sexp (c:QLang.cldmr) : sexp =
  STerm ("cld_mrl",
	  (STerm ("cld_mr_chain", cld_mr_chain_to_sexp c.cld_mr_chain))
	  :: (STerm ("cld_mr_last", cld_mr_last_to_sexp c.cld_mr_last))
	  :: [])

let sexp_to_cldmr (se:sexp) : QLang.cldmr =
  match se with
  | STerm ("cld_mrl",
	   (STerm ("cld_mr_chain", chain))
	   :: (STerm ("cld_mr_last", last))
	   :: [])
    ->
      { cld_mr_chain = 
sexp_to_cld_mr_chain chain;
	cld_mr_last = sexp_to_cld_mr_last last }
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cldmr")

(* NRA Section *)

let rec sexp_to_sql_query (se : sexp) =
  begin match se with
  | STerm ("query", sfw) ->
      sexp_to_sfw sfw
  | STerm (sterm, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL query: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL query")
  end
and sexp_to_sfw sfw =
  begin match sfw with
  | (STerm ("select", selects)) :: (STerm ("from", [froms])) :: other_clauses ->
      let (where,group_by,order_by) = sexp_to_other_clauses other_clauses in
      QSQL.sql_sql_query
	(sexp_to_sql_selects selects)
	(sexp_to_sql_froms froms)
	where group_by order_by
  | (STerm ("union", [q1;q2])) :: [] ->
      QSQL.sql_sql_union (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | (STerm ("intersect", [q1;q2])) :: [] ->
      QSQL.sql_sql_intersect (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | STerm (sterm, _) :: _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL sfw block: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL query")
  end
and sexp_to_sql_selects selects =
  begin match selects with
  | [] -> []
  | (STerm ("all",[])) :: selects' ->
      (QSQL.sql_select_star
       :: (sexp_to_sql_selects selects'))
  | (STerm ("as",[cname])) :: expr :: selects' ->
      (QSQL.sql_select_expr (sstring_to_coq_string cname) (sexp_to_sql_expr expr))
      :: (sexp_to_sql_selects selects')
  | STerm ("deref",[cname;STerm ("ref",[tname])]) :: selects' ->
      (QSQL.sql_select_column_deref (sstring_to_coq_string tname) (sstring_to_coq_string cname))
      :: (sexp_to_sql_selects selects')
  | STerm ("ref",[cname]) :: selects' ->
      (QSQL.sql_select_column (sstring_to_coq_string cname))
      :: (sexp_to_sql_selects selects')
  | (STerm ("function", _) as expr) :: selects'
  | (STerm ("multiply", _) as expr) :: selects'
  | (STerm ("divide", _) as expr) :: selects' ->
      (QSQL.sql_select_expr (Util.char_list_of_string "") (sexp_to_sql_expr expr))
      :: (sexp_to_sql_selects selects')
  | STerm (sterm, _) :: _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL select: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL select")
  end
and sexp_to_sql_froms froms =
  begin match froms with
  | STerm ("table",[tname]) -> [QSQL.sql_from_table (sstring_to_coq_string tname)]
  | STerm ("aliasAs", [new_tname;STerm ("table",[tname])]) ->
      [QSQL.sql_from_table_alias (sstring_to_coq_string new_tname)
	 (sstring_to_coq_string tname)]
  | STerm ("aliasAs", [tname;query]) ->
      [QSQL.sql_from_query (sstring_to_coq_string tname, None) (sexp_to_sql_query query)]
  | STerm ("join", [from1;from2]) ->
      (sexp_to_sql_froms from1) @ (sexp_to_sql_froms from2)
  | STerm (sterm, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL froms: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL froms")
  end
and sexp_to_other_clauses other_clauses =
  begin match other_clauses with
  | [] -> (None, None, None)
  | STerm ("where",[cond]) :: rest ->
      let (group_by,order_by) = sexp_to_sql_group_by_order_by rest in
      (Some (sexp_to_sql_cond cond), group_by, order_by)
  | rest ->
      let (group_by,order_by) = sexp_to_sql_group_by_order_by rest in
      (None, group_by, order_by)
  end
and sexp_to_sql_group_by_order_by rest =
  begin match rest with
  | [] -> (None,None)
  | (STerm ("groupBy",groups)) :: (STerm ("having",[cond])) :: rest ->
      let order_by = sexp_to_sql_order_by rest in
      let group_by = Some (sexp_to_sql_groups groups, Some (sexp_to_sql_cond cond)) in
      (group_by, order_by)
  | STerm ("groupBy",groups) :: rest ->
      let order_by = sexp_to_sql_order_by rest in
      let group_by = Some (sexp_to_sql_groups groups, None) in
      (group_by, order_by)
  | rest ->
      let order_by = sexp_to_sql_order_by rest in
      (None, order_by)
  end
and sexp_to_sql_order_by rest =
  begin match rest with
  | [] -> None
  | STerm ("orderBy",orders) :: [] ->
      Some (sexp_to_sql_orders orders)
  | STerm ("orderBy",orders) :: STerm (sterm, _) :: _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL other clauses (after orderBy): " ^ sterm))
  | STerm (sterm, _) :: _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL other clauses: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL other clauses")
  end
and sexp_to_sql_groups groups =
  begin match groups with
  | [] -> []
  | (STerm ("ref",[cname])) :: groups' -> (sstring_to_coq_string cname) :: sexp_to_sql_groups groups'
  | STerm (sterm, _) :: _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL groups: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL groups")
  end
and sexp_to_sql_orders orders =
  begin match orders with
  | [] -> []
  | (STerm ("ascending",[(STerm ("ref",[cname]))])) :: orders' ->
      (sstring_to_coq_string cname, Compiler.Ascending) :: sexp_to_sql_orders orders'
  | (STerm ("descending",[(STerm ("ref",[cname]))])) :: orders' ->
      (sstring_to_coq_string cname, Compiler.Descending) :: sexp_to_sql_orders orders'
  | (STerm ("ascending",STerm (sterm,_)::_)) :: orders' ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL ascending order: " ^ sterm))
  | (STerm ("descending",STerm (sterm,_)::_)) :: orders' ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL descending order: " ^ sterm))
  | STerm (sterm, _) :: _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL orders: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL orders")
  end
    
and sexp_to_sql_expr expr =
  begin match expr with
  | SString s ->
      QSQL.sql_expr_const (Dstring (char_list_of_string s))
  | SFloat f ->
      QSQL.sql_expr_const (Dforeign (Obj.magic (Enhancedfloat f)))
  | SInt i ->
      QSQL.sql_expr_const (Dnat i)
  | STerm ("dunit",[]) ->
      QSQL.sql_expr_const (Dunit)
  | STerm ("list",const_list) ->
      QSQL.sql_expr_const (Dcoll (sexp_to_sql_const_list const_list))
  | STerm ("cast",[STerm ("as",[SString "DATE"]); expr1]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_from_string)))
	(sexp_to_sql_expr expr1)
  | STerm ("literal",[SString "date"; SString sdate]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string sdate)))
  | STerm ("interval",[SString sinterval; STerm ("year",[])]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_interval_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string (sinterval ^ "-YEAR"))))
  | STerm ("interval",[SString sinterval; STerm ("month",[])]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_interval_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string (sinterval ^ "-MONTH"))))
  | STerm ("interval",[SString sinterval; STerm ("day",[])]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op Compiler.Uop_sql_date_interval_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string (sinterval ^ "-DAY"))))
  | STerm ("deref",[cname;STerm ("ref",[tname])]) ->
      QSQL.sql_expr_column_deref (sstring_to_coq_string tname) (sstring_to_coq_string cname)
  | STerm ("ref",[cname]) -> (QSQL.sql_expr_column (sstring_to_coq_string cname))
  | STerm ("minus",[expr1]) ->
      QSQL.sql_expr_unary Compiler.SMinus (sexp_to_sql_expr expr1)
  | STerm ("add",[expr1;expr2]) ->
      QSQL.sql_expr_binary Compiler.SPlus (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("subtract",[expr1;expr2]) ->
      QSQL.sql_expr_binary Compiler.SSubtract (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("multiply",[expr1;expr2]) ->
      QSQL.sql_expr_binary Compiler.SMult (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("divide",[expr1;expr2]) ->
      QSQL.sql_expr_binary Compiler.SDivide (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "substr";expr1;SInt n1;SInt n2]) ->
     QSQL.sql_expr_unary (Compiler.SSubstring (n1-1,Some (n1-1+n2))) (sexp_to_sql_expr expr1) (* It's 'substring (expr from n1 for n2)' i.e., from n1 for n2 characters, with initial index 1 *)
  | STerm ("cases",
	   [STerm ("case", [STerm ("when", [condexpr])
			  ; STerm ("then", [expr1])])
	   ; STerm ("default", [expr2])]) ->
     QSQL.sql_expr_case
       (sexp_to_sql_cond condexpr)
       (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "count"]) ->
      QSQL.sql_expr_agg_expr Compiler.SCount QSQL.sql_expr_star
  | STerm ("function",[SString "count";expr1]) ->
      QSQL.sql_expr_agg_expr Compiler.SCount (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "sum";expr1]) ->
      QSQL.sql_expr_agg_expr Compiler.SSum (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "avg";expr1]) ->
      QSQL.sql_expr_agg_expr Compiler.SAvg (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "min";expr1]) ->
      QSQL.sql_expr_agg_expr Compiler.SMin (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "max";expr1]) ->
      QSQL.sql_expr_agg_expr Compiler.SMax (sexp_to_sql_expr expr1)
  | STerm ("query", _) -> QSQL.sql_expr_query (sexp_to_sql_query expr) (* XXX Nested query XXX *)
  | STerm ("extract",[STerm ("year",[]);expr1]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_YEAR))))
	(sexp_to_sql_expr expr1)
  | STerm ("extract",[STerm ("month",[]);expr1]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_MONTH))))
	(sexp_to_sql_expr expr1)
  | STerm ("extract",[STerm ("day",[]);expr1]) ->
      QSQL.sql_expr_unary (Compiler.SUnaryForeignExpr (Obj.magic (Compiler.Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_DAY))))
	(sexp_to_sql_expr expr1)
  | STerm ("function",[SString "date_minus";expr1;expr2]) ->
      QSQL.sql_expr_binary (Compiler.SBinaryForeignExpr (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_minus)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_plus";expr1;expr2]) ->
      QSQL.sql_expr_binary (Compiler.SBinaryForeignExpr (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_plus)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "concat";expr1;expr2]) ->
      QSQL.sql_expr_binary Compiler.SConcat
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function", (SString fun_name)::_) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL expr: function " ^ fun_name))
  | STerm (sterm, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL expr: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL expr")
  end
and sexp_to_sql_const_list const_list =
  begin match const_list with
  | [] -> []
  | (SString s) :: const_list' ->
      (Dstring (char_list_of_string s)) :: (sexp_to_sql_const_list const_list')
  | (SFloat f) :: const_list' ->
      (Dforeign (Obj.magic (Enhancedfloat f))) :: (sexp_to_sql_const_list const_list')
  | (SInt i) :: const_list' ->
      (Dnat i) :: (sexp_to_sql_const_list const_list')
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL const_list")
  end
and sexp_to_sql_cond cond =
  begin match cond with
  | STerm ("and",[cond1;cond2]) ->
      QSQL.sql_cond_and (sexp_to_sql_cond cond1) (sexp_to_sql_cond cond2)
  | STerm ("or",[cond1;cond2]) ->
      QSQL.sql_cond_or (sexp_to_sql_cond cond1) (sexp_to_sql_cond cond2)
  | STerm ("not",[cond1]) ->
      QSQL.sql_cond_not (sexp_to_sql_cond cond1)
  | STerm ("equal",[expr1;expr2]) ->
      QSQL.sql_cond_binary SEq (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("not_equal",[expr1;expr2]) ->
      QSQL.sql_cond_binary SDiff (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("greater_than",[expr1;expr2]) ->
      QSQL.sql_cond_binary SGt (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("greater_than_or_equal",[expr1;expr2]) ->
      QSQL.sql_cond_binary SGe (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("less_than",[expr1;expr2]) ->
      QSQL.sql_cond_binary SLt (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("less_than_or_equal",[expr1;expr2]) ->
      QSQL.sql_cond_binary SLe (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("like",[expr1;slike]) ->
      QSQL.sql_cond_like (sexp_to_sql_expr expr1) (sstring_to_coq_string slike)
  | STerm ("exists",[query]) ->
      QSQL.sql_cond_exists (sexp_to_sql_query query)
  | STerm ("isBetween",[expr1;expr2;expr3]) ->
      QSQL.sql_cond_between (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2) (sexp_to_sql_expr expr3)
  | STerm ("isIn",[expr1;expr2]) ->
      QSQL.sql_cond_in (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_le";expr1;expr2]) ->
      QSQL.sql_cond_binary (Compiler.SBinaryForeignCond (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_le)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_lt";expr1;expr2]) ->
      QSQL.sql_cond_binary (Compiler.SBinaryForeignCond (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_lt)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_gt";expr1;expr2]) ->
      QSQL.sql_cond_binary (Compiler.SBinaryForeignCond (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_gt)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_ge";expr1;expr2]) ->
      QSQL.sql_cond_binary (Compiler.SBinaryForeignCond (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_ge)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_between";expr1;expr2;expr3]) ->
      let sql_expr1 = (sexp_to_sql_expr expr1) in
      let sql_expr2 = (sexp_to_sql_expr expr2) in
      let sql_expr3 = (sexp_to_sql_expr expr3) in
      QSQL.sql_cond_and
	(QSQL.sql_cond_binary (Compiler.SBinaryForeignCond (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_le))) sql_expr2 sql_expr1)
	(QSQL.sql_cond_binary (Compiler.SBinaryForeignCond (Obj.magic (Compiler.Enhanced_binary_sql_date_op Bop_sql_date_le))) sql_expr1 sql_expr3)
  | STerm (sterm, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL condition: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL condition")
  end

let rec sexp_to_sql_statement (stmt : sexp)  =
  begin match stmt with
  (* Bypass for 'with' at the beginning of the query -- treated as a view *)
  | STerm ("query",((STerm ("with",[STerm ("as",[SString tname]);view_query]))::rest)) ->
      let rest_stmt = sexp_to_sql_statement (STerm ("query",rest)) in
      (QSQL.sql_create_view (Util.char_list_of_string tname) (sexp_to_sql_query view_query))::rest_stmt
  | STerm ("query",_) -> [QSQL.sql_run_query (sexp_to_sql_query stmt)]
  | STerm ("createView", [SString name; query]) ->
     [QSQL.sql_create_view (Util.char_list_of_string name) (sexp_to_sql_query query)]
  | STerm ("dropView",[SString name]) -> [QSQL.sql_drop_view (Util.char_list_of_string name)]
  | STerm (sterm, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL statement: " ^ sterm))
  | _ ->
     raise (Qcert_Error "Not well-formed S-expr inside SQL statement")
  end

let sexp_to_sql (se : sexp) : QLang.sql =
  begin match se with
  | STerm ("statements",stmts) ->
     List.concat (map sexp_to_sql_statement stmts)
  | _ ->
     raise (Qcert_Error "Not well-formed S-expr in top SQL statements")
  end
    
(* Query translations *)
let sexp_to_query (lang: QLang.language) (se: sexp) : QLang.query =
  begin match lang with
  | Compiler.L_rule ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_camp -> Compiler.Q_camp (sexp_to_camp se)
  | Compiler.L_oql ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_sql ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_lambda_nra ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_nra ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_nraenv -> Compiler.Q_nraenv (sexp_to_nraenv se)
  | Compiler.L_nnrc -> Compiler.Q_nnrc (sexp_to_nnrc se)
  | Compiler.L_nnrcmr -> Compiler.Q_nnrcmr (sexp_to_nnrcmr se)
  | Compiler.L_cldmr -> Compiler.Q_cldmr (sexp_to_cldmr se)
  | Compiler.L_dnnrc_dataset ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_dnnrc_typed_dataset ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_javascript
  | Compiler.L_java
  | Compiler.L_spark
  | Compiler.L_spark2
  | Compiler.L_cloudant ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | Compiler.L_error err ->
      raise (Qcert_Error ("sexp_to_query: "^(Util.string_of_char_list err)))
  end

let query_to_sexp (q: QLang.query) : sexp =
  begin match q with
  | Compiler.Q_rule _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_camp q -> camp_to_sexp q
  | Compiler.Q_oql _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_sql _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_lambda_nra _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_nra _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_nraenv q -> nraenv_to_sexp q
  | Compiler.Q_nnrc q -> nnrc_to_sexp q
  | Compiler.Q_nnrcmr q -> nnrcmr_to_sexp q
  | Compiler.Q_cldmr q -> cldmr_to_sexp q
  | Compiler.Q_dnnrc_dataset _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_dnnrc_typed_dataset _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_javascript _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_java _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_spark _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_spark2 _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_cloudant _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Compiler.Q_error err ->
      SString ("query_to_sexp: "^(Util.string_of_char_list err))
  end
