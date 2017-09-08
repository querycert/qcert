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

(* This module contains parsing utilities *)

open Util
open SExp

open QcertCompiler
open QcertCompiler.EnhancedCompiler

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
  | Ascending -> SString "asc"
  | Descending -> SString "desc"
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

let foreign_data_to_sexp (fd:enhanced_data) : sexp =
  match fd with
  | Enhancedfloat f -> SFloat f
  | Enhancedstring s -> STerm ("enhanced_string", (SString s)::[])
  | Enhancedtimescale ts -> STerm ("dtime_scale", (SString (PrettyCommon.timescale_as_string ts))::[])
  | Enhancedtimeduration td -> raise Not_found
  | Enhancedtimepoint tp -> raise Not_found
  | Enhancedsqldate td -> raise Not_found
  | Enhancedsqldateinterval tp -> raise Not_found

let rec data_to_sexp (d : QData.qdata) : sexp =
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
  | Dforeign fdt -> foreign_data_to_sexp (Obj.magic fdt)
and drec_to_sexp (ad : char list * QData.qdata) : sexp =
  STerm ("datt", (SString (string_of_char_list (fst ad))) :: (data_to_sexp (snd ad)) :: [])

let rec sexp_to_data (se:sexp) : QData.qdata =
  match se with
  | STerm ("dunit", []) -> Dunit
  | SBool b -> Dbool b
  | SInt n -> Dnat n
  | SFloat f -> (Dforeign (Obj.magic (Enhancedfloat f)))
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
      Dforeign (Obj.magic (PrettyCommon.foreign_data_of_string s))
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr with name " ^ t))
and sexp_to_drec (sel:sexp) : (char list * QData.qdata) =
  match sel with
  | STerm ("datt", (SString s) :: se :: []) ->
      (char_list_of_string s, sexp_to_data se)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside drec")

(* Operators Section *)

let arithbop_to_sexp (b:arithBOp) : sexp =
  STerm (PrettyCommon.string_of_binarith b,[])
  
let sexp_to_arithbop (se:sexp) : arithBOp =
  match se with
  | STerm (s,[]) -> PrettyCommon.binarith_of_string s
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
  | AForeignBinaryOp fbop -> SString (PrettyCommon.string_of_foreign_binop (Obj.magic fbop))

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
  | SString fbop -> AForeignBinaryOp (Obj.magic (PrettyCommon.foreign_binop_of_string fbop))
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
  STerm (PrettyCommon.string_of_unarith b,[])

let sexp_to_arithuop (se:sexp) : arithUOp =
  match se with
  | STerm (s,[]) -> PrettyCommon.unarith_of_string s
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
  | AForeignUnaryOp fuop -> SString (PrettyCommon.string_of_foreign_unop (Obj.magic fuop))

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
  | SString s -> AForeignUnaryOp (Obj.magic (PrettyCommon.foreign_unop_of_string s))
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
  | PgetConstant sl -> STerm ("Pgetconstant", [coq_string_to_sstring sl])
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
  | STerm ("Pgetconstant", [sl]) -> PgetConstant (sstring_to_coq_string sl)
  | STerm ("Penv", []) -> Penv
  | STerm ("PletEnv", [se1;se2]) -> PletEnv (sexp_to_camp se1,sexp_to_camp se2)
  | STerm ("Pleft", []) -> Pleft
  | STerm ("Pright", []) -> Pright
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside camp with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside camp")

(* CAMP Rule Section *)

let rec camp_rule_to_sexp (p : QLang.camp_rule) : sexp =
  match p with
  | Rule_when (p1, p2) ->
      STerm ("Rule_when", [camp_to_sexp p1; camp_rule_to_sexp p2])
  | Rule_global (p1, p2) ->
      STerm ("Rule_global", [camp_to_sexp p1; camp_rule_to_sexp p2])
  | Rule_not (p1, p2) ->
      STerm ("Rule_not", [camp_to_sexp p1; camp_rule_to_sexp p2])
  | Rule_return p ->
      STerm ("Rule_not", [camp_to_sexp p])
  | Rule_match p ->
      STerm ("Rule_match", [camp_to_sexp p])

let rec sexp_to_camp_rule (se : sexp) : QLang.camp_rule =
  match se with
  | STerm ("Rule_when", [se1; se2]) ->
      Rule_when (sexp_to_camp se1, sexp_to_camp_rule se2)
  | STerm ("Rule_global", [se1; se2]) ->
      Rule_global (sexp_to_camp se1, sexp_to_camp_rule se2)
  | STerm ("Rule_not", [se1; se2]) ->
      Rule_not (sexp_to_camp se1, sexp_to_camp_rule se2)
  | STerm ("Rule_return", [se]) ->
      Rule_return (sexp_to_camp se)
  | STerm ("Rule_match", [se]) ->
      Rule_match (sexp_to_camp se)
  (* Falls back to CAMP *)
  | STerm (_, _) ->
      Rule_match (sexp_to_camp se)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside camp_rule")


(* NRA Section *)

let rec nraenv_to_sexp (op : QLang.nraenv_core) : sexp =
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

let rec sexp_to_nraenv (se : sexp) : QLang.nraenv_core =
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
  | NNRCGetConstant v -> STerm ("NNRCGetConstant", [SString (string_of_char_list v)])
  | NNRCVar v -> STerm ("NNRCVar", [SString (string_of_char_list v)])
  | NNRCConst d -> STerm ("NNRCConst", [data_to_sexp d])
  | NNRCBinop (b, n1, n2) -> STerm ("NNRCBinop", (binop_to_sexp b) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NNRCUnop (u, n1) -> STerm ("NNRCUnop", (unop_to_sexp u) :: [nnrc_to_sexp n1])
  | NNRCLet (v, n1, n2) -> STerm ("NNRCLet", (SString (string_of_char_list v)) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NNRCFor (v, n1, n2) -> STerm ("NNRCFor", (SString (string_of_char_list v)) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NNRCIf (n1, n2, n3) -> STerm ("NNRCIf", [nnrc_to_sexp n1;nnrc_to_sexp n2;nnrc_to_sexp n3])
  | NNRCEither (n1,v1,n2,v2,n3) -> STerm ("NNRCEither",
					 (SString (string_of_char_list v1))
					 :: (SString (string_of_char_list v2))
					 :: [nnrc_to_sexp n1;nnrc_to_sexp n2;nnrc_to_sexp n3])
  | NNRCGroupBy (g,sl,n1) -> STerm ("NNRCGroupBy",
				    (SString (string_of_char_list g))
				    :: (STerm ("keys",coq_string_list_to_sstring_list sl))
				    :: [nnrc_to_sexp n1])

let rec sexp_to_nnrc (se:sexp) : QLang.nnrc =
  match se with
  | STerm ("NNRCGetConstant", [SString v]) -> NNRCGetConstant (char_list_of_string v)
  | STerm ("NNRCVar", [SString v]) -> NNRCVar (char_list_of_string v)
  | STerm ("NNRCConst", [d]) -> NNRCConst (sexp_to_data d)
  | STerm ("NNRCBinop", b :: [n1;n2]) -> NNRCBinop (sexp_to_binop b, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("NNRCUnop", u :: [n1]) -> NNRCUnop (sexp_to_unop u, sexp_to_nnrc n1)
  | STerm ("NNRCLet", (SString v) :: [n1;n2]) -> NNRCLet (char_list_of_string v, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("NNRCFor", (SString v) :: [n1;n2]) -> NNRCFor (char_list_of_string v, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("NNRCIf", [n1;n2;n3]) -> NNRCIf (sexp_to_nnrc n1, sexp_to_nnrc n2, sexp_to_nnrc n3)
  | STerm ("NNRCEither", (SString v1) :: (SString v2) :: [n1;n2;n3]) ->
      NNRCEither (sexp_to_nnrc n1,char_list_of_string v1,sexp_to_nnrc n2,char_list_of_string v2,sexp_to_nnrc n3)
  | STerm ("NNRCGroupBy", (SString v1) :: (STerm ("keys", v2)) :: [n1]) ->
      NNRCGroupBy (char_list_of_string v1,sstring_list_to_coq_string_list v2,sexp_to_nnrc n1)
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

let fun_to_sexp (f:(var list * QLang.nnrc)) : sexp =
  STerm ("lambda", (params_to_sexp (fst f)) :: (nnrc_to_sexp (snd f)) :: [])

let sexp_to_fun (se:sexp) : (var list * QLang.nnrc) =
  match se with
  | STerm ("lambda", params :: sen :: []) ->
      (sexp_to_params params, sexp_to_nnrc sen)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside lambda")

let unary_fun_to_sexp (f:var * QLang.nnrc) : sexp =
  fun_to_sexp ([fst f], snd f)

let sexp_to_unary_fun (se:sexp) : var * QLang.nnrc =
  match sexp_to_fun se with
  | ([var], n) -> (var, n)
  | _ ->
      raise (Qcert_Error "Map or Reduce lambda isn't unary")
  
let binary_fun_to_sexp (f:(var * var) * QLang.nnrc) : sexp =
  fun_to_sexp ([fst (fst f); (snd (fst f))], snd f)

let sexp_to_binary_fun (se:sexp) : (var * var) * QLang.nnrc =
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


let mr_last_to_sexp (last: (var list * QLang.nnrc) * (var * dlocalization) list) =
  match last with
  | (f, var_locs)
    ->
      (STerm ("mr_last",
	      (fun_to_sexp f) :: (var_locs_to_sexp var_locs)))

let sexp_to_mr_last (se:sexp) : (var list * QLang.nnrc) * (var * dlocalization) list =
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


let cldmr_step_to_sexp (mr:cldmr_step) : sexp =
  STerm ("cld_mr",
	 (STerm ("cld_mr_input", (SString (string_of_char_list mr.cldmr_step_input))::[]))
	 :: (STerm ("cld_mr_map", (cld_map_fun_to_sexp mr.cldmr_step_map.map_fun0)
		    :: (cld_map_emit_to_sexp mr.cldmr_step_map.map_emit) :: []))
	 :: (STerm ("cld_mr_reduce", cld_red_opt_to_sexp mr.cldmr_step_reduce))
	 :: (STerm ("cld_mr_reduce_default", cld_reduce_default_to_sexp mr.cldmr_step_reduce_default))
	 :: [])

let sexp_to_cldmr_step (se:sexp) : cldmr_step =
  match se with
  | STerm ("cld_mr",
	   (STerm ("cld_mr_input", (SString input)::[]))
	   :: (STerm ("cld_mr_map", mapf::mape::[]))
	   :: (STerm ("cld_mr_reduce", reduce_opt))
	   :: (STerm ("cld_mr_reduce_default", default))
	   :: [])
    ->
      { cldmr_step_input = char_list_of_string input;
	cldmr_step_map = { map_fun0 = sexp_to_cld_map_fun mapf;
		       map_emit = sexp_to_cld_map_emit mape };
	cldmr_step_reduce = sexp_to_cld_red_opt reduce_opt;
        cldmr_step_reduce_default = sexp_to_cld_reduce_default default }
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cld_mr")


let cldmr_chain_to_sexp (mrl:cldmr_step list) : sexp list =
  List.map cldmr_step_to_sexp mrl

let sexp_to_cldmr_chain (sel:sexp list) : cldmr_step list =
  List.map sexp_to_cldmr_step sel


let cldmr_last_to_sexp (last: (var list * QLang.nnrc) * var list) : sexp list =
  match last with
  | (f, vars)
    ->
      (fun_to_sexp f) :: (var_list_to_sexp vars)

let sexp_to_cldmr_last (sel:sexp list) : (var list * QLang.nnrc) * var list =
  match sel with
  | f :: vars ->
      (sexp_to_fun f, sexp_to_var_list vars)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cldmr_last")


let cldmr_to_sexp (c:QLang.cldmr) : sexp =
  STerm ("cldmr",
	  (STerm ("cld_mr_chain", cldmr_chain_to_sexp c.cldmr_chain))
	  :: (STerm ("cld_mr_last", cldmr_last_to_sexp c.cldmr_last))
	  :: [])

let sexp_to_cldmr (se:sexp) : QLang.cldmr =
  match se with
  | STerm ("cld_mrl",
	   (STerm ("cld_mr_chain", chain))
	   :: (STerm ("cld_mr_last", last))
	   :: [])
    ->
      { cldmr_chain = sexp_to_cldmr_chain chain;
	cldmr_last = sexp_to_cldmr_last last }
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside cldmr")

(* SQL Section *)

let rec sexp_to_sql_query (se : sexp) =
  begin match se with
  | STerm ("query", sfw) ->
      sexp_to_sfw sfw
  | STerm ("union", [STerm ("distinct",[]);q1;q2]) ->
      QSQL.sql_sql_union SDistinct (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | STerm ("intersect", [STerm ("distinct",[]);q1;q2]) ->
      QSQL.sql_sql_intersect SDistinct (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | STerm ("except", [STerm ("distinct",[]);q1;q2]) ->
      QSQL.sql_sql_except SDistinct (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | STerm ("union", [q1;q2]) ->
      QSQL.sql_sql_union SAll (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | STerm ("intersect", [q1;q2]) ->
      QSQL.sql_sql_intersect SAll (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | STerm ("except", [q1;q2]) ->
      QSQL.sql_sql_except SAll (sexp_to_sql_query q1) (sexp_to_sql_query q2)
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
  | (STerm ("union", [STerm ("distinct",[]);q1;q2])) :: [] ->
      QSQL.sql_sql_union SDistinct (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | (STerm ("intersect", [STerm ("distinct",[]);q1;q2])) :: [] ->
      QSQL.sql_sql_intersect SDistinct (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | (STerm ("except", [STerm ("distinct",[]);q1;q2])) :: [] ->
      QSQL.sql_sql_except SDistinct (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | (STerm ("union", [q1;q2])) :: [] ->
      QSQL.sql_sql_union SAll (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | (STerm ("intersect", [q1;q2])) :: [] ->
      QSQL.sql_sql_intersect SAll (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | (STerm ("except", [q1;q2])) :: [] ->
      QSQL.sql_sql_except SAll (sexp_to_sql_query q1) (sexp_to_sql_query q2)
  | STerm (sterm, _) :: _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL sfw block: " ^ sterm))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside SQL sfw block")
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
      (sstring_to_coq_string cname, Ascending) :: sexp_to_sql_orders orders'
  | (STerm ("descending",[(STerm ("ref",[cname]))])) :: orders' ->
      (sstring_to_coq_string cname, Descending) :: sexp_to_sql_orders orders'
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
(*  | STerm ("const_list",const_list) ->
      List.fold_left (QSQL.sql_binary (map (fun e -> (QSQL.sql_unary sexp_to_sql_expr const_list)) *)
  | STerm ("cast",[STerm ("as",[SString "DATE"]); expr1]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (QcertCompiler.Enhanced_unary_sql_date_op QcertCompiler.Uop_sql_date_from_string)))
	(sexp_to_sql_expr expr1)
  | STerm ("literal",[SString "date"; SString sdate]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (Enhanced_unary_sql_date_op Uop_sql_date_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string sdate)))
  | STerm ("interval",[SString sinterval; STerm ("year",[])]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (Enhanced_unary_sql_date_op Uop_sql_date_interval_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string (sinterval ^ "-YEAR"))))
  | STerm ("interval",[SString sinterval; STerm ("month",[])]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (Enhanced_unary_sql_date_op Uop_sql_date_interval_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string (sinterval ^ "-MONTH"))))
  | STerm ("interval",[SString sinterval; STerm ("day",[])]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (Enhanced_unary_sql_date_op Uop_sql_date_interval_from_string)))
	(QSQL.sql_expr_const (Dstring (char_list_of_string (sinterval ^ "-DAY"))))
  | STerm ("deref",[cname;STerm ("ref",[tname])]) ->
      QSQL.sql_expr_column_deref (sstring_to_coq_string tname) (sstring_to_coq_string cname)
  | STerm ("ref",[cname]) -> (QSQL.sql_expr_column (sstring_to_coq_string cname))
  | STerm ("minus",[expr1]) ->
      QSQL.sql_expr_unary SMinus (sexp_to_sql_expr expr1)
  | STerm ("add",[expr1;expr2]) ->
      QSQL.sql_expr_binary SPlus (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("subtract",[expr1;expr2]) ->
      QSQL.sql_expr_binary SSubtract (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("multiply",[expr1;expr2]) ->
      QSQL.sql_expr_binary SMult (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("divide",[expr1;expr2]) ->
      QSQL.sql_expr_binary SDivide (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "substr";expr1;SInt n1;SInt n2]) ->
     QSQL.sql_expr_unary (SSubstring (n1-1,Some (n1-1+n2))) (sexp_to_sql_expr expr1) (* It's 'substring (expr from n1 for n2)' i.e., from n1 for n2 characters, with initial index 1 *)
  | STerm ("cases",
	   [STerm ("case", [STerm ("when", [condexpr])
			  ; STerm ("then", [expr1])])
	   ; STerm ("default", [expr2])]) ->
     QSQL.sql_expr_case
       (sexp_to_sql_cond condexpr)
       (sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "count"]) ->
      QSQL.sql_expr_agg_expr SCount QSQL.sql_expr_star
  | STerm ("function",[SString "count";expr1]) ->
      QSQL.sql_expr_agg_expr SCount (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "sum";expr1]) ->
      QSQL.sql_expr_agg_expr SSum (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "avg";expr1]) ->
      QSQL.sql_expr_agg_expr SAvg (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "min";expr1]) ->
      QSQL.sql_expr_agg_expr SMin (sexp_to_sql_expr expr1)
  | STerm ("function",[SString "max";expr1]) ->
      QSQL.sql_expr_agg_expr SMax (sexp_to_sql_expr expr1)
  | STerm ("query", _) -> QSQL.sql_expr_query (sexp_to_sql_query expr) (* XXX Nested query XXX *)
  | STerm ("extract",[STerm ("year",[]);expr1]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_YEAR))))
	(sexp_to_sql_expr expr1)
  | STerm ("extract",[STerm ("month",[]);expr1]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_MONTH))))
	(sexp_to_sql_expr expr1)
  | STerm ("extract",[STerm ("day",[]);expr1]) ->
      QSQL.sql_expr_unary (SUnaryForeignExpr (Obj.magic (Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_DAY))))
	(sexp_to_sql_expr expr1)
  | STerm ("function",[SString "date_minus";expr1;expr2]) ->
      QSQL.sql_expr_binary (SBinaryForeignExpr (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_minus)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_plus";expr1;expr2]) ->
      QSQL.sql_expr_binary (SBinaryForeignExpr (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_plus)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "concat";expr1;expr2]) ->
      QSQL.sql_expr_binary SConcat
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",(STerm ("partitionBy",_))::(SString fun_name)::_) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL expr: function (using 'partition by') " ^ fun_name))
  | STerm ("function", (SString fun_name)::_) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL expr: function " ^ fun_name))
  | STerm ("cast",(STerm ("as",[SString cast_type]))::_) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL expr: cast as " ^ cast_type))
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
  | STerm ("isNull",[expr1]) ->
      QSQL.sql_cond_binary SEq (sexp_to_sql_expr expr1) (QSQL.sql_expr_const (Dunit))
  | STerm ("function",[SString "date_le";expr1;expr2]) ->
      QSQL.sql_cond_binary (SBinaryForeignCond (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_le)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_lt";expr1;expr2]) ->
      QSQL.sql_cond_binary (SBinaryForeignCond (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_lt)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_gt";expr1;expr2]) ->
      QSQL.sql_cond_binary (SBinaryForeignCond (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_gt)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_ge";expr1;expr2]) ->
      QSQL.sql_cond_binary (SBinaryForeignCond (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_ge)))
	(sexp_to_sql_expr expr1) (sexp_to_sql_expr expr2)
  | STerm ("function",[SString "date_between";expr1;expr2;expr3]) ->
      let sql_expr1 = (sexp_to_sql_expr expr1) in
      let sql_expr2 = (sexp_to_sql_expr expr2) in
      let sql_expr3 = (sexp_to_sql_expr expr3) in
      QSQL.sql_cond_and
	(QSQL.sql_cond_binary (SBinaryForeignCond (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_le))) sql_expr2 sql_expr1)
	(QSQL.sql_cond_binary (SBinaryForeignCond (Obj.magic (Enhanced_binary_sql_date_op Bop_sql_date_le))) sql_expr1 sql_expr3)
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
    
(* SQL++ Section *)

let sqlpp_function_name_to_sexp_tag (name : QSQLPP.sqlpp_function_name) : string =
	begin match name with
	| SPFget_year -> "get_year"
	| SPFget_month -> "get_month"
	| SPFget_day -> "get_day"
	| SPFget_hour -> "get_hour"
	| SPFget_minute -> "get_minute"
	| SPFget_second -> "get_second"
	| SPFget_millisecond -> "get_millisecond"
	| SPFavg -> "avg"
	| SPFmin  -> "min"
	| SPFmax  -> "max"
	| SPFcount  -> "count"
	| SPFsum  -> "sum"
	| SPFcoll_avg -> "coll_avg"
	| SPFcoll_min -> "coll_min"
	| SPFcoll_max -> "coll_max"
	| SPFcoll_count -> "coll_count"
	| SPFcoll_sum -> "coll_sum"
	| SPFarray_avg -> "array_avg"
	| SPFarray_min -> "array_min"
	| SPFarray_max -> "array_max"
	| SPFarray_count -> "array_count"
	| SPFarray_sum -> "array_sum"
	| SPFsqrt -> "sqrt"
	| SPFsubstring -> "substring"
	| SPFregexp_contains -> "regexp_contains"
	| SPFcontains -> "contains"
	end

let rec sqlpp_expr_to_sexp (expr : QSQLPP.sqlpp_expr) : sexp =	 
  begin match expr with
  | SPPositive arg -> STerm("Positive", [sqlpp_expr_to_sexp arg])
  | SPNegative arg -> STerm("Negative", [sqlpp_expr_to_sexp arg])
  | SPExists arg -> STerm("Exists", [sqlpp_expr_to_sexp arg])
  | SPNot arg -> STerm("Not", [sqlpp_expr_to_sexp arg])
  | SPIsNull arg -> STerm("IsNull", [sqlpp_expr_to_sexp arg])
  | SPIsMissing arg -> STerm("IsMissing", [sqlpp_expr_to_sexp arg])
  | SPIsUnknown arg -> STerm("IsUnknown", [sqlpp_expr_to_sexp arg])                                  
  | SPPlus (arg1, arg2) -> STerm("Plus", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPMinus (arg1, arg2) -> STerm("Minus", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPMult (arg1, arg2) -> STerm("Mult", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2]) 
  | SPDiv (arg1, arg2) -> STerm("Div", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPMod (arg1, arg2) -> STerm("Mod", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPExp (arg1, arg2) -> STerm("Exp", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPConcat (arg1, arg2) -> STerm("Concat", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPIn (arg1, arg2) -> STerm("In", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPEq (arg1, arg2) -> STerm("Eq", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPFuzzyEq (arg1, arg2) -> STerm("FuzzyEq", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPNeq (arg1, arg2) -> STerm("Neq", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPLt (arg1, arg2) -> STerm("Lt", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPGt (arg1, arg2) -> STerm("Gt", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPLe (arg1, arg2) -> STerm("Le", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPGe (arg1, arg2) -> STerm("Ge", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPLike (arg1, arg2) -> STerm("Like", [sqlpp_expr_to_sexp arg1;coq_string_to_sstring arg2])
  | SPAnd (arg1, arg2) -> STerm("And", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPOr (arg1, arg2) -> STerm("Or", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2])
  | SPBetween (arg1, arg2, arg3) -> STerm("Between", [sqlpp_expr_to_sexp arg1;sqlpp_expr_to_sexp arg2;sqlpp_expr_to_sexp arg3])
  | SPSimpleCase (expr, whenthens, Some default) -> STerm("SimpleCase", (sqlpp_expr_to_sexp expr) :: STerm("Default", [sqlpp_expr_to_sexp default]) ::
			(List.map sqlpp_whenthen_to_sexp whenthens))
  | SPSimpleCase (expr, whenthens, None) -> STerm("SimpleCase", sqlpp_expr_to_sexp expr::(List.map sqlpp_whenthen_to_sexp whenthens))
  | SPSearchedCase (whenthens, Some default) -> STerm("SearchedCase", STerm("Default", [sqlpp_expr_to_sexp default])::(List.map sqlpp_whenthen_to_sexp whenthens))
  | SPSearchedCase (whenthens, None) -> STerm("SearchedCase", List.map sqlpp_whenthen_to_sexp whenthens)
  | SPSome (bindings, sat) -> STerm("Some", [STerm("Bindings", List.map sqlpp_var_in_to_sexp bindings); sqlpp_expr_to_sexp sat])
  | SPEvery (bindings, sat) -> STerm("Some", [STerm("Bindings", List.map sqlpp_var_in_to_sexp bindings); sqlpp_expr_to_sexp sat])
  | SPDot (expr, field) -> STerm("Dot", [coq_string_to_sstring field; sqlpp_expr_to_sexp expr])
  | SPIndex (prim, ind) -> STerm("Index", [sqlpp_expr_to_sexp ind; sqlpp_expr_to_sexp prim])
  | SPIndexAny (prim) -> STerm("IndexAny", [sqlpp_expr_to_sexp prim])
  | SPLiteral (data) -> data_to_sexp data
  | SPNull -> STerm("Null", [])
	| SPMissing -> STerm("Missing", [])
  | SPVarRef (name) -> STerm("VarRef", [coq_string_to_sstring name])
  | SPFunctionCall (name, exprs) -> STerm("FunctionCall", STerm((sqlpp_function_name_to_sexp_tag name), []) :: (List.map sqlpp_expr_to_sexp exprs))
  | SPArray (members) -> STerm("Array", (List.map sqlpp_expr_to_sexp members))
  | SPBag (members) -> STerm("Bag", (List.map sqlpp_expr_to_sexp members))
  | SPObject (fields) -> STerm("Object", (List.map sqlpp_field_to_sexp fields))
  | SPQuery (stmt) -> sqlpp_select_to_sexp stmt
	end
	
and sqlpp_whenthen_to_sexp (whenthen : QSQLPP.sqlpp_when_then) : sexp =
	begin match whenthen with
	| SPWhenThen (whenexp, thenexp) -> STerm("WhenThen", [sqlpp_expr_to_sexp whenexp; sqlpp_expr_to_sexp thenexp])
	end

and sqlpp_var_in_to_sexp (var_in : (char list * sqlpp_expr)) : sexp =
	STerm("VarIn", [coq_string_to_sstring (fst var_in); sqlpp_expr_to_sexp (snd var_in)])
	
and sqlpp_field_to_sexp (field : (char list * sqlpp_expr)) : sexp =
	STerm("Field", [coq_string_to_sstring (fst field) ; sqlpp_expr_to_sexp (snd field)])
	
and sqlpp_select_to_sexp (stmt : sqlpp_select_statement) : sexp =
	begin match stmt with
	| SPSelectStmt (lets, block, unions, SPOrderBy orderby) -> STerm("Select", STerm("Lets", List.map sqlpp_let_to_sexp lets) :: 
		(sqlpp_select_block_to_sexp block) :: STerm("Unions", List.map sqlpp_union_to_sexp unions) :: 
		STerm("Ordering", List.map sqlpp_order_by_to_sexp orderby)::[])
	| SPSelectStmt (lets, block, unions, SPNoOrderBy) -> STerm("Select", STerm("Lets", List.map sqlpp_let_to_sexp lets) :: 
		(sqlpp_select_block_to_sexp block) :: STerm("Unions", List.map sqlpp_union_to_sexp unions) ::
		STerm("Ordering", [])::[])
	end
	
and sqlpp_let_to_sexp (l : (char list * sqlpp_expr)) : sexp =
	STerm("Let", [coq_string_to_sstring (fst l); sqlpp_expr_to_sexp (snd l)])
	
and sqlpp_select_block_to_sexp (block : sqlpp_select_block) : sexp =
	begin match block with
	| SPSelectBlock (select, froms, lets1, where, groupby, lets2, having) -> STerm("SelectBlock", [(sqlpp_select_clause_to_sexp select);
			STerm("Froms", (List.map sqlpp_from_to_sexp froms)); STerm("Lets", (List.map sqlpp_let_to_sexp lets1)); 
			(sqlpp_where_to_sexp where); (sqlpp_group_to_sexp groupby);
			STerm("Lets", (List.map sqlpp_let_to_sexp lets2)); (sqlpp_having_to_sexp having)]) 
	end

and sqlpp_select_clause_to_sexp (clause : sqlpp_select) : sexp =
	begin match clause with
	| SPSelectSQL (distinct, projections) -> STerm("SelectSQL", sqlpp_distinct_to_sexp distinct::(List.map sqlpp_project_to_sexp projections))
	| SPSelectValue (distinct, expr) -> STerm("SelectValue", [sqlpp_distinct_to_sexp distinct; sqlpp_expr_to_sexp expr])
	end
	
and sqlpp_distinct_to_sexp (distinct : sqlpp_distinct) : sexp =
	begin match distinct with
	| SPDistinct -> STerm("Distinct", [])
	| SPAll -> STerm("All", [])
	end
	
and sqlpp_project_to_sexp (project : sqlpp_project) : sexp =
	begin match project with
	| SPProject (expr, Some name) -> STerm("Project", [sqlpp_expr_to_sexp expr; coq_string_to_sstring name])
	| SPProject (expr, None) -> STerm("Project", [sqlpp_expr_to_sexp expr])
	| SPProjectStar -> STerm("ProjectStar", [])
	end
	
and sqlpp_from_to_sexp (clause : sqlpp_from) : sexp =
	begin match clause with
	| SPFrom (expr, Some name, joins) -> STerm("From", sqlpp_expr_to_sexp expr :: STerm("as", [coq_string_to_sstring name]) ::
		(List.map sqlpp_join_clause_to_sexp joins))
	| SPFrom (expr, None, joins) ->  STerm("From", sqlpp_expr_to_sexp expr :: (List.map sqlpp_join_clause_to_sexp joins))
	end
	
and sqlpp_join_clause_to_sexp (clause : sqlpp_join_clause) : sexp =
	begin match clause with
	| SPJoin (jtype, expr1, Some var, expr2) -> STerm("Join", [sqlpp_join_type_to_sexp jtype; STerm("as", [coq_string_to_sstring var]); 
			sqlpp_expr_to_sexp expr1; sqlpp_expr_to_sexp expr2])
	| SPJoin (jtype, expr1, None, expr2) -> STerm("Join", [sqlpp_join_type_to_sexp jtype; sqlpp_expr_to_sexp expr1; 
			sqlpp_expr_to_sexp expr2])
	| SPUnnest (jtype, expr, Some var, Some positionVar) -> STerm("Unnest", [sqlpp_join_type_to_sexp jtype; 
			STerm("as", [coq_string_to_sstring var]); STerm("at", [coq_string_to_sstring positionVar]); sqlpp_expr_to_sexp expr])
	| SPUnnest (jtype, expr, Some var, None) -> STerm("Unnest", [sqlpp_join_type_to_sexp jtype; 
			STerm("as", [coq_string_to_sstring var]); sqlpp_expr_to_sexp expr])
	| SPUnnest (jtype, expr, None, Some positionVar) -> STerm("Unnest", [sqlpp_join_type_to_sexp jtype; 
			STerm("at", [coq_string_to_sstring positionVar]); sqlpp_expr_to_sexp expr])
	| SPUnnest (jtype, expr, None, None) -> STerm("Unnest", [sqlpp_join_type_to_sexp jtype; sqlpp_expr_to_sexp expr])
	end
	
and sqlpp_join_type_to_sexp (jtype : sqlpp_join_type) : sexp =
	begin match jtype with
	| SPInner -> STerm("Inner", [])
	| SPLeftOuter -> STerm("LeftOuter", [])
	end
	
and sqlpp_group_to_sexp (clause : sqlpp_group_by) : sexp =
	begin match clause with
	| SPGroupBy (keys, Some aspart) -> STerm("GroupBy", [STerm("Keys", List.map sqlpp_group_key_to_sexp keys); sqlpp_group_as_to_sexp aspart])
	| SPGroupBy (keys, None) -> STerm("GroupBy", [STerm("Keys", List.map sqlpp_group_key_to_sexp keys)])
	| SPNoGroupBy -> STerm("GroupBy", [])
	end
	
and sqlpp_group_as_to_sexp (aspart : (char list * ((char list * char list) list)))	: sexp =
	begin match aspart with
	| (name , renames) -> STerm("GroupAs", coq_string_to_sstring name :: (List.map sqlpp_rename_to_sexp renames))
	end
	
and sqlpp_rename_to_sexp (rename : (char list * char list)) : sexp =
	begin match rename with
	| (var , varref) -> STerm("Rename", [coq_string_to_sstring var; coq_string_to_sstring varref])
	end
	
and sqlpp_group_key_to_sexp (key : (sqlpp_expr * char list option)) : sexp =
	begin match key with
	| (expr, Some name) -> STerm("Key", [sqlpp_expr_to_sexp expr; STerm("as", [coq_string_to_sstring name])])
	| (expr, None) -> STerm("Key", [sqlpp_expr_to_sexp expr])
	end
	
and sqlpp_where_to_sexp (clause : sqlpp_where) : sexp =
	begin match clause with
	| SPWhere expr -> STerm("Where", [sqlpp_expr_to_sexp expr])
	| SPNoWhere -> STerm("Where", [])
	end
	
and sqlpp_having_to_sexp (having : sqlpp_expr option) : sexp =
	begin match having with
	| Some expr -> STerm("Having", [sqlpp_expr_to_sexp expr])
	| None -> STerm("Having", [])
	end
	
and sqlpp_union_to_sexp(union : sqlpp_union_element) : sexp = 
	begin match union with
	| SPBlock (block) -> sqlpp_select_block_to_sexp block
	| SPSubquery (stmt) -> sqlpp_select_to_sexp stmt
	end
	
and sqlpp_order_by_to_sexp(order : (sqlpp_expr * sqlpp_order_spec)) : sexp = 
	begin match order with
	| (expr , Ascending) -> STerm("OrderBy", [sqlpp_expr_to_sexp (fst order) ; SString "ASC"])
	| (expr , Descending) -> STerm("OrderBy", [sqlpp_expr_to_sexp (fst order) ; SString "DESC"])
	end

let sqlpp_to_sexp (e : QLang.sqlpp) : sexp = sqlpp_expr_to_sexp e

let sexp_to_sqlpp_function_name (s : sexp) : sqlpp_function_name =
	begin match s with
	| STerm("get_year", []) -> SPFget_year
	| STerm("get_month", []) -> SPFget_month 
	| STerm("get_day", []) -> SPFget_day
	| STerm("get_hour", []) -> SPFget_hour
	| STerm("get_minute", []) -> SPFget_minute
	| STerm("get_second", []) -> SPFget_second
	| STerm("get_millisecond", []) -> SPFget_millisecond
	| STerm("avg", []) -> SPFavg
	| STerm("min", []) -> SPFmin
	| STerm("max", []) -> SPFmax
	| STerm("count", []) -> SPFcount
	| STerm("sum", []) -> SPFsum
	| STerm("coll_avg", []) -> SPFcoll_avg
	| STerm("coll_min", []) -> SPFcoll_min
	| STerm("coll_max", []) -> SPFcoll_max
	| STerm("coll_count", []) -> SPFcoll_count
	| STerm("coll_sum", []) -> SPFcoll_sum
	| STerm("array_avg", []) -> SPFarray_avg
	| STerm("array_min", []) -> SPFarray_min
	| STerm("array_max", []) -> SPFarray_max
	| STerm("array_count", []) -> SPFarray_count
	| STerm("array_sum", []) -> SPFarray_sum
	| STerm("sqrt", []) -> SPFsqrt
	| STerm("substring", []) -> SPFsubstring
	| STerm("regexp_contains", []) -> SPFregexp_contains
	| STerm("contains", []) -> SPFcontains
	| STerm(x, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL++ function call expression: " ^ x))
	end
	
let rec sexp_to_sqlpp_expr (stmt : sexp)  =
  begin match stmt with
	| STerm ("Positive", [s]) -> QSQLPP.sqlpp_sqlpp_positive (sexp_to_sqlpp_expr s) 
  | STerm ("Negative", [s]) -> QSQLPP.sqlpp_sqlpp_negative (sexp_to_sqlpp_expr s)
  | STerm ("Exists", [s]) -> QSQLPP.sqlpp_sqlpp_exists (sexp_to_sqlpp_expr s)
  | STerm ("Not", [s]) -> QSQLPP.sqlpp_sqlpp_not (sexp_to_sqlpp_expr s)
  | STerm ("IsNull", [s]) -> QSQLPP.sqlpp_sqlpp_is_null (sexp_to_sqlpp_expr s)
  | STerm ("IsMissing", [s]) -> QSQLPP.sqlpp_sqlpp_is_missing (sexp_to_sqlpp_expr s)
  | STerm ("IsUnknown", [s]) -> QSQLPP.sqlpp_sqlpp_is_unknown (sexp_to_sqlpp_expr s)
	| STerm("Plus", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_plus (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Minus", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_minus (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Mult", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_mult (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Div", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_div (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Mod", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_mod (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Exp", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_exp (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Concat", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_concat (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("In", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_in (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Eq", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_eq (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("FuzzyEq", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_fuzzy_eq (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Neq", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_neq (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Lt", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_lt (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Gt", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_gt (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Le", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_le (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Ge", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_ge (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Like", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_like (sexp_to_sqlpp_expr expr1) (sstring_to_coq_string expr2)
	| STerm("And", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_and (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Or", [expr1;expr2]) -> QSQLPP.sqlpp_sqlpp_or (sexp_to_sqlpp_expr expr1) (sexp_to_sqlpp_expr expr2)
	| STerm("Between", [e1;e2;e3]) -> QSQLPP.sqlpp_sqlpp_between (sexp_to_sqlpp_expr e1) (sexp_to_sqlpp_expr e2) (sexp_to_sqlpp_expr e3)
	| STerm("SimpleCase", cond::STerm("Default", [els])::rest) -> 
		QSQLPP.sqlpp_sqlpp_simple_case (sexp_to_sqlpp_expr cond) (List.map sexp_to_sqlpp_when_then rest) (Some (sexp_to_sqlpp_expr els))
	| STerm("SimpleCase", cond::rest) -> 
		QSQLPP.sqlpp_sqlpp_simple_case (sexp_to_sqlpp_expr cond) (List.map sexp_to_sqlpp_when_then rest) None
	| STerm("SearchedCase", STerm("Default", [els])::rest) -> 
		QSQLPP.sqlpp_sqlpp_searched_case (List.map sexp_to_sqlpp_when_then rest) (Some (sexp_to_sqlpp_expr els))
	| STerm("SearchedCase", rest) -> 
		QSQLPP.sqlpp_sqlpp_searched_case (List.map sexp_to_sqlpp_when_then rest) None
	| STerm("Some", [STerm("Bindings", vars);sat]) ->
		QSQLPP.sqlpp_sqlpp_some (List.map sexp_to_sqlpp_binding vars) (sexp_to_sqlpp_expr sat)
	| STerm("Every", [STerm("Bindings", vars);sat]) ->
		QSQLPP.sqlpp_sqlpp_every (List.map sexp_to_sqlpp_binding vars) (sexp_to_sqlpp_expr sat)
	| STerm("Dot", [s;expr]) ->
		QSQLPP.sqlpp_sqlpp_dot (sexp_to_sqlpp_expr expr) (sstring_to_coq_string s)
	| STerm("Index", [ind;prim]) ->
		QSQLPP.sqlpp_sqlpp_index (sexp_to_sqlpp_expr prim) (sexp_to_sqlpp_expr ind)
	| STerm("IndexAny", [prim]) ->
		QSQLPP.sqlpp_sqlpp_index_any (sexp_to_sqlpp_expr prim)
  | SString s ->
    QSQLPP.sqlpp_sqlpp_literal (Dstring (char_list_of_string s))
  | SFloat f ->
    QSQLPP.sqlpp_sqlpp_literal (Dforeign (Obj.magic (Enhancedfloat f)))
  | SInt i ->
    QSQLPP.sqlpp_sqlpp_literal (Dnat i)
  | SBool b ->
		QSQLPP.sqlpp_sqlpp_literal (Dbool b)		
	| STerm("Null", []) -> QSQLPP.sqlpp_sqlpp_null
	| STerm("Missing", []) -> QSQLPP.sqlpp_sqlpp_missing
	| STerm("VarRef", [s]) -> 
		QSQLPP.sqlpp_sqlpp_var_ref (sstring_to_coq_string s)
	| STerm("FunctionCall", s::args) ->
		QSQLPP.sqlpp_sqlpp_function_call (sexp_to_sqlpp_function_name s) (List.map sexp_to_sqlpp_expr args)
	| STerm("Array", members) ->
		QSQLPP.sqlpp_sqlpp_array (List.map sexp_to_sqlpp_expr members)
	| STerm("Bag", members) ->
		QSQLPP.sqlpp_sqlpp_bag (List.map sexp_to_sqlpp_expr members)
	| STerm("Object", fields) ->
		QSQLPP.sqlpp_sqlpp_object (List.map sexp_to_sqlpp_field fields)
	| STerm("Select", body) ->
		QSQLPP.sqlpp_sqlpp_query (sexp_to_sqlpp_select_body body)
  | STerm (sterm, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL++ expression: " ^ sterm))
  end

and sexp_to_sqlpp_when_then (se : sexp) : QSQLPP.sqlpp_when_then =
	begin	match se with
	| STerm("WhenThen", [e1;e2]) -> QSQLPP.sqlpp_sqlpp_when_then (sexp_to_sqlpp_expr e1) (sexp_to_sqlpp_expr e2)
	| STerm("WhenThen", _) -> raise (Qcert_Error "Not well-formed operands to WhenThen node")
	| STerm(sterm, _) -> raise (Qcert_Error ("Unexpected node where WhenThen expected: " ^ sterm))
	| _ ->
		raise (Qcert_Error "Non STerm node found where WhenThen node expected in SQL++ case expression")
	end
		
and sexp_to_sqlpp_binding (se : sexp) : (char list * sqlpp_expr) =
	begin match se with
	| STerm ("VarIn", [s;expr]) -> (sstring_to_coq_string s, sexp_to_sqlpp_expr expr)				
	| _ ->
		raise (Qcert_Error "VarIn node not found where expected in SQL++ quantified expression")
	end

and sexp_to_sqlpp_field (se : sexp) : (char list * sqlpp_expr) =
	begin match se with
	| STerm ("Field", [name;value]) -> (sstring_to_coq_string name, sexp_to_sqlpp_expr value)
	| _ ->
		raise (Qcert_Error "Field not found where expected in SQL++ object constructor")
	end
	
and sexp_to_sqlpp_select_body (sl : sexp list) =
	begin match sl with
	| STerm("Lets", lets)::STerm("SelectBlock", block)::STerm("Unions", unions)::STerm("Ordering", ordering)::[] ->
		QSQLPP.sqlpp_sqlpp_select_stmt (List.map sexp_to_sqlpp_let lets) (sexp_to_sqlpp_select_block block) 
		   (List.map sexp_to_sqlpp_union unions) (sexp_to_sqlpp_order_by ordering)
	| _ ->
		raise (Qcert_Error "Not well-formed S-expr list in SQL++ select statement")
	end
	
and sexp_to_sqlpp_let (se : sexp) : (char list * sqlpp_expr) =
	begin match se with	
	| STerm("Let", [s;expr]) -> (sstring_to_coq_string s, sexp_to_sqlpp_expr expr)
	| _ ->
		raise (Qcert_Error "Let clause not found where expected in SQL++ select body");
	end
	
and sexp_to_sqlpp_select_block (sl : sexp list) : QSQLPP.sqlpp_select_block =
	begin match sl with
	| STerm("SelectSQL", select)::STerm("Froms", froms)::STerm("Lets", lets1)::STerm("Where", where)::
						STerm("GroupBy", groups)::STerm("Lets", lets2)::STerm("Having", having)::[] ->
    QSQLPP.sqlpp_sqlpp_select_block (sexp_to_sqlpp_select_sql select) (List.map sexp_to_sqlpp_from froms) (List.map sexp_to_sqlpp_let lets1)
			(sexp_to_sqlpp_where where) (sexp_to_sqlpp_group_by groups) (List.map sexp_to_sqlpp_let lets2) (sexp_to_sqlpp_having having)
	| STerm("SelectValue", select)::STerm("Froms", froms)::STerm("Lets", lets1)::STerm("Where", where)::
						STerm("GroupBy", groups)::STerm("Lets", lets2)::STerm("Having", having)::[] ->
    QSQLPP.sqlpp_sqlpp_select_block (sexp_to_sqlpp_select_value select) (List.map sexp_to_sqlpp_from froms) (List.map sexp_to_sqlpp_let lets1)
			(sexp_to_sqlpp_where where) (sexp_to_sqlpp_group_by groups) (List.map sexp_to_sqlpp_let lets2) (sexp_to_sqlpp_having having)
	| _ ->
		raise (Qcert_Error "Select block not found where expected in SQL++ select body");
  end
	
and sexp_to_sqlpp_select_sql (sl : sexp list) : QSQLPP.sqlpp_select =
	begin match sl with
	| STerm(s, [])::projections -> QSQLPP.sqlpp_sqlpp_select_sql (sexp_to_sqlpp_distinct s)	(List.map sexp_to_sqlpp_project projections)
	| _ -> raise (Qcert_Error "Not well-formed S-expr in SQL-style select in SQL++")
	end
	
and sexp_to_sqlpp_select_value (sl : sexp list) : QSQLPP.sqlpp_select =
	begin match sl with
	| STerm(s, [])::[expr] -> QSQLPP.sqlpp_sqlpp_select_value (sexp_to_sqlpp_distinct s)	(sexp_to_sqlpp_expr expr)
	| _ -> raise (Qcert_Error "Not well-formed S-expr in value-style select in SQL++")
	end
	
and sexp_to_sqlpp_distinct (s : string) : QSQLPP.sqlpp_distinct =
		begin match s with
		| "Distinct" -> QSQLPP.sqlpp_sqlpp_distinct
		| "All" -> QSQLPP.sqlpp_sqlpp_all
		| _ -> raise (Qcert_Error "Not well-formed S-expr in Distinct|All indicator in SQL++ select clause") 
		end
		
and sexp_to_sqlpp_where (sl : sexp list) : QSQLPP.sqlpp_where =
	begin match sl with
	| [where] -> QSQLPP.sqlpp_sqlpp_where (sexp_to_sqlpp_expr where)
	| [] -> QSQLPP.sqlpp_sqlpp_no_where
	| _ -> raise (Qcert_Error "Not well-formed S-expr in SQL++ where clause")
	end
	
and sexp_to_sqlpp_having (sl : sexp list) =
	begin match sl with
	| [having] -> Some (sexp_to_sqlpp_expr having)
	| [] -> None
	| _ -> raise (Qcert_Error "Not well-formed S-expr in SQL++ 'having' clause")
	end
	
and sexp_to_sqlpp_union (se : sexp) : QSQLPP.sqlpp_union_element =
	begin match se with
	| STerm("Select", body) -> QSQLPP.sqlpp_sqlpp_subquery (sexp_to_sqlpp_select_body body)
	| STerm("SelectBlock", block) -> QSQLPP.sqlpp_sqlpp_block (sexp_to_sqlpp_select_block block)
	| _ -> 	raise (Qcert_Error "Not well-formed S-expr in SQL++ union list in select statement")
	end
		
and sexp_to_sqlpp_order_by (sl : sexp list) : QSQLPP.sqlpp_order_by =
	begin match sl with
	| [] -> QSQLPP.sqlpp_sqlpp_no_order_by
	| _ -> QSQLPP.sqlpp_sqlpp_order_by (List.map sexp_to_sqlpp_order_by_element sl)
	end
	
and sexp_to_sqlpp_order_by_element (se: sexp) =
	begin match se with
	| STerm("OrderBy", [expr;direction]) -> (sexp_to_sqlpp_expr expr, sexp_to_sqlpp_sort_desc direction)
	| _ -> raise (Qcert_Error "Not well-formed S-expr in SQL++ order-by clause")
	end
	
and sexp_to_sqlpp_sort_desc (direction: sexp) =
	begin match direction with
	| SString "ASC" -> Ascending
	| SString "DESC" -> Descending
	| _ -> raise (Qcert_Error "Invalid sort direction indictor in SQL++ order-by clause")
	end 
	
and sexp_to_sqlpp_project (se : sexp) : QSQLPP.sqlpp_project =
	begin match se with
	| STerm("Project", [expr]) -> QSQLPP.sqlpp_sqlpp_project (sexp_to_sqlpp_expr expr, None)
	| STerm("Project", [expr;name]) -> QSQLPP.sqlpp_sqlpp_project (sexp_to_sqlpp_expr expr , Some (sstring_to_coq_string name))
	| STerm("ProjectStar", []) -> QSQLPP.sqlpp_sqlpp_project_star
	| _ -> raise (Qcert_Error "Not well-formed S-expr in SQL++ projection in SQL-style select")
	end
	
and sexp_to_sqlpp_from (se : sexp) : QSQLPP.sqlpp_from =
	begin match se with
	| STerm("From", expr :: STerm("as", [alias]) :: joins) -> 
		QSQLPP.sqlpp_sqlpp_from (sexp_to_sqlpp_expr expr) (Some (sstring_to_coq_string alias)) (List.map sexp_to_sqlpp_join_clause joins) 
	| STerm("From", expr :: joins) -> 
		QSQLPP.sqlpp_sqlpp_from (sexp_to_sqlpp_expr expr) None (List.map sexp_to_sqlpp_join_clause joins) 
	| _ -> raise (Qcert_Error "Not well-formed S-expr in from clause")
	end
	
and sexp_to_sqlpp_join_clause (se : sexp) : QSQLPP.sqlpp_join_clause =
	begin match se with
	| STerm("Join", [kind ; STerm("as", [alias]) ; expr1 ; expr2]) -> 
		QSQLPP.sqlpp_sqlpp_join (sexp_to_sqlpp_join_type kind) (sexp_to_sqlpp_expr expr1) 
			(Some (sstring_to_coq_string alias)) (sexp_to_sqlpp_expr expr2)
	| STerm("Join", [kind ; expr1 ; expr2]) ->
		QSQLPP.sqlpp_sqlpp_join (sexp_to_sqlpp_join_type kind) (sexp_to_sqlpp_expr expr1) None (sexp_to_sqlpp_expr expr2)
	| STerm("Unnest", [kind ; STerm("as", [alias]) ; STerm("at", [position]) ; expr]) ->
		QSQLPP.sqlpp_sqlpp_unnest (sexp_to_sqlpp_join_type kind) (sexp_to_sqlpp_expr expr)
			(Some (sstring_to_coq_string alias)) (Some (sstring_to_coq_string position))
	| STerm("Unnest", [kind ; STerm("at", [position]) ; expr]) ->
		QSQLPP.sqlpp_sqlpp_unnest (sexp_to_sqlpp_join_type kind) (sexp_to_sqlpp_expr expr) None (Some (sstring_to_coq_string position)) 
	| STerm("Unnest", [kind ; STerm("as", [alias]) ; expr]) ->
		QSQLPP.sqlpp_sqlpp_unnest (sexp_to_sqlpp_join_type kind) (sexp_to_sqlpp_expr expr) (Some (sstring_to_coq_string alias)) None
	| STerm("Unnest", [kind ; expr]) ->
		QSQLPP.sqlpp_sqlpp_unnest (sexp_to_sqlpp_join_type kind) (sexp_to_sqlpp_expr expr) None None
	| _ -> raise (Qcert_Error "Not well-formed S-expr found where Join or Unnest is expected")
	end
	
and sexp_to_sqlpp_join_type (se : sexp) : QSQLPP.sqlpp_join_type =
	begin match se with
	| STerm("Inner", []) -> QSQLPP.sqlpp_sqlpp_inner
	| STerm("LeftOuter", []) -> QSQLPP.sqlpp_sqlpp_left_outer
	| _ -> raise (Qcert_Error "Not well-formed S-expr found where a join type is expected")
	end
	
and sexp_to_sqlpp_group_by (sl : sexp list) : QSQLPP.sqlpp_group_by =
	begin match sl with
	| [STerm("Keys", keys) ; STerm("GroupAs" , var::renames)] ->
		QSQLPP.sqlpp_sqlpp_group_by (List.map sexp_to_sqlpp_group_key keys)
			(Some (sstring_to_coq_string var, (List.map sexp_to_sqlpp_rename renames)))
	| [STerm("Keys", keys) ] ->
		QSQLPP.sqlpp_sqlpp_group_by (List.map sexp_to_sqlpp_group_key keys) None
	| [] ->
		QSQLPP.sqlpp_sqlpp_no_group_by
	| _ -> raise (Qcert_Error "Not well-formed S-expr in group-by clause")
	end
	
and sexp_to_sqlpp_group_key (se : sexp) =
	begin match se with
	| STerm("Key", [expr; STerm("as", [name])]) ->
		(sexp_to_sqlpp_expr expr , Some (sstring_to_coq_string name))
	| STerm("Key", [expr]) ->
		(sexp_to_sqlpp_expr expr , None)
	| _ -> raise (Qcert_Error "Not well-formed S-expr in group-by clause (Key expected)")
	end

and sexp_to_sqlpp_rename (se : sexp) =
	begin match se with
	| STerm("Rename", [string1 ; string2 ]) ->
		(sstring_to_coq_string string1, sstring_to_coq_string string2)
	| _ -> raise (Qcert_Error "Not well-formed S-expr in group-by clause (group-as portion)")
	end
			
let sexp_to_sqlpp (se : sexp) : QLang.sqlpp = sexp_to_sqlpp_expr se
	
(* Query translations *)
let sexp_to_query (lang: QLang.language) (se: sexp) : QLang.query =
  begin match lang with
  | L_tech_rule ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_designer_rule -> Q_camp_rule (sexp_to_camp_rule se)
  | L_oql ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_sql -> Q_sql (sexp_to_sql se)
	| L_sqlpp -> Q_sqlpp (sexp_to_sqlpp se)
  | L_lambda_nra ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_camp_rule -> Q_camp_rule (sexp_to_camp_rule se)
  | L_camp -> Q_camp (sexp_to_camp se)
  | L_nra ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_nraenv_core -> Q_nraenv_core (sexp_to_nraenv se)
  | L_nraenv -> 
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_nnrc_core -> Q_nnrc_core (sexp_to_nnrc se)
  | L_nnrc -> Q_nnrc (sexp_to_nnrc se)
  | L_nnrcmr -> Q_nnrcmr (sexp_to_nnrcmr se)
  | L_cldmr -> Q_cldmr (sexp_to_cldmr se)
  | L_dnnrc ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_dnnrc_typed ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_javascript
  | L_java
  | L_spark_rdd
  | L_spark_df
  | L_cloudant ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_error err ->
      raise (Qcert_Error ("sexp_to_query: "^(Util.string_of_char_list err)))
  end

let query_to_sexp (q: QLang.query) : sexp =
  begin match q with
  | Q_tech_rule _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_designer_rule _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_oql _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_sql _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_sqlpp q -> sqlpp_to_sexp q
  | Q_lambda_nra _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_camp_rule q -> camp_rule_to_sexp q
  | Q_camp q -> camp_to_sexp q
  | Q_nra _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_nraenv_core q -> nraenv_to_sexp q
  | Q_nraenv _ -> 
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_nnrc_core q -> nnrc_to_sexp q
  | Q_nnrc q -> nnrc_to_sexp q
  | Q_nnrcmr q -> nnrcmr_to_sexp q
  | Q_cldmr q -> cldmr_to_sexp q
  | Q_dnnrc _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_dnnrc_typed _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_javascript _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_java _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_spark_rdd _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_spark_df _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_cloudant _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_error err ->
      SString ("query_to_sexp: "^(Util.string_of_char_list err))
  end
