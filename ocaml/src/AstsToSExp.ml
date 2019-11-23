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
  begin match fd with
  | Enhancedstring s -> STerm ("enhanced_string", (SString s)::[])
  | Enhancedtimescale ts -> STerm ("dtime_scale", (SString (PrettyCommon.timescale_as_string ts))::[])
  | Enhancedtimeduration td -> raise Not_found
  | Enhancedtimepoint tp -> raise Not_found
  | Enhancedsqldate td -> raise Not_found
  | Enhancedsqldateinterval tp -> raise Not_found
  end

let rec data_to_sexp (d : QData.qdata) : sexp =
  begin match d with
  | Dunit -> STerm ("dunit", [])
  | Dnat n -> SInt n
  | Dfloat f -> SFloat f
  | Dbool b -> SBool b
  | Dstring s -> SString (string_of_char_list s)
  | Dcoll dl -> STerm ("dcoll", List.map data_to_sexp dl)
  | Drec adl -> STerm ("drec", List.map drec_to_sexp adl)
  | Dleft d -> STerm ("dleft", data_to_sexp d :: [])
  | Dright d -> STerm ("dright", data_to_sexp d :: [])
  | Dbrand (bs,d) -> STerm ("dbrand", (STerm ("brands", dbrands_to_sexp bs)) :: (STerm ("value", (data_to_sexp d) :: [])) :: [])
  | Dforeign fdt -> foreign_data_to_sexp (Obj.magic fdt)
  end
and drec_to_sexp (ad : char list * QData.qdata) : sexp =
  STerm ("datt", (SString (string_of_char_list (fst ad))) :: (data_to_sexp (snd ad)) :: [])

let rec sexp_to_data (se:sexp) : QData.qdata =
  begin match se with
  | STerm ("dunit", []) -> Dunit
  | SBool b -> Dbool b
  | SInt n -> Dnat n
  | SFloat f -> Dfloat f
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
  end
and sexp_to_drec (sel:sexp) : (char list * QData.qdata) =
  begin match sel with
  | STerm ("datt", (SString s) :: se :: []) ->
      (char_list_of_string s, sexp_to_data se)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside drec")
  end

(* Operators Section *)

let nat_arithbop_to_sexp (b:nat_arith_binary_op) : sexp =
  STerm (PrettyCommon.string_of_nat_arith_binary_op b,[])
  
let float_arithbop_to_sexp (b:float_arith_binary_op) : sexp =
  STerm (PrettyCommon.string_of_float_arith_binary_op b,[])
  
let float_comparebop_to_sexp (b:float_compare_binary_op) : sexp =
  STerm (PrettyCommon.string_of_float_compare_binary_op b,[])
  
let sexp_to_nat_arithbop (se:sexp) : nat_arith_binary_op =
  begin match se with
  | STerm (s,[]) -> PrettyCommon.nat_arith_binary_op_of_string s
  | _ ->
      raise  (Qcert_Error "Not well-formed S-expr inside arith binary_op")
  end
  
let sexp_to_float_arithbop (se:sexp) : float_arith_binary_op =
  begin match se with
  | STerm (s,[]) -> PrettyCommon.float_arith_binary_op_of_string s
  | _ ->
      raise  (Qcert_Error "Not well-formed S-expr inside arith binary_op")
  end

let sexp_to_float_comparebop (se:sexp) : float_compare_binary_op =
  begin match se with
  | STerm (s,[]) -> PrettyCommon.float_compare_binary_op_of_string s
  | _ ->
      raise  (Qcert_Error "Not well-formed S-expr inside compare binary_op")
  end

let binary_op_to_sexp (b:binary_op) : sexp =
  begin match b with
  | OpEqual -> STerm ("OpEqual",[])
  | OpBagUnion -> STerm ("OpBagUnion",[])
  | OpRecConcat -> STerm ("OpRecConcat",[])
  | OpRecMerge -> STerm ("OpRecMerge",[])
  | OpAnd -> STerm ("OpAnd",[])
  | OpOr -> STerm ("OpOr",[])
  | OpNatBinary ab -> STerm ("OpNatBinary",[nat_arithbop_to_sexp ab])
  | OpFloatBinary ab -> STerm ("OpFloatBinary",[float_arithbop_to_sexp ab])
  | OpFloatCompare ab -> STerm ("OpFloatBinary",[float_comparebop_to_sexp ab])
  | OpLt -> STerm ("OpLt",[])
  | OpLe -> STerm ("OpLe",[])
  | OpBagDiff -> STerm ("OpBagDiff",[])
  | OpBagMin -> STerm ("OpBagMin",[])
  | OpBagMax -> STerm ("OpBagMax",[])
  | OpBagNth -> STerm ("OpBagNth",[])
  | OpContains -> STerm ("OpContains",[])
  | OpStringConcat -> STerm ("OpStringConcat",[])
  | OpStringJoin -> STerm ("OpStringJoin",[])
  | OpForeignBinary fbop -> SString (PrettyCommon.string_of_foreign_binary_op (Obj.magic fbop))
  end

let sexp_to_binary_op (se:sexp) : binary_op =
  begin match se with
  | STerm ("OpEqual",[]) -> OpEqual
  | STerm ("OpBagUnion",[]) -> OpBagUnion
  | STerm ("OpRecConcat",[]) -> OpRecConcat
  | STerm ("OpRecMerge",[]) -> OpRecMerge
  | STerm ("OpAnd",[]) -> OpAnd
  | STerm ("OpOr",[]) -> OpOr
  | STerm ("OpNatBinary",[se']) -> OpNatBinary (sexp_to_nat_arithbop se')
  | STerm ("OpFloatBinary",[se']) -> OpFloatBinary (sexp_to_float_arithbop se')
  | STerm ("OpFloatCompare",[se']) -> OpFloatCompare (sexp_to_float_comparebop se')
  | STerm ("OpLt",[]) -> OpLt
  | STerm ("OpLe",[]) -> OpLe
  | STerm ("FloatLt",[]) -> OpFloatCompare FloatLt
  | STerm ("FloatLe",[]) -> OpFloatCompare FloatLe
  | STerm ("FloatGt",[]) -> OpFloatCompare FloatGt
  | STerm ("FloatGe",[]) -> OpFloatCompare FloatGe
  | STerm ("OpBagDiff",[]) -> OpBagDiff
  | STerm ("OpBagMin",[]) -> OpBagMin
  | STerm ("OpBagMax",[]) -> OpBagMax
  | STerm ("OpBagNth",[]) -> OpBagNth
  | STerm ("OpContains",[]) -> OpContains
  | STerm ("OpStringConcat",[]) -> OpStringConcat
  | STerm ("OpStringJoin",[]) -> OpStringJoin
  | SString fbop -> OpForeignBinary (Obj.magic (PrettyCommon.foreign_binary_op_of_string fbop))
  (* WARNING: Those are not printed, only parsed *)
  | STerm ("OpTimeAs",[]) -> Enhanced.Ops.Binary.coq_OpTimeAs
  | STerm ("OpTimeShift",[]) -> Enhanced.Ops.Binary.coq_OpTimeShift
  | STerm ("OpTimeNe",[]) -> Enhanced.Ops.Binary.coq_OpTimeNe
  | STerm ("OpTimeLt",[]) -> Enhanced.Ops.Binary.coq_OpTimeLt
  | STerm ("OpTimeLe",[]) -> Enhanced.Ops.Binary.coq_OpTimeLe
  | STerm ("OpTimeGt",[]) -> Enhanced.Ops.Binary.coq_OpTimeGt
  | STerm ("OpTimeGe",[]) -> Enhanced.Ops.Binary.coq_OpTimeGe
  | STerm ("OpTimeDurationFromScale",[]) -> Enhanced.Ops.Binary.coq_OpTimeDurationFromScale
  | STerm ("OpTimeDurationBetween",[]) -> Enhanced.Ops.Binary.coq_OpTimeDurationBetween
  | STerm ("OpSqlDatePlus",[]) -> Enhanced.Ops.Binary.coq_OpSqlDatePlus
  | STerm ("OpSqlDateMinus",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateMinus
  | STerm ("OpSqlDateNe",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateNe
  | STerm ("OpSqlDateLt",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateLt
  | STerm ("OpSqlDateLe",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateLe
  | STerm ("OpSqlDateGt",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateGt
  | STerm ("OpSqlDateGe",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateGe
  | STerm ("OpSqlDateIntervalBetween",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateIntervalBetween
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside arith binary_op with name " ^ t))
  | _ -> raise  (Qcert_Error "Not well-formed S-expr inside arith binary_op")
  end

let nat_arith_unary_op_to_sexp (b:nat_arith_unary_op) : sexp =
  STerm (PrettyCommon.string_of_nat_arith_unary_op b,[])

let sexp_to_nat_arith_unary_op (se:sexp) : nat_arith_unary_op =
  begin match se with
  | STerm (s,[]) -> PrettyCommon.nat_arith_unary_op_of_string s
  | _ ->
      raise  (Qcert_Error "Not well-formed S-expr inside arith unary_op")
  end

let float_arith_unary_op_to_sexp (b:float_arith_unary_op) : sexp =
  STerm (PrettyCommon.string_of_float_arith_unary_op b,[])

let sexp_to_float_arith_unary_op (se:sexp) : float_arith_unary_op =
  begin match se with
  | STerm (s,[]) -> PrettyCommon.float_arith_unary_op_of_string s
  | _ ->
      raise  (Qcert_Error "Not well-formed S-expr inside arith unary_op")
  end

let unary_op_to_sexp (u:unary_op) : sexp =
  begin match u with
  | OpIdentity -> STerm ("OpIdentity",[])
  | OpNeg -> STerm ("OpNeg",[])
  | OpBag -> STerm ("OpBag",[])
  | OpCount -> STerm ("OpCount",[])
  | OpFlatten -> STerm ("OpFlatten",[])
  | OpLeft -> STerm ("OpLeft",[])
  | OpRight -> STerm ("OpRight",[])
  | OpBrand bl -> STerm ("OpBrand", dbrands_to_sexp bl)
  | OpRec s -> STerm ("OpRec", [coq_string_to_sstring s])
  | OpDot s -> STerm ("OpDot", [coq_string_to_sstring s])
  | OpRecRemove s -> STerm ("OpRecRemove", [coq_string_to_sstring s])
  | OpRecProject sl -> STerm ("OpRecProject", coq_string_list_to_sstring_list sl)
  | OpDistinct -> STerm ("OpDistinct",[])
  | OpOrderBy sl -> STerm ("OpOrderBy", coq_string_list_to_sstring_list_with_order sl)
  | OpToString -> STerm ("OpToString",[])
  | OpToText -> STerm ("OpToText",[])
  | OpLength -> STerm ("OpLength",[])
  | OpSubstring (n,None) -> STerm ("OpSubstring",[SInt n])
  | OpSubstring (n1,(Some n2)) -> STerm ("OpSubstring",[SInt n1;SInt n2])
  | OpLike (p,None) -> STerm ("OpLike",[coq_string_to_sstring p])
  | OpLike (p,(Some esc)) -> STerm ("OpLike",[coq_string_to_sstring p;coq_string_to_sstring [esc]])
  | OpCast bl -> STerm ("OpCast", dbrands_to_sexp bl)
  | OpUnbrand -> STerm ("OpUnbrand",[])
  | OpSingleton -> STerm ("OpSingleton",[])
  | OpNatUnary au -> STerm ("OpNatUnary", [nat_arith_unary_op_to_sexp au])
  | OpNatSum -> STerm ("OpNatSum",[])
  | OpNatMean -> STerm ("OpNatMean",[])
  | OpNatMin -> STerm ("OpNatMin",[])
  | OpNatMax -> STerm ("OpNatMax",[])
  | OpFloatOfNat -> STerm ("OpFloatOfNat",[])
  | OpFloatUnary au -> STerm ("OpFloatUnary", [float_arith_unary_op_to_sexp au])
  | OpFloatTruncate -> STerm ("OpFloatTruncate",[])
  | OpFloatSum -> STerm ("OpFloatSum",[])
  | OpFloatMean -> STerm ("OpFloatMean",[])
  | OpFloatBagMin -> STerm ("OpFloatBagMin",[])
  | OpFloatBagMax -> STerm ("OpFloatBagMax",[])
  | OpForeignUnary fuop -> SString (PrettyCommon.string_of_foreign_unary_op (Obj.magic fuop))
  end

let sstring_to_sql_date_component (part:sexp) : Enhanced.Data.sql_date_part =
  begin match part with
  | SString "DAY" ->   Enhanced.Data.sql_date_day
  | SString "MONTH" -> Enhanced.Data.sql_date_month
  | SString "YEAR" ->  Enhanced.Data.sql_date_year
  | _ -> raise (Qcert_Error "Not well-formed S-expr for sql date component")
  end

let sexp_to_unary_op (se:sexp) : unary_op =
  begin match se with
  | STerm ("OpIdentity",[]) -> OpIdentity
  | STerm ("OpNeg",[]) -> OpNeg
  | STerm ("OpBag",[]) -> OpBag
  | STerm ("OpCount",[]) -> OpCount
  | STerm ("OpFlatten",[]) -> OpFlatten
  | STerm ("OpLeft",[]) -> OpLeft
  | STerm ("OpRight",[]) -> OpRight
  | STerm ("OpBrand", bl) -> OpBrand (sexp_to_dbrands bl)
  | STerm ("OpRec", [se']) -> OpRec (sstring_to_coq_string se')
  | STerm ("OpDot", [se']) -> OpDot (sstring_to_coq_string se')
  | STerm ("OpRecRemove", [se']) -> OpRecRemove (sstring_to_coq_string se')
  | STerm ("OpRecProject", sl) -> OpRecProject (sstring_list_to_coq_string_list sl)
  | STerm ("OpDistinct",[]) -> OpDistinct
  | STerm ("OpOrderBy",sl) -> OpOrderBy (sstring_list_with_order_to_coq_string_list sl)
  | STerm ("OpToString",[]) -> OpToString
  | STerm ("OpToText",[]) -> OpToText
  | STerm ("OpLength",[]) -> OpLength
  | STerm ("OpSubstring",[SInt n1]) -> OpSubstring (n1,None)
  | STerm ("OpSubstring",[SInt n1;SInt n2]) -> OpSubstring (n1,Some n2)
  | STerm ("OpLike",[p]) -> OpLike (sstring_to_coq_string p,None)
  | STerm ("OpLike",[p;SString esc]) ->
     OpLike (sstring_to_coq_string p,Some (esc.[0]))
  | STerm ("OpCast", bl) -> OpCast (sexp_to_dbrands bl)
  | STerm ("OpUnbrand",[]) -> OpUnbrand
  | STerm ("OpSingleton",[]) -> OpSingleton
  | STerm ("OpNatUnary", [se']) ->
      let au = sexp_to_nat_arith_unary_op se' in
      OpNatUnary au
  | STerm ("OpNatSum",[]) -> OpNatSum
  | STerm ("OpNatMean",[]) -> OpNatMean
  | STerm ("OpNatMin",[]) -> OpNatMin
  | STerm ("OpNatMax",[]) -> OpNatMax
  | SString s -> OpForeignUnary (Obj.magic (PrettyCommon.foreign_unary_op_of_string s))
  | STerm ("OpFloatUnary", [se']) ->
      let au = sexp_to_float_arith_unary_op se' in
      OpFloatUnary au
  | STerm ("OpFloatOfNat",[]) -> OpFloatOfNat
  | STerm ("OpFloatTruncate",[]) -> OpFloatTruncate
  | STerm ("OpFloatSum",[]) -> OpFloatSum
  | STerm ("OpFloatMean",[]) -> OpFloatMean
  | STerm ("OpFloatBagMin",[]) -> OpFloatBagMin
  | STerm ("OpFloatBagMax",[]) -> OpFloatBagMax
  (* WARNING: Those are not printed, only parsed *)
  | STerm ("OpTimeToSscale",[]) -> Enhanced.Ops.Unary.coq_OpTimeToSscale
  | STerm ("OpTimeFromString",[]) -> Enhanced.Ops.Unary.coq_OpTimeFromString
  | STerm ("OpTimeDurationFromString",[]) -> Enhanced.Ops.Unary.coq_OpTimeDurationFromString
  | STerm ("OpSqlDateFromString",[]) -> Enhanced.Ops.Unary.coq_OpSqlDateFromString
  | STerm ("OpSqlDateIntervalromString",[]) -> Enhanced.Ops.Unary.coq_OpSqlDateIntervalFromString
  | STerm ("OpSqlGetDateComponent",[part]) -> Enhanced.Ops.Unary.coq_OpSqlGetDateComponent (sstring_to_sql_date_component part)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside unary_op with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside unary_op")
  end

(* CAMP Section *)

let rec camp_to_sexp (p : QLang.camp) : sexp =
  begin match p with
  | Pconst d -> STerm ("Pconst", [data_to_sexp d])
  | Punop (u, p1) -> STerm ("Punop", (unary_op_to_sexp u) :: [camp_to_sexp p1])
  | Pbinop (b, p1, p2) -> STerm ("Pbinop", (binary_op_to_sexp b) :: [camp_to_sexp p1; camp_to_sexp p2])
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
  end

let rec sexp_to_camp (se : sexp) : QLang.camp =
  begin match se with
  | STerm ("Pconst", [d]) -> Pconst (sexp_to_data d)
  | STerm ("Punop", use :: [se1]) ->
      let u = sexp_to_unary_op use in
      Punop (u, sexp_to_camp se1)
  | STerm ("Pbinop", bse :: [se1;se2]) ->
      let b = sexp_to_binary_op bse in
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
  end

(* CAMP Rule Section *)

let rec camp_rule_to_sexp (p : QLang.camp_rule) : sexp =
  begin match p with
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
  end

let rec sexp_to_camp_rule (se : sexp) : QLang.camp_rule =
  begin match se with
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
  end

(* NRA Section *)

let rec nraenv_to_sexp (op : QLang.nraenv_core) : sexp =
  begin match op with
  | CNRAEnvID -> STerm ("ANID",[])
  | CNRAEnvConst d -> STerm ("ANConst", [data_to_sexp d])
  | CNRAEnvBinop (b, op1, op2) -> STerm ("ANBinop", (binary_op_to_sexp b) :: [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvUnop (u, op1) -> STerm ("ANUnop", (unary_op_to_sexp u) :: [nraenv_to_sexp op1])
  | CNRAEnvMap (op1,op2) -> STerm ("ANMap", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvMapProduct (op1,op2) -> STerm ("ANMapProduct", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvProduct (op1,op2) -> STerm ("ANProduct", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvSelect (op1,op2) -> STerm ("ANSelect", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvDefault (op1,op2) -> STerm ("ANDefault", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvEither (op1,op2) -> STerm ("ANEither", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvEitherConcat (op1,op2) -> STerm ("ANEitherConcat", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvApp (op1,op2) -> STerm ("ANApp", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvGetConstant sl -> STerm ("ANGetConstant", [coq_string_to_sstring sl])
  | CNRAEnvEnv -> STerm ("ANEnv",[])
  | CNRAEnvAppEnv (op1,op2) -> STerm ("ANAppEnv", [nraenv_to_sexp op1;nraenv_to_sexp op2])
  | CNRAEnvMapEnv op1 -> STerm ("ANMapEnv", [nraenv_to_sexp op1])
  end

let rec sexp_to_nraenv (se : sexp) : QLang.nraenv_core =
  begin match se with
  | STerm ("ANID",[]) -> CNRAEnvID
  | STerm ("ANConst", [d]) -> CNRAEnvConst (sexp_to_data d)
  | STerm ("ANBinop", bse :: [se1;se2]) ->
      let b = sexp_to_binary_op bse in
      CNRAEnvBinop (b, sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANUnop", use :: [se1]) ->
      let u = sexp_to_unary_op use in
      CNRAEnvUnop (u, sexp_to_nraenv se1)
  | STerm ("ANMap", [se1;se2]) -> CNRAEnvMap (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANMapProduct", [se1;se2]) -> CNRAEnvMapProduct (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANProduct", [se1;se2]) -> CNRAEnvProduct (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANSelect", [se1;se2]) -> CNRAEnvSelect (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANDefault", [se1;se2]) -> CNRAEnvDefault (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANEither", [se1;se2]) -> CNRAEnvEither (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANEitherConcat", [se1;se2]) -> CNRAEnvEitherConcat (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANApp", [se1;se2]) -> CNRAEnvApp (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANGetConstant", [sl]) -> CNRAEnvGetConstant (sstring_to_coq_string sl)
  | STerm ("ANEnv",[]) -> CNRAEnvEnv
  | STerm ("ANAppEnv", [se1;se2]) -> CNRAEnvAppEnv (sexp_to_nraenv se1, sexp_to_nraenv se2)
  | STerm ("ANMapEnv", [se1]) -> CNRAEnvMapEnv (sexp_to_nraenv se1)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside NRAEnv with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside NRAEnv")
  end

(* NNRC Section *)

let rec nnrc_to_sexp (n : QLang.nnrc) : sexp =
  begin match n with
  | NNRCGetConstant v -> STerm ("NNRCGetConstant", [SString (string_of_char_list v)])
  | NNRCVar v -> STerm ("NNRCVar", [SString (string_of_char_list v)])
  | NNRCConst d -> STerm ("NNRCConst", [data_to_sexp d])
  | NNRCBinop (b, n1, n2) -> STerm ("NNRCBinop", (binary_op_to_sexp b) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NNRCUnop (u, n1) -> STerm ("NNRCUnop", (unary_op_to_sexp u) :: [nnrc_to_sexp n1])
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
  end

let rec sexp_to_nnrc (se:sexp) : QLang.nnrc =
  begin match se with
  | STerm ("NNRCGetConstant", [SString v]) -> NNRCGetConstant (char_list_of_string v)
  | STerm ("NNRCVar", [SString v]) -> NNRCVar (char_list_of_string v)
  | STerm ("NNRCConst", [d]) -> NNRCConst (sexp_to_data d)
  | STerm ("NNRCBinop", b :: [n1;n2]) -> NNRCBinop (sexp_to_binary_op b, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("NNRCUnop", u :: [n1]) -> NNRCUnop (sexp_to_unary_op u, sexp_to_nnrc n1)
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
  end

(* NNRS Section *)

let rec nnrs_expr_to_sexp e : sexp =
  match e with
  | NNRSGetConstant v -> STerm ("NNRSGetConstant", [SString (string_of_char_list v)])
  | NNRSVar v -> STerm ("NNRSVar", [SString (string_of_char_list v)])
  | NNRSConst d -> STerm ("NNRSConst", [data_to_sexp d])
  | NNRSBinop (b, n1, n2) -> STerm ("NNRSBinop", (binary_op_to_sexp b) :: [nnrs_expr_to_sexp n1;nnrs_expr_to_sexp n2])
  | NNRSUnop (u, n1) -> STerm ("NNRSUnop", (unary_op_to_sexp u) :: [nnrs_expr_to_sexp n1])
  | NNRSGroupBy (g,sl,n1) -> STerm ("NNRSGroupBy",
                                 (SString (string_of_char_list g))
                                 :: (STerm ("keys",coq_string_list_to_sstring_list sl))
                                 :: [nnrs_expr_to_sexp n1])

let rec nnrs_stmt_to_sexp s : sexp =
  match s with
  | NNRSSeq (s1, s2) ->
    STerm ("NNRSSeq", [ nnrs_stmt_to_sexp s1; nnrs_stmt_to_sexp s2])
  | NNRSLet (v, e, s) -> STerm ("NNRSLet", [SString (string_of_char_list v); nnrs_expr_to_sexp e; nnrs_stmt_to_sexp s])
  | NNRSLetMut (v, s1, s2) -> STerm ("NNRSLetMut", [SString (string_of_char_list v); nnrs_stmt_to_sexp s1; nnrs_stmt_to_sexp s2])
  | NNRSLetMutColl (v, s1, s2) -> STerm ("NNRSLetMutColl", [SString (string_of_char_list v); nnrs_stmt_to_sexp s1; nnrs_stmt_to_sexp s2])
  | NNRSAssign (v, e) -> STerm ("NNRSAssign", [SString (string_of_char_list v); nnrs_expr_to_sexp e])
  | NNRSPush (v, e) -> STerm ("NNRSPush", [SString (string_of_char_list v); nnrs_expr_to_sexp e])
  | NNRSFor (v, e, s) -> STerm ("NNRSFor", [SString (string_of_char_list v); nnrs_expr_to_sexp e; nnrs_stmt_to_sexp s])
  | NNRSIf (e, s1, s2) -> STerm ("NNRSIf", [nnrs_expr_to_sexp e; nnrs_stmt_to_sexp s1; nnrs_stmt_to_sexp s2])
  | NNRSEither (e,v1,s1,v2,s2) -> STerm ("NNRSEither",
                                      (SString (string_of_char_list v1))
                                   :: (SString (string_of_char_list v2))
                                   :: [nnrs_expr_to_sexp e;nnrs_stmt_to_sexp s1;nnrs_stmt_to_sexp s2])

let nnrs_to_sexp ((n, ret) : QLang.nnrs) : sexp =
  STerm ("NNRS", [nnrs_stmt_to_sexp n; SString (string_of_char_list ret)])


let rec sexp_to_nnrs_expr (se:sexp) =
  match se with
  | STerm ("NNRSGetConstant", [SString v]) -> NNRSGetConstant (char_list_of_string v)
  | STerm ("NNRSVar", [SString v]) -> NNRSVar (char_list_of_string v)
  | STerm ("NNRSConst", [d]) -> NNRSConst (sexp_to_data d)
  | STerm ("NNRSBinop", b :: [n1;n2]) -> NNRSBinop (sexp_to_binary_op b, sexp_to_nnrs_expr n1, sexp_to_nnrs_expr n2)
  | STerm ("NNRSUnop", u :: [n1]) -> NNRSUnop (sexp_to_unary_op u, sexp_to_nnrs_expr n1)
  | STerm ("NNRSGroupBy", (SString v1) :: (STerm ("keys", v2)) :: [n1]) ->
      NNRSGroupBy (char_list_of_string v1,sstring_list_to_coq_string_list v2,sexp_to_nnrs_expr n1)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside nnrs_expr with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nnrc_expr")

let rec sexp_to_nnrs_stmt (se:sexp) =
  match se with
  | STerm ("NNRSSeq", [s1; s2]) -> NNRSSeq (sexp_to_nnrs_stmt s1, sexp_to_nnrs_stmt s1)
  | STerm ("NNRSLet", [SString v; e; s]) -> NNRSLet (char_list_of_string v, (sexp_to_nnrs_expr e), sexp_to_nnrs_stmt s)
  | STerm ("NNRSLetMut", [SString v; s1; s2]) -> NNRSLetMut (char_list_of_string v, sexp_to_nnrs_stmt s1, sexp_to_nnrs_stmt s2)
  | STerm ("NNRSLetMutColl", [SString v; s1; s2]) -> NNRSLetMutColl (char_list_of_string v, sexp_to_nnrs_stmt s1, sexp_to_nnrs_stmt s2)
  | STerm ("NNRSAssign", [SString v; e]) -> NNRSAssign (char_list_of_string v, sexp_to_nnrs_expr e)
  | STerm ("NNRSPush", [SString v; e]) -> NNRSPush (char_list_of_string v, sexp_to_nnrs_expr e)
  | STerm ("NNRSFor", [SString v; e; s]) -> NNRSFor (char_list_of_string v, sexp_to_nnrs_expr e, sexp_to_nnrs_stmt s)
  | STerm ("NNRSIf", [e; s1; s2]) -> NNRSIf (sexp_to_nnrs_expr e, sexp_to_nnrs_stmt s1, sexp_to_nnrs_stmt s2)
  | STerm ("NNRSEither", (SString v1) :: (SString v2) :: [e;s1;s2]) ->
      NNRSEither (sexp_to_nnrs_expr e,char_list_of_string v1,sexp_to_nnrs_stmt s1,char_list_of_string v2,sexp_to_nnrs_stmt s2)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside nnrs_stmt with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nnrc_stmt")

let sexp_to_nnrs (se:sexp) : QLang.nnrs =
  match se with
  | STerm ("NNRS", [s; SString ret]) ->
    (sexp_to_nnrs_stmt s, char_list_of_string ret)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nnrs")

(* NNRSimp Section *)

let rec nnrs_imp_expr_to_sexp e : sexp =
  match e with
  | NNRSimpGetConstant v -> STerm ("NNRSimpGetConstant", [SString (string_of_char_list v)])
  | NNRSimpVar v -> STerm ("NNRSimpVar", [SString (string_of_char_list v)])
  | NNRSimpConst d -> STerm ("NNRSimpConst", [data_to_sexp d])
  | NNRSimpBinop (b, n1, n2) -> STerm ("NNRSimpBinop", (binary_op_to_sexp b) :: [nnrs_imp_expr_to_sexp n1;nnrs_imp_expr_to_sexp n2])
  | NNRSimpUnop (u, n1) -> STerm ("NNRSimpUnop", (unary_op_to_sexp u) :: [nnrs_imp_expr_to_sexp n1])
  | NNRSimpGroupBy (g,sl,n1) -> STerm ("NNRSimpGroupBy",
                                 (SString (string_of_char_list g))
                                 :: (STerm ("keys",coq_string_list_to_sstring_list sl))
                                 :: [nnrs_imp_expr_to_sexp n1])

let rec nnrs_imp_stmt_to_sexp s : sexp =
  match s with
  | NNRSimpSkip  ->
    STerm ("NNRSimpSkip", [])
  | NNRSimpSeq (s1, s2) ->
    STerm ("NNRSimpSeq", [ nnrs_imp_stmt_to_sexp s1; nnrs_imp_stmt_to_sexp s2])
  | NNRSimpLet (v, None, s) -> STerm ("NNRSimpLet", [SString (string_of_char_list v); nnrs_imp_stmt_to_sexp s])
  | NNRSimpLet (v, Some e, s) -> STerm ("NNRSimpLet", [SString (string_of_char_list v); nnrs_imp_expr_to_sexp e; nnrs_imp_stmt_to_sexp s])
  | NNRSimpAssign (v, e) -> STerm ("NNRSimpAssign", [SString (string_of_char_list v); nnrs_imp_expr_to_sexp e])
  | NNRSimpFor (v, e, s) -> STerm ("NNRSimpFor", [SString (string_of_char_list v); nnrs_imp_expr_to_sexp e; nnrs_imp_stmt_to_sexp s])
  | NNRSimpIf (e, s1, s2) -> STerm ("NNRSimpIf", [nnrs_imp_expr_to_sexp e; nnrs_imp_stmt_to_sexp s1; nnrs_imp_stmt_to_sexp s2])
  | NNRSimpEither (e,v1,s1,v2,s2) -> STerm ("NNRSimpEither",
                                      (SString (string_of_char_list v1))
                                   :: (SString (string_of_char_list v2))
                                   :: [nnrs_imp_expr_to_sexp e;nnrs_imp_stmt_to_sexp s1;nnrs_imp_stmt_to_sexp s2])

let nnrs_imp_to_sexp ((n, ret) : QLang.nnrs_imp) : sexp =
  STerm ("NNRSimp", [nnrs_imp_stmt_to_sexp n; SString (string_of_char_list ret)])


let rec sexp_to_nnrs_imp_expr (se:sexp) =
  match se with
  | STerm ("NNRSimpGetConstant", [SString v]) -> NNRSimpGetConstant (char_list_of_string v)
  | STerm ("NNRSimpVar", [SString v]) -> NNRSimpVar (char_list_of_string v)
  | STerm ("NNRSimpConst", [d]) -> NNRSimpConst (sexp_to_data d)
  | STerm ("NNRSimpBinop", b :: [n1;n2]) -> NNRSimpBinop (sexp_to_binary_op b, sexp_to_nnrs_imp_expr n1, sexp_to_nnrs_imp_expr n2)
  | STerm ("NNRSimpUnop", u :: [n1]) -> NNRSimpUnop (sexp_to_unary_op u, sexp_to_nnrs_imp_expr n1)
  | STerm ("NNRSimpGroupBy", (SString v1) :: (STerm ("keys", v2)) :: [n1]) ->
      NNRSimpGroupBy (char_list_of_string v1,sstring_list_to_coq_string_list v2,sexp_to_nnrs_imp_expr n1)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside nnrs_imp_expr with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nnrc_expr")

let rec sexp_to_nnrs_imp_stmt (se:sexp) =
  match se with
  | STerm ("NNRSimpSkip", []) -> NNRSimpSkip
  | STerm ("NNRSimpSeq", [s1; s2]) -> NNRSimpSeq (sexp_to_nnrs_imp_stmt s1, sexp_to_nnrs_imp_stmt s1)
  | STerm ("NNRSimpLet", [SString v; s]) -> NNRSimpLet (char_list_of_string v, None, sexp_to_nnrs_imp_stmt s)
  | STerm ("NNRSimpLet", [SString v; e; s]) -> NNRSimpLet (char_list_of_string v, Some (sexp_to_nnrs_imp_expr e), sexp_to_nnrs_imp_stmt s)
  | STerm ("NNRSimpAssign", [SString v; e]) -> NNRSimpAssign (char_list_of_string v, sexp_to_nnrs_imp_expr e)
  | STerm ("NNRSimpFor", [SString v; e; s]) -> NNRSimpFor (char_list_of_string v, sexp_to_nnrs_imp_expr e, sexp_to_nnrs_imp_stmt s)
  | STerm ("NNRSimpIf", [e; s1; s2]) -> NNRSimpIf (sexp_to_nnrs_imp_expr e, sexp_to_nnrs_imp_stmt s1, sexp_to_nnrs_imp_stmt s2)
  | STerm ("NNRSimpEither", (SString v1) :: (SString v2) :: [e;s1;s2]) ->
      NNRSimpEither (sexp_to_nnrs_imp_expr e,char_list_of_string v1,sexp_to_nnrs_imp_stmt s1,char_list_of_string v2,sexp_to_nnrs_imp_stmt s2)
  | STerm (t, _) ->
      raise (Qcert_Error ("Not well-formed S-expr inside nnrs_imp_stmt with name " ^ t))
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nnrc_stmt")

let sexp_to_nnrs_imp (se:sexp) : QLang.nnrs_imp =
  match se with
  | STerm ("NNRSimp", [s; SString ret]) ->
    (sexp_to_nnrs_imp_stmt s, char_list_of_string ret)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside nnrs_imp")

(* Imp Section *)

let imp_expr_to_sexp data_to_sexp op_to_sexp runtime_op_to_sexp e : sexp =
  let rec imp_expr_to_sexp e : sexp =
    match e with
    | ImpExprVar v -> STerm ("ImpExprVar", [SString (string_of_char_list v)])
    | ImpExprConst d -> STerm ("ImpExprConst", [data_to_sexp d])
    | ImpExprOp (op, args) -> STerm ("ImpExprOp", (op_to_sexp op) :: List.map imp_expr_to_sexp args)
    | ImpExprRuntimeCall (op, args) -> STerm ("ImpExprRuntimeCall", (runtime_op_to_sexp op) :: List.map imp_expr_to_sexp args)
  in
  imp_expr_to_sexp e

let imp_stmt_to_sexp data_to_sexp op_to_sexp runtime_op_to_sexp s : sexp =
  let imp_expr_to_sexp e = imp_expr_to_sexp data_to_sexp op_to_sexp runtime_op_to_sexp e in
  let rec imp_stmt_to_sexp s : sexp =
    match s with
    | ImpStmtAssign (v, e) -> STerm ("ImpStmtAssign", [SString (string_of_char_list v); imp_expr_to_sexp e])
    | ImpStmtFor (v, e, s) -> STerm ("ImpStmtFor", [SString (string_of_char_list v); imp_expr_to_sexp e; imp_stmt_to_sexp s])
    | ImpStmtForRange (v, e1, e2, s) -> STerm ("ImpStmtForRange", [SString (string_of_char_list v); imp_expr_to_sexp e1; imp_expr_to_sexp e2; imp_stmt_to_sexp s])
    | ImpStmtIf (e, s1, s2) -> STerm ("ImpStmtIf", [imp_expr_to_sexp e; imp_stmt_to_sexp s1; imp_stmt_to_sexp s2])
  in
  imp_stmt_to_sexp s

let imp_function_to_sexp data_to_sexp op_to_sexp runtime_op_to_sexp (ImpFun(var, s, ret)) : sexp =
  STerm ("ImpFun", [STerm ("ImpFunArgs", [SString (string_of_char_list var)]);
                    imp_stmt_to_sexp data_to_sexp op_to_sexp runtime_op_to_sexp s;
                    STerm ("ImpFunReturn", [SString (string_of_char_list ret)])])

let rec imp_to_sexp data_to_sexp op_to_sexp runtime_op_to_sexp ((* ImpLib *) l) : sexp =
  STerm
    ("ImpLib",
     List.map
       (fun (f, def) ->
          STerm ("ImpDef", [SString (string_of_char_list f);
                            imp_function_to_sexp data_to_sexp op_to_sexp runtime_op_to_sexp def ]))
       l)

let sexp_to_imp sexp_to_data sexp_to_op sexp_to_runtime_op (se:sexp) =
  assert false (* XXX TODO XXX *)


(* ImpQcert Section *)

let sexp_to_imp_qcert_data d =
  assert false (* XXX TODO XXX *)

let sexp_to_imp_qcert_op op =
  assert false (* XXX TODO XXX *)

let sexp_to_imp_qcert_runtime_op op =
  assert false (* XXX TODO XXX *)

let rec imp_qcert_to_sexp q : sexp =
  imp_to_sexp sexp_to_imp_qcert_data sexp_to_imp_qcert_op sexp_to_imp_qcert_runtime_op q

let sexp_to_imp_qcert (se:sexp) =
  sexp_to_imp sexp_to_imp_qcert_data sexp_to_imp_qcert_op sexp_to_imp_qcert_runtime_op se

(* ImpJson Section *)

let sexp_to_imp_json_data d =
  assert false (* XXX TODO XXX *)

let sexp_to_imp_json_op op =
  assert false (* XXX TODO XXX *)

let sexp_to_imp_json_runtime_op op =
  assert false (* XXX TODO XXX *)

let rec imp_json_to_sexp q : sexp =
  imp_to_sexp sexp_to_imp_json_data sexp_to_imp_json_op sexp_to_imp_json_runtime_op q

let sexp_to_imp_json (se:sexp) =
  sexp_to_imp sexp_to_imp_json_data sexp_to_imp_json_op sexp_to_imp_json_runtime_op se


(* NNRCMR section *)

let var_to_sexp (v:var) : sexp =
  SString (string_of_char_list v)

let opt_var_to_sexp (vo:var option) : sexp list =
  begin match vo with
  | None -> []
  | Some v -> [var_to_sexp v]
  end
    
let sexp_to_var (se:sexp) : var =
  begin match se with
  | SString v -> char_list_of_string v
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside var")
  end

let sexp_to_var_opt (sel:sexp list) : var option =
  begin match sel with
  | [] -> None
  | [se] -> Some (sexp_to_var se)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside optional var")
  end

let var_list_to_sexp (vl:var list) : sexp list =
  map (fun v -> (SString (string_of_char_list v))) vl

let sexp_to_var_list (sel:sexp list) =
  List.map sexp_to_var sel

let params_to_sexp (vl:var list) : sexp =
  STerm ("params", var_list_to_sexp vl)

let sexp_to_params (se:sexp) =
  begin match se with
  | STerm ("params", vars) -> sexp_to_var_list vars
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside var list")
  end

let fun_to_sexp (f:(var list * QLang.nnrc)) : sexp =
  STerm ("lambda", (params_to_sexp (fst f)) :: (nnrc_to_sexp (snd f)) :: [])

let sexp_to_fun (se:sexp) : (var list * QLang.nnrc) =
  begin match se with
  | STerm ("lambda", params :: sen :: []) ->
      (sexp_to_params params, sexp_to_nnrc sen)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside lambda")
  end

let unary_fun_to_sexp (f:var * QLang.nnrc) : sexp =
  fun_to_sexp ([fst f], snd f)

let sexp_to_unary_fun (se:sexp) : var * QLang.nnrc =
  begin match sexp_to_fun se with
  | ([var], n) -> (var, n)
  | _ ->
      raise (Qcert_Error "Map or Reduce lambda isn't unary")
  end
  
let binary_fun_to_sexp (f:(var * var) * QLang.nnrc) : sexp =
  fun_to_sexp ([fst (fst f); (snd (fst f))], snd f)

let sexp_to_binary_fun (se:sexp) : (var * var) * QLang.nnrc =
  begin match sexp_to_fun se with
  | ([var1; var2], n) -> ((var1, var2), n)
  | _ ->
      raise (Qcert_Error "Map or Reduce lambda isn't binary")
  end  

let map_fun_to_sexp (mf:map_fun) =
  begin match mf with
  | MapDist f -> STerm ("MapDist", (unary_fun_to_sexp f)::[])
  | MapDistFlatten f -> STerm ("MapDistFlatten", (unary_fun_to_sexp f)::[])
  | MapScalar f -> STerm ("MapScalar", (unary_fun_to_sexp f)::[])
  end

let sexp_to_map_fun (se:sexp) =
  begin match se with
  | STerm ("MapDist", sef::[]) -> MapDist (sexp_to_unary_fun sef)
  | STerm ("MapDistFlatten", sef::[]) -> MapDistFlatten (sexp_to_unary_fun sef)
  | STerm ("MapScalar", sef::[]) -> MapScalar (sexp_to_unary_fun sef)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside map_fun")
  end

let numeric_type_to_sexp nt =
  begin match nt with
  | Enhanced_numeric_int -> SString "Enhanced_numeric_int"
  | Enhanced_numeric_float -> SString "Enhanced_numeric_float"
  end

let sexp_to_numeric_type se =
  begin match se with
  | SString "Enhanced_numeric_int" -> Enhanced_numeric_int
  | SString "Enhanced_numeric_float" -> Enhanced_numeric_float
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside numeric_type")
  end


let reduce_op_to_sexp se =
  begin match se with
  | RedOpCount -> STerm ("RedOpCount",[])
  | RedOpSum nt -> STerm ("RedOpSum", (numeric_type_to_sexp nt)::[])
  | RedOpMin nt -> STerm ("RedOpMin", (numeric_type_to_sexp nt)::[])
  | RedOpMax nt -> STerm ("RedOpMax", (numeric_type_to_sexp nt)::[])
  | RedOpArithMean nt -> STerm ("RedOpArithMean", (numeric_type_to_sexp nt)::[])
  | RedOpStats nt -> STerm ("RedOpStats", (numeric_type_to_sexp nt)::[])
  end

let sexp_to_reduce_op se =
  begin match se with
  | STerm ("RedOpCount",[]) -> RedOpCount
  | STerm ("RedOpSum", nt::[]) -> RedOpSum (sexp_to_numeric_type nt)
  | STerm ("RedOpMin", nt::[]) -> RedOpMin (sexp_to_numeric_type nt)
  | STerm ("RedOpMax", nt::[]) -> RedOpMax (sexp_to_numeric_type nt)
  | STerm ("RedOpArithMean", nt::[]) -> RedOpArithMean (sexp_to_numeric_type nt)
  | STerm ("RedOpStats", nt::[]) -> RedOpStats (sexp_to_numeric_type nt)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside reduce_op")
  end


let reduce_fun_to_sexp (rf:reduce_fun) =
  begin match rf with
  | RedId -> STerm ("RedId", [])
  | RedCollect f -> STerm ("RedCollect", (unary_fun_to_sexp f)::[])
  | RedOp ro -> STerm ("foreign_reduce_op", (reduce_op_to_sexp (Obj.magic ro))::[])
  | RedSingleton -> STerm ("RedSingleton", [])
  end

let sexp_to_reduce_fun (se:sexp) =
  begin match se with
  | STerm ("RedId", []) -> RedId
  | STerm ("RedCollect", f::[]) -> RedCollect (sexp_to_unary_fun f)
  | STerm ("foreign_reduce_op", ro::[]) -> RedOp (Obj.magic (sexp_to_reduce_op ro))
  | STerm ("RedSingleton", []) -> RedSingleton
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside reduce_fun")
  end

let mr_to_sexp (mr:mr) : sexp =
  STerm ("mr",
	 (STerm ("mr_input", (SString (string_of_char_list mr.mr_input))::[]))
	 :: (STerm ("mr_output", (SString (string_of_char_list mr.mr_output))::[]))
	 :: (map_fun_to_sexp mr.mr_map)
	 :: (reduce_fun_to_sexp mr.mr_reduce)
	 :: [])

let sexp_to_mr (se:sexp) : mr =
  begin match se with
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
  end

let mr_chain_to_sexp (mrl:mr list) : sexp list =
  List.map mr_to_sexp mrl

let sexp_to_mr_chain (sel:sexp list) : mr list =
  List.map sexp_to_mr sel


let loc_to_sexp l =
  begin match l with
  | Vlocal -> SString "Vscalar"
  | Vdistr -> SString "Vdistributed"
  end

let sexp_to_loc (se:sexp) =
  begin match se with
  | SString "Vscalar" -> Vlocal
  | SString "Vdistributed" -> Vdistr
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside dlocalization")
  end

let var_loc_to_sexp (v,l) =
  STerm ("var_loc", (SString (string_of_char_list v))::(loc_to_sexp l)::[])
    
let sexp_to_var_loc (se:sexp) =
  begin match se with
  | STerm ("var_loc", (SString v)::l::[]) ->
      (char_list_of_string v, sexp_to_loc l)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside var-dlocalization pair")
  end
    
let var_locs_to_sexp env : sexp list =
  map var_loc_to_sexp env

let sexp_to_var_locs (se:sexp list) =
  map sexp_to_var_loc se


let mr_last_to_sexp (last: (var list * QLang.nnrc) * (var * dlocalization) list) =
  begin match last with
  | (f, var_locs)
    ->
      (STerm ("mr_last",
	      (fun_to_sexp f) :: (var_locs_to_sexp var_locs)))
  end

let sexp_to_mr_last (se:sexp) : (var list * QLang.nnrc) * (var * dlocalization) list =
  begin match se with
  | STerm ("mr_last", f :: var_locs) ->
      (sexp_to_fun f, sexp_to_var_locs var_locs)
  | _ ->
      raise (Qcert_Error "Not well-formed S-expr inside mr_last")
  end

let nnrcmr_to_sexp (n:QLang.nnrcmr) : sexp =
  STerm ("nrcmr",
	 (STerm ("mr_env", var_locs_to_sexp n.mr_inputs_loc))
	 :: (STerm ("mr_chain", mr_chain_to_sexp (n.mr_chain)))
	 :: (mr_last_to_sexp n.mr_last)
	 :: [])

let sexp_to_nnrcmr (se:sexp) : QLang.nnrcmr =
  begin match se with
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
  end

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
      QSQL.sql_expr_const (Dfloat f)
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
      (Dfloat f) :: (sexp_to_sql_const_list const_list')
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
  | SPSelectStmt (lets, block, unions, SPOrderBy orderby) ->
      STerm("Select", STerm("Lets", List.map sqlpp_let_to_sexp lets) :: 
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
  | SPSelectBlock (select, froms, lets1, where, groupby, lets2, having) ->
      STerm("SelectBlock", [(sqlpp_select_clause_to_sexp select);
			    STerm("Froms", (List.map sqlpp_from_to_sexp froms)); STerm("Lets", (List.map sqlpp_let_to_sexp lets1)); 
			    (sqlpp_where_to_sexp where); (sqlpp_group_to_sexp groupby);
			    STerm("Lets", (List.map sqlpp_let_to_sexp lets2)); (sqlpp_having_to_sexp having)]) 
  end

and sqlpp_select_clause_to_sexp (clause : sqlpp_select) : sexp =
  begin match clause with
  | SPSelectSQL (distinct, projections) ->
      STerm("SelectSQL", sqlpp_distinct_to_sexp distinct::(List.map sqlpp_project_to_sexp projections))
  | SPSelectValue (distinct, expr) ->
      STerm("SelectValue", [sqlpp_distinct_to_sexp distinct; sqlpp_expr_to_sexp expr])
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
  | SPFrom (expr, Some name, joins) ->
      STerm("From", sqlpp_expr_to_sexp expr :: STerm("as", [coq_string_to_sstring name]) ::
	    (List.map sqlpp_join_clause_to_sexp joins))
  | SPFrom (expr, None, joins) ->  STerm("From", sqlpp_expr_to_sexp expr :: (List.map sqlpp_join_clause_to_sexp joins))
  end

and sqlpp_join_clause_to_sexp (clause : sqlpp_join_clause) : sexp =
  begin match clause with
  | SPJoin (jtype, expr1, Some var, expr2) ->
      STerm("Join", [sqlpp_join_type_to_sexp jtype; STerm("as", [coq_string_to_sstring var]); 
		     sqlpp_expr_to_sexp expr1; sqlpp_expr_to_sexp expr2])
  | SPJoin (jtype, expr1, None, expr2) ->
      STerm("Join", [sqlpp_join_type_to_sexp jtype; sqlpp_expr_to_sexp expr1; 
		     sqlpp_expr_to_sexp expr2])
  | SPUnnest (jtype, expr, Some var, Some positionVar) ->
      STerm("Unnest", [sqlpp_join_type_to_sexp jtype; 
		       STerm("as", [coq_string_to_sstring var]); STerm("at", [coq_string_to_sstring positionVar]); sqlpp_expr_to_sexp expr])
  | SPUnnest (jtype, expr, Some var, None) ->
      STerm("Unnest", [sqlpp_join_type_to_sexp jtype; 
		       STerm("as", [coq_string_to_sstring var]); sqlpp_expr_to_sexp expr])
  | SPUnnest (jtype, expr, None, Some positionVar) ->
      STerm("Unnest", [sqlpp_join_type_to_sexp jtype; 
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
  | SPGroupBy (keys, Some aspart) ->
      STerm("GroupBy", [STerm("Keys", List.map sqlpp_group_key_to_sexp keys); sqlpp_group_as_to_sexp aspart])
  | SPGroupBy (keys, None) ->
      STerm("GroupBy", [STerm("Keys", List.map sqlpp_group_key_to_sexp keys)])
  | SPNoGroupBy ->
      STerm("GroupBy", [])
  end
	
and sqlpp_group_as_to_sexp (aspart : (char list * ((char list * char list) list)))	: sexp =
  begin match aspart with
  | (name , renames) ->
      STerm("GroupAs", coq_string_to_sstring name :: (List.map sqlpp_rename_to_sexp renames))
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
  | _ ->
      raise (Qcert_Error ("Not well-formed S-expr inside SQL++ function call expression"))
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
      QSQLPP.sqlpp_sqlpp_literal (Dfloat f)
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
  | L_nnrs_core -> Q_nnrs_core (sexp_to_nnrs se)
  | L_nnrs -> Q_nnrs (sexp_to_nnrs se)
  | L_nnrs_imp -> Q_nnrs_imp (sexp_to_nnrs_imp se)
  | L_imp_qcert -> Q_nnrs_imp (sexp_to_imp_qcert se)
  | L_imp_json -> Q_nnrs_imp (sexp_to_imp_json se)
  | L_nnrcmr -> Q_nnrcmr (sexp_to_nnrcmr se)
  | L_dnnrc ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_dnnrc_typed ->
      raise (Qcert_Error ("sexp to "^(QcertUtil.name_of_language lang)^" not yet implemented")) (* XXX TODO XXX *)
  | L_js_ast
  | L_javascript
  | L_java
  | L_spark_rdd
  | L_spark_df ->
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
  | Q_nnrs_core q -> nnrs_to_sexp q
  | Q_nnrs q -> nnrs_to_sexp q
  | Q_nnrs_imp q -> nnrs_imp_to_sexp q
  | Q_imp_qcert q -> imp_qcert_to_sexp q
  | Q_imp_json q -> imp_json_to_sexp q
  | Q_nnrcmr q -> nnrcmr_to_sexp q
  | Q_dnnrc _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_dnnrc_typed _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_js_ast _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_javascript _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_java _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_spark_rdd _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_spark_df _ ->
      SString ((QcertUtil.name_of_query q)^" to sexp not yet implemented") (* XXX TODO XXX *)
  | Q_error err ->
      SString ("query_to_sexp: "^(Util.string_of_char_list err))
  end
