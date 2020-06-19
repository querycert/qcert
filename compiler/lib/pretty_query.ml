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
open Core.EnhancedCompiler

open Pretty_common

(** Pretty query wrapper *)

type 'a pretty_fun = bool -> int -> bool -> QData.json -> bool -> 'a -> string
	  
let pretty_query pconf (pretty_q:'a pretty_fun) (q:'a) =
  let greek = get_charset_bool pconf in
  let margin = get_margin pconf in
  let annot = get_type_annotations pconf in
  let inheritance = get_inheritance pconf in
  let link_runtime = link_js_runtime pconf in
  pretty_q greek margin annot inheritance link_runtime q

(** Pretty CAMPRule *)

let pretty_camp_rule greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for CAMPRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty TechRule *)

let pretty_tech_rule greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for TechRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty DesignerRule *)

let pretty_designer_rule greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for TechRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty CAMP *)

let pretty_camp greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for CAMP at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty OQL *)

let pretty_oql greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for OQL at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty SQL *)

let pretty_sql greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for SQL at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty SQL++ *)

let pretty_sqlpp greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for SQL++ at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty LambdaNRA *)

let pretty_lambda_nra greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for LambdaNRA at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty NRA *)

let rec pretty_nra_aux p sym ff a =
  begin match a with
  | Core.NRAID -> fprintf ff "%s" "ID"
  | Core.NRAConst d -> fprintf ff "%a" pretty_data d
  | Core.NRABinop (b,a1,a2) -> (pretty_binary_op p sym pretty_nra_aux) ff b a1 a2
  | Core.NRAUnop (u,a1) -> (pretty_unary_op p sym pretty_nra_aux) ff u a1
  | Core.NRAMap (a1,a2) -> pretty_nra_exp p sym sym.chi ff a1 (Some a2)
  | Core.NRAMapProduct (a1,a2) -> pretty_nra_exp p sym sym.djoin ff a1 (Some a2)
  | Core.NRAProduct (a1,a2) -> pretty_infix_exp p 5 sym pretty_nra_aux sym.times ff a1 a2
  | Core.NRASelect (a1,a2) -> pretty_nra_exp p sym sym.sigma ff a1 (Some a2)
  | Core.NRADefault (a1,a2) -> pretty_infix_exp p 8 sym pretty_nra_aux sym.bars ff a1 a2
  | Core.NRAEither (a1,a2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ ID@;<1 -2>with@]@;<1 0>@[<hv 2>| left as ID ->@ %a@]@;<1 0>@[<hv 2>| right as ID ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      (pretty_nra_aux p sym) a1
	      (pretty_nra_aux p sym) a2
  | Core.NRAEitherConcat (a1,a2) -> pretty_infix_exp p 7 sym pretty_nra_aux sym.sqlrarrow ff a1 a2
  | Core.NRAApp (a1,a2) -> pretty_infix_exp p 9 sym pretty_nra_aux sym.circ ff a1 a2
  | Core.NRAGetConstant s -> fprintf ff "Table%a%s%a" pretty_sym sym.lfloor (string_of_char_list s) pretty_sym sym.rfloor
  end
    
(* resets precedence back to 0 *)
and pretty_nra_exp p sym thissym ff a1 oa2 =
  begin match oa2 with
  | None ->
      if p > 22
      then
	      fprintf ff "@[<hv 1>(%a%a%a%a())@]" pretty_sym thissym pretty_sym sym.langle (pretty_nra_aux 0 sym) a1 pretty_sym sym.rangle
      else
	      fprintf ff "@[<hv 0>%a%a%a%a()@]" pretty_sym thissym pretty_sym sym.langle (pretty_nra_aux 0 sym) a1 pretty_sym sym.rangle
  | Some a2 ->
      if p > 22
      then
	      fprintf ff "@[<hv 3>(%a%a%a%a(@,%a@;<0 -2>))@]" pretty_sym thissym pretty_sym sym.langle (pretty_nra_aux 0 sym) a1 pretty_sym sym.rangle (pretty_nra_aux 0 sym) a2
      else
	      fprintf ff "@[<hv 2>%a%a%a%a(@,%a@;<0 -2>)@]" pretty_sym thissym pretty_sym sym.langle (pretty_nra_aux 0 sym) a1 pretty_sym sym.rangle (pretty_nra_aux 0 sym) a2
  end

let pretty_nra greek margin annot inheritance link_runtime q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nra_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty NRAEnv *)

let rec pretty_nraenv_aux p sym ff a =
  begin match a with
  | Core.NRAEnvID -> fprintf ff "%s" "ID"
  | Core.NRAEnvConst d -> fprintf ff "%a" pretty_data d
  | Core.NRAEnvBinop (b,a1,a2) -> (pretty_binary_op p sym pretty_nraenv_aux) ff b a1 a2
  | Core.NRAEnvUnop (u,a1) -> (pretty_unary_op p sym pretty_nraenv_aux) ff u a1
  | Core.NRAEnvMap (a1,a2) -> pretty_nraenv_exp p sym sym.chi ff a1 (Some a2)
  | Core.NRAEnvMapProduct (a1,a2) -> pretty_nraenv_exp p sym sym.djoin ff a1 (Some a2)
  | Core.NRAEnvProduct (a1,a2) -> pretty_infix_exp p 5 sym pretty_nraenv_aux sym.times ff a1 a2
  | Core.NRAEnvSelect (a1,a2) -> pretty_nraenv_exp p sym sym.sigma ff a1 (Some a2)
  | Core.NRAEnvDefault (a1,a2) -> pretty_infix_exp p 8 sym pretty_nraenv_aux sym.bars ff a1 a2
  | Core.NRAEnvEither (a1,a2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ ID@;<1 -2>with@]@;<1 0>@[<hv 2>| left as ID ->@ %a@]@;<1 0>@[<hv 2>| right as ID ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      (pretty_nraenv_aux p sym) a1
	      (pretty_nraenv_aux p sym) a2
  | Core.NRAEnvEitherConcat (a1,a2) -> pretty_infix_exp p 7 sym pretty_nraenv_aux sym.sqlrarrow ff a1 a2
  | Core.NRAEnvApp (a1,a2) -> pretty_infix_exp p 9 sym pretty_nraenv_aux sym.circ ff a1 a2
  | Core.NRAEnvGetConstant s -> fprintf ff "Table%a%s%a" pretty_sym sym.lfloor (string_of_char_list s) pretty_sym sym.rfloor
  | Core.NRAEnvEnv -> fprintf ff "%s" "ENV"
  | Core.NRAEnvAppEnv (a1,a2) ->  pretty_infix_exp p 10 sym pretty_nraenv_aux sym.circe ff a1 a2
  | Core.NRAEnvMapEnv a1 -> pretty_nraenv_exp p sym sym.chie ff a1 None
  | Core.NRAEnvFlatMap (a1,a2) -> pretty_nraenv_exp p sym sym.chiflat ff a1 (Some a2)
  | Core.NRAEnvJoin (a1,a2,a3) -> pretty_infix_dependent p 5 sym pretty_nraenv_aux sym.join ff a1 a2 a3
  | Core.NRAEnvNaturalJoin (a1,a2) -> pretty_infix_exp p 5 sym pretty_nraenv_aux sym.join ff a1 a2
  | Core.NRAEnvProject (atts,a1) ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.bpi (pretty_squared_names sym) atts (pretty_nraenv_aux 0 sym) a1
  | Core.NRAEnvGroupBy (g,atts,a1) ->
      fprintf ff "@[<hv 0>%a%a%a(%a)@]" pretty_sym sym.gamma (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nraenv_aux 0 sym) a1
  | Core.NRAEnvUnnest (a,b,a1) ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.rho (pretty_squared_names sym) [a;b] (pretty_nraenv_aux 0 sym) a1
  end

(* resets precedence back to 0 *)
and pretty_nraenv_exp p sym thissym ff a1 oa2 =
  begin match oa2 with
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
  end

and pretty_infix_dependent pouter pinner sym callb thissym ff a1 a2 a3 =
  if pouter > pinner
  then
    fprintf ff "@[<hov 0>(%a@ %a%a%a%a@ %a)@]" (callb pinner sym) a1 pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle (callb pinner sym) a2
  else
    fprintf ff "@[<hov 0>%a@ %a%a%a%a@ %a@]" (callb pinner sym) a1 pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle (callb pinner sym) a2


let pretty_nraenv greek margin annot inheritance link_runtime q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nraenv_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNRAEnv *)

let pretty_nraenv_core greek margin annot inheritance link_runtime q =
  pretty_nraenv greek margin annot inheritance link_runtime (QDriver.nraenv_core_to_nraenv q)
    
(** Pretty NNRC *)

let rec pretty_nnrc_aux p sym ff n =
  begin match n with
  | Core.NNRCGetConstant v -> fprintf ff "$$%s"  (string_of_char_list v)
  | Core.NNRCVar v -> fprintf ff "$v%s"  (string_of_char_list v)
  | Core.NNRCConst d -> fprintf ff "%a" pretty_data d
  | Core.NNRCBinop (b,n1,n2) -> (pretty_binary_op p sym pretty_nnrc_aux) ff b n1 n2
  | Core.NNRCUnop (u,n1) -> (pretty_unary_op p sym pretty_nnrc_aux) ff u n1
  | Core.NNRCLet (v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	      (string_of_char_list v)
	      (pretty_nnrc_aux p sym) n1
	      (pretty_nnrc_aux p sym) n2
  | Core.NNRCFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	      (pretty_nnrc_aux 0 sym) n2
	      (string_of_char_list v) pretty_sym sym.sin
	      (pretty_nnrc_aux 0 sym) n1
  | Core.NNRCIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	      (pretty_nnrc_aux p sym) n1
	      (pretty_nnrc_aux p sym) n2
	      (pretty_nnrc_aux p sym) n3
  | Core.NNRCEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      (pretty_nnrc_aux p sym) n0
	      (string_of_char_list v1) (pretty_nnrc_aux p sym) n1
	      (string_of_char_list v2) (pretty_nnrc_aux p sym) n2
  | Core.NNRCGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrc_aux 0 sym) n1
  end

let pretty_nnrc greek margin annot inheritance link_runtime q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrc_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNNRC *)

let pretty_nnrc_core greek margin annot inheritance link_runtime q =
  pretty_nnrc greek margin annot inheritance link_runtime q

(** Pretty NNRS *)

let rec pretty_nnrs_expr p sym ff e =
  begin match e with
  | Core.NNRSGetConstant v -> fprintf ff "$$%s"  (string_of_char_list v)
  | Core.NNRSVar v -> fprintf ff "$v%s"  (string_of_char_list v)
  | Core.NNRSConst d -> fprintf ff "%a" pretty_data d
  | Core.NNRSBinop (b,n1,n2) -> (pretty_binary_op p sym pretty_nnrs_expr) ff b n1 n2
  | Core.NNRSUnop (u,n1) -> (pretty_unary_op p sym pretty_nnrs_expr) ff u n1
  | Core.NNRSGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrs_expr 0 sym) n1
  end

let rec pretty_nnrs_stmt p sym ff stmt =
  begin match stmt with
  | Core.NNRSSeq (s1, s2) ->
      fprintf ff "@[<hv 0>%a;@;<1 0>%a@]"
        (pretty_nnrs_stmt 0 sym) s1
        (pretty_nnrs_stmt 0 sym) s2
  | Core.NNRSLet (v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
        (string_of_char_list v)
        (pretty_nnrs_expr p sym) n1
        (pretty_nnrs_stmt p sym) n2
  | Core.NNRSLetMut (v, s1, s2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s from {%a} @]@;<1 0>@[<hv 2>in@ @[<hv 2>%a@]@]@]"
        (string_of_char_list v)
        (pretty_nnrs_stmt p sym) s1
        (pretty_nnrs_stmt p sym) s2
  | Core.NNRSLetMutColl (v, s1, s2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let_coll $v%s from {%a} @]@;<1 0>@[<hv 2>in@ @[<hv 2>%a@]@]@]"
        (string_of_char_list v)
        (pretty_nnrs_stmt p sym) s1
        (pretty_nnrs_stmt p sym) s2
  | Core.NNRSPush (v, e) ->
      fprintf ff "@[<hv 2>push(@,$v%s,@;<1 0>%a@;<0 -2>)@]"
        (string_of_char_list v)
        (pretty_nnrs_expr 0 sym) e
  | Core.NNRSAssign (v, e) ->
      fprintf ff "@[<hv 2>$v%s :=@;<1 0>%a@;<0 -2>)@]"
        (string_of_char_list v)
        (pretty_nnrs_expr 0 sym) e
  | Core.NNRSFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>for (@[<hv 2>$v%s %a@;<1 0>%a@]) {@;<1 2>%a@ }@]"
        (string_of_char_list v) pretty_sym sym.sin
        (pretty_nnrs_expr 0 sym) n1
        (pretty_nnrs_stmt 0 sym) n2
  | Core.NNRSIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
        (pretty_nnrs_expr p sym) n1
        (pretty_nnrs_stmt p sym) n2
        (pretty_nnrs_stmt p sym) n3
  | Core.NNRSEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
        (pretty_nnrs_expr p sym) n0
        (string_of_char_list v1) (pretty_nnrs_stmt p sym) n1
        (string_of_char_list v2) (pretty_nnrs_stmt p sym) n2
  end

let pretty_nnrs_aux p sym ff ((s, ret): Core.nnrs) =
  fprintf ff "@[<hv 0>%a;@;<1 0>return $v%s@]@]"
    (pretty_nnrs_stmt 0 sym) s
    (string_of_char_list ret)


let pretty_nnrs greek margin annot inheritance link_runtime q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrs_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNNRS *)

let pretty_nnrs_core greek margin annot inheritance link_runtime q =
  pretty_nnrs greek margin annot inheritance link_runtime q

(** Pretty NNRSimp *)

let rec pretty_nnrs_imp_expr p sym ff e =
  begin match e with
  | Core.NNRSimpGetConstant v -> fprintf ff "$$%s"  (string_of_char_list v)
  | Core.NNRSimpVar v -> fprintf ff "$v%s"  (string_of_char_list v)
  | Core.NNRSimpConst d -> fprintf ff "%a" pretty_data d
  | Core.NNRSimpBinop (b,n1,n2) -> (pretty_binary_op p sym pretty_nnrs_imp_expr) ff b n1 n2
  | Core.NNRSimpUnop (u,n1) -> (pretty_unary_op p sym pretty_nnrs_imp_expr) ff u n1
  | Core.NNRSimpGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrs_imp_expr 0 sym) n1
  end

let rec pretty_nnrs_imp_stmt p sym ff stmt =
  begin match stmt with
  | Core.NNRSimpSkip ->
      fprintf ff "@[<hv 0>()@;<1 0>@]"
  | Core.NNRSimpSeq (s1, s2) ->
      fprintf ff "@[<hv 0>%a;@;<1 0>%a@]"
        (pretty_nnrs_imp_stmt 0 sym) s1
        (pretty_nnrs_imp_stmt 0 sym) s2
  | Core.NNRSimpLet (v,None,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s@]@;<1 0>@[<hv 2>in@ %a@]@]"
        (string_of_char_list v)
        (pretty_nnrs_imp_stmt p sym) n2
  | Core.NNRSimpLet (v,Some n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
        (string_of_char_list v)
        (pretty_nnrs_imp_expr p sym) n1
        (pretty_nnrs_imp_stmt p sym) n2
  | Core.NNRSimpAssign (v, e) ->
      fprintf ff "@[<hv 2>$v%s :=@;<1 0>%a@;<0 -2>@]"
        (string_of_char_list v)
        (pretty_nnrs_imp_expr 0 sym) e
  | Core.NNRSimpFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>for (@[<hv 2>$v%s %a@;<1 0>%a@]) {@;<1 2>%a@ }@]"
        (string_of_char_list v) pretty_sym sym.sin
        (pretty_nnrs_imp_expr 0 sym) n1
        (pretty_nnrs_imp_stmt 0 sym) n2
  | Core.NNRSimpIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
        (pretty_nnrs_imp_expr p sym) n1
        (pretty_nnrs_imp_stmt p sym) n2
        (pretty_nnrs_imp_stmt p sym) n3
  | Core.NNRSimpEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
        (pretty_nnrs_imp_expr p sym) n0
        (string_of_char_list v1) (pretty_nnrs_imp_stmt p sym) n1
        (string_of_char_list v2) (pretty_nnrs_imp_stmt p sym) n2
  end

let pretty_nnrs_imp_aux p sym ff ((s, ret): Core.nnrs_imp) =
  fprintf ff "@[<hv 0>%a;@;<1 0>return $v%s@]@]"
    (pretty_nnrs_imp_stmt 0 sym) s
    (string_of_char_list ret)

let pretty_nnrs_imp greek margin annot inheritance link_runtime q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrs_imp_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty Imp *)

let pretty_imp_expr pretty_constant pretty_op pretty_runtime p sym ff e =
  let rec pretty_imp_expr p sym ff e =
    begin match e with
    | Core.ImpExprVar v -> fprintf ff "%s"  (string_of_char_list v)
    | Core.ImpExprConst d -> fprintf ff "%a" pretty_constant d
    | Core.ImpExprOp (op,args) -> (pretty_op p sym pretty_imp_expr) ff (op, args)
    | Core.ImpExprRuntimeCall (op,args) -> (pretty_runtime p sym pretty_imp_expr) ff (op, args)
    | Core.ImpExprError msg -> fprintf ff "error %s"  (string_of_char_list msg)
    end
  in
  pretty_imp_expr p sym ff e

let pretty_imp_stmt pretty_constant pretty_op pretty_runtime p sym ff stmt =
  let pretty_imp_expr p sym ff e = pretty_imp_expr pretty_constant pretty_op pretty_runtime p sym ff e in
  let pretty_decl p sym ff (v, e_opt) =
    begin match e_opt with
    | None ->
        fprintf ff "@[<hv 0>@[<hv 2>let %s;@]@]"
          (string_of_char_list v)
    | Some e ->
        fprintf ff "@[<hv 0>@[<hv 2>let %s =@ %a;@]@]"
          (string_of_char_list v)
          (pretty_imp_expr p sym) e
    end
  in
  let rec pretty_imp_stmt p sym ff stmt =
    begin match stmt with
    | Core.ImpStmtBlock (decls, stmts) ->
        fprintf ff "@[<hv 0>{@;<1 2>%a@;<1 2>%a@ }@]"
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff "@;<1 0>") (pretty_decl p sym)) decls
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff "@;<1 0>") (pretty_imp_stmt p sym)) stmts
    | Core.ImpStmtAssign (v, e) ->
        fprintf ff "@[<hv 2>%s =@;<1 0>%a;@;<0 -2>@]"
          (string_of_char_list v)
          (pretty_imp_expr 0 sym) e
    | Core.ImpStmtFor (v,e,s) ->
        fprintf ff "@[<hv 0>for (@[<hv 2>%s %a@;<1 0>%a@]) {@;<1 2>%a@ }@]"
          (string_of_char_list v) pretty_sym sym.sin
          (pretty_imp_expr 0 sym) e
          (pretty_imp_stmt 0 sym) s
    | Core.ImpStmtForRange (v,e1,e2,s) ->
        fprintf ff "@[<hv 0>for (@[<hv 2>%s =@;<1 0>%a to@;<1 0>%a@]) {@;<1 2>%a@ }@]"
          (string_of_char_list v)
          (pretty_imp_expr 0 sym) e1
          (pretty_imp_expr 0 sym) e2
          (pretty_imp_stmt 0 sym) s
    | Core.ImpStmtIf (e,s1,s2) ->
        fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
          (pretty_imp_expr p sym) e
          (pretty_imp_stmt p sym) s1
          (pretty_imp_stmt p sym) s2
    end
  in
  pretty_imp_stmt p sym ff stmt


let pretty_imp_return pretty_constant pretty_op pretty_runtime p sym ff ret =
  let pretty_imp_expr p sym ff e = pretty_imp_expr pretty_constant pretty_op pretty_runtime p sym ff e in
  fprintf ff "@[<hv 2>return@;<1 0>%a;@;<0 -2>@]"
    (pretty_imp_expr 0 sym) (Core.ImpExprVar ret)

let pretty_imp_function pretty_constant pretty_op pretty_runtime p sym ff f =
  let Core.ImpFun (arg, body, ret) = f in
  fprintf ff "@[<hv 0>function (%a) {@;<1 2>%a@;<1 2>%a@ }@]"
    (fun ff v -> fprintf ff "%s" (string_of_char_list v)) arg
    (pretty_imp_stmt pretty_constant pretty_op pretty_runtime p sym) body
    (pretty_imp_return pretty_constant pretty_op pretty_runtime p sym) ret

let pretty_imp_aux pretty_constant pretty_op pretty_runtime p sym ff ((* ImpLib *) l) =
  List.iter
    (fun (f, def) ->
      fprintf ff "@[<hv 0>@[<hv 2>define %s as@ %a@]@;<0 0>@]"
        (string_of_char_list f)
        (pretty_imp_function pretty_constant pretty_op pretty_runtime p sym) def)
    l

let pretty_imp pretty_constant pretty_op pretty_runtime greek margin annot inheritance link_runtime q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_imp_aux pretty_constant pretty_op pretty_runtime 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty ImpData *)

let pretty_imp_data_constant = pretty_data

let pretty_imp_data_op p sym pretty_imp_expr ff (op, args) =
  begin match op, args with
  | Core.DataOpUnary u, [ e ] ->
      (pretty_unary_op p sym pretty_imp_expr) ff u e
  | Core.DataOpBinary b, [e1;e2] ->
      (pretty_binary_op p sym pretty_imp_expr) ff b e1 e2
  | _ -> assert false
  end

let pretty_imp_data_runtime p sym pretty_imp_expr ff (op, args) =
  begin match op, args with
  | Core.DataRuntimeGroupby(g,atts), [e] ->
      fprintf ff "@[<hv 2>groupBy@[<hv 2>(%a,@ %a,@ %a)@]@]"
        (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_imp_expr 0 sym) e
  | Core.DataRuntimeEither, [e] ->
      fprintf ff "@[<hv 2>either@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | Core.DataRuntimeToLeft, [e] ->
      fprintf ff "@[<hv 2>toLeft@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | Core.DataRuntimeToRight, [e] ->
      fprintf ff "@[<hv 2>toRight@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | _ -> assert false
  end

let pretty_imp_data = pretty_imp pretty_imp_data_constant pretty_imp_data_op pretty_imp_data_runtime

(** Pretty ImpData *)

let pretty_imp_ejson_constant ff d =
  fprintf ff "%s"
    (string_of_char_list (Core.EnhancedCompiler.QData.cejson_to_string d))

let pretty_imp_ejson_op p sym pretty_imp_expr ff (op, args) =
  begin match op, args with
  | Core.EJsonOpNot, [ e ] ->
      fprintf ff "@[<hv 2>!@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | EJsonOpNeg, [ e ] ->
      fprintf ff "@[<hv 2>-@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | EJsonOpAnd, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ &&@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpOr, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ ||@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpLt, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ <@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpLe, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ <=@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpGt, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ >@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpGe, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ >=@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpAddString, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ +@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpAddNumber, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ +@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpSub, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ -@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpMult, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ *@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpDiv, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ /@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpStrictEqual, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ ===@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpStrictDisequal, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@ !==@ @[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpArray, args ->
      fprintf ff "@[<hv 2>[@[<hv 2>%a@]@]@]"
        (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ",@;<1 0>") (pretty_imp_expr 0 sym))
        args
  | EJsonOpArrayLength, [ e ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a).length@]@]" (pretty_imp_expr 0 sym) e
  | EJsonOpArrayPush, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@].push@[<hv 2>(%a)@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpArrayAccess, [ e1; e2 ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)@]@[<hv 2>[%a]@]@]"
        (pretty_imp_expr 0 sym) e1 (pretty_imp_expr 0 sym) e2
  | EJsonOpObject fields, args ->
      let field_arg_list = List.map2 (fun x y -> (string_of_char_list x, y)) fields args in
      fprintf ff "@[<hv 2>[@[<hv 2>%a@]@]@]"
        (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ",@;<1 0>")
           (fun ff (f,e) -> fprintf ff "@[<hv 2>'%s': %a@]" f (pretty_imp_expr 0 sym) e))
        field_arg_list
  | EJsonOpAccess field, [ e ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)['%s']@]@]" (pretty_imp_expr 0 sym) e (string_of_char_list field)
  | EJsonOpHasOwnProperty field, [ e ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a).hasOwnProperty('%s')@]@]" (pretty_imp_expr 0 sym) e (string_of_char_list field)
  | _ -> assert false
  end

let pretty_imp_ejson_runtime p sym pretty_imp_expr ff (op, args) =
  fprintf ff "@[<hv 2>%s(@[<hv 2>%a@])@]"
    (string_of_char_list (QUtil.string_of_ejson_runtime_op op))
    (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ",@;<1 0>") (pretty_imp_expr 0 sym)) args

let pretty_imp_ejson = pretty_imp pretty_imp_ejson_constant pretty_imp_ejson_op pretty_imp_ejson_runtime

(** Pretty NNRCMR *)

let pretty_fun sym ff (x, n) =
  fprintf ff "@[fun ($v%s) ->@ %a@]"
    (string_of_char_list x)
    (pretty_nnrc_aux 0 sym) n

let pretty_default_fun sym ff n =
  fprintf ff "@[fun db_default() ->@ %a@]"
    (pretty_nnrc_aux 0 sym) n

let pretty_reduce_op_to_string op =
  begin match op with
  | Core.RedOpCount -> "count"
  | Core.RedOpSum typ -> "+"
  | Core.RedOpMin typ -> "min"
  | Core.RedOpMax typ -> "max"
  | Core.RedOpArithMean typ -> "arithmean"
  | Core.RedOpStats typ -> "stats"
  end

let pretty_nnrcmr_job_aux sym ff mr =
  let distributed = "distributed" in
  let scalar = "scalar" in
  let input_loc =
    begin match mr.Core.mr_map with
    | Core.MapDist _ -> distributed
    | Core.MapDistFlatten _ -> distributed
    | Core.MapScalar _ -> scalar
    end
  in
  let output_loc =
    begin match mr.Core.mr_reduce with
    | Core.RedId -> distributed
    | Core.RedCollect _ -> scalar
    | Core.RedOp _ -> scalar
    | Core.RedSingleton -> scalar
    end
  in
  fprintf ff "@[<hv 0>input = $v%s : %s;@\n"
    (string_of_char_list mr.Core.mr_input) input_loc;
  fprintf ff "output = $v%s : %s;@\n"
    (string_of_char_list mr.Core.mr_output) output_loc;
  begin match mr.Core.mr_map with
  | Core.MapDist f -> fprintf ff "map(@[%a@]);" (pretty_fun sym) f
  | Core.MapDistFlatten f -> fprintf ff "flatMap(@[%a@]);" (pretty_fun sym) f
  | Core.MapScalar f -> fprintf ff "@[%a@];" (pretty_fun sym) f
  end;
  fprintf ff "@\n";
  begin match mr.Core.mr_reduce with
  | Core.RedId -> ()
  | Core.RedCollect f -> fprintf ff "reduce(@[%a@]);" (pretty_fun sym) f
  | Core.RedOp op ->
      let op_s = pretty_reduce_op_to_string (Obj.magic op)
      in
      fprintf ff "reduce(%s);" op_s
  | Core.RedSingleton ->       fprintf ff "reduce(singleton);"
  end;
  fprintf ff "@\n";
  begin match QUtil.mr_reduce_empty [] mr with
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
  begin match l with
  | [] -> ()
  | d :: [] -> fprintf ff "%a" pp d
  | d :: l -> fprintf ff "%a%s@ %a" pp d sep (pretty_list pp sep) l
  end

let pretty_mr_last sym ff mr_last =
  let ((params, n), args) = mr_last in
  let pretty_param ff x =
    fprintf ff "%s" (string_of_char_list x)
  in
  let pretty_arg ff (x, loc) =
    begin match loc with
    | Core.Vlocal ->  fprintf ff "(%s: Scalar)" (string_of_char_list x)
    | Core.Vdistr ->  fprintf ff "(%s: Distributed)" (string_of_char_list x)
    end
  in
  fprintf ff "@[(fun (%a) => %a) (%a)@]"
    (pretty_list pretty_param ",") params
    (pretty_nnrc_aux 0 sym) n
    (pretty_list pretty_arg ",") args

let pretty_nnrcmr_aux sym ff mrl =
  pretty_mr_chain sym ff mrl.Core.mr_chain;
  fprintf ff "@[%a@]" (pretty_mr_last sym) mrl.Core.mr_last

let pretty_nnrcmr greek margin annot inheritance link_runtime mr_chain =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrcmr_aux sym) mr_chain;
    flush_str_formatter ()
  end

(** Pretty DNNRC *)

let rec pretty_dnnrc_aux ann plug p sym ff n =
  begin match n with
  | Core.DNNRCGetConstant (a, v) -> fprintf ff "%a$%s" ann a (string_of_char_list v)
  | Core.DNNRCVar (a, v) -> fprintf ff "%a$v%s" ann a (string_of_char_list v)
  | Core.DNNRCConst (a, d) -> fprintf ff "%a%a" ann a pretty_data d
  | Core.DNNRCBinop (a, b,n1,n2) ->
      fprintf ff "%a(" ann a
        ; ((pretty_binary_op 0 sym (pretty_dnnrc_aux ann plug)) ff b n1 n2)
        ; fprintf ff ")"
  | Core.DNNRCUnop (a,u,n1) ->
      fprintf ff "%a(" ann a
        ; ((pretty_unary_op 0 sym (pretty_dnnrc_aux ann plug)) ff u n1)
        ; fprintf ff ")"
  | Core.DNNRCLet (a,v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>%a let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	      ann a
	      (string_of_char_list v)
	      (pretty_dnnrc_aux ann plug p sym) n1
	      (pretty_dnnrc_aux ann plug p sym) n2
  | Core.DNNRCFor (a,v,n1,n2) ->
      fprintf ff "@[<hv 0>%a{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	      ann a
	      (pretty_dnnrc_aux ann plug 0 sym) n2
	      (string_of_char_list v) pretty_sym sym.sin
	      (pretty_dnnrc_aux ann plug 0 sym) n1
  | Core.DNNRCIf (a,n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>%a if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	      ann a
	      (pretty_dnnrc_aux ann plug p sym) n1
	      (pretty_dnnrc_aux ann plug p sym) n2
	      (pretty_dnnrc_aux ann plug p sym) n3
  | Core.DNNRCEither (a,n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>%a match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      ann a
	      (pretty_dnnrc_aux ann plug p sym) n0
	      (string_of_char_list v1) (pretty_dnnrc_aux ann plug p sym) n1
	      (string_of_char_list v2) (pretty_dnnrc_aux ann plug p sym) n2
  | Core.DNNRCCollect (a,n1) ->
      fprintf ff "@[%a%s[@[%a@]]@]"
	      ann a
	      "COLLECT"
	      (pretty_dnnrc_aux ann plug p sym) n1
  | Core.DNNRCDispatch (a,n1) ->
      fprintf ff "@[%a%s[@[%a@]]@]"
	      ann a
	      "DISPATCH"
	      (pretty_dnnrc_aux ann plug p sym) n1
  | Core.DNNRCAlg (a,body,arglist) ->
      fprintf ff "@[%adataframe(@[fun $%a => @] %a)@[(%a)@]@]"
	      ann a
        (pretty_list (fun ff s -> fprintf ff "%s" s) ",") (List.map (fun x -> (string_of_char_list (fst x))) arglist)
        plug body
	      (pretty_list (pretty_dnnrc_aux ann plug p sym) ",") (List.map snd arglist)
  | Core.DNNRCGroupBy (a,g,atts,n1) ->
      fprintf ff "@[<hv 2>%agroup by@ %a%a@[<hv 2>(%a)@]@]" ann a (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_dnnrc_aux ann plug 0 sym) n1
  end

let pretty_dnnrc_base ann plug greek margin annot n =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_dnnrc_aux ann plug 0 sym) n;
    flush_str_formatter ()
  end

let pretty_annotate_ignore ff a = ()

(* Pretty Spark IR *)
let rec pretty_column_aux p sym ff col =
  begin match col with
  | Core.CCol v -> fprintf ff "%a%s%a" pretty_sym sym.langle (string_of_char_list v) pretty_sym sym.rangle
  | Core.CDot (v,c) -> pretty_unary_op p sym pretty_column_aux ff (Core.OpDot v) c
  | Core.CLit (d,rt) -> fprintf ff "@[%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle pretty_data d
  | Core.CPlus (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff (Core.OpNatBinary Core.NatPlus) c1 c2
  | Core.CEq (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff Core.OpEqual c1 c2
  | Core.CLessThan (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff Core.OpLt c1 c2
  | Core.CNeg c -> pretty_unary_op p sym pretty_column_aux ff Core.OpNeg c
  | Core.CToString c -> pretty_unary_op p sym pretty_column_aux ff Core.OpToString c
  | Core.CSConcat (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff Core.OpStringConcat c1 c2
  | Core.CUDFCast (bs,c) -> pretty_unary_op p sym pretty_column_aux ff (Core.OpCast bs) c
  | Core.CUDFUnbrand (rt,c) -> fprintf ff "@[!%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle (pretty_column_aux p sym) c
  end

let pretty_named_column_aux p sym ff (name, col) =
  fprintf ff "%s%@%a" (string_of_char_list name) (pretty_column_aux p sym) col

let rec pretty_dataframe_aux p sym ff ds =
  begin match ds with
  | Core.DSVar v -> fprintf ff "$%s" (string_of_char_list v)
  | Core.DSSelect (cl,ds1) -> fprintf ff "@[select %a @[<hv 2>from %a@] @]"
				(pretty_list (pretty_named_column_aux p sym) ",") cl (pretty_dataframe_aux p sym) ds1
  | Core.DSFilter (c,ds1) -> fprintf ff "@[filter %a @[<hv 2>from %a@] @]"
				(pretty_column_aux p sym) c (pretty_dataframe_aux p sym) ds1
  | Core.DSCartesian (ds1,ds2) ->  pretty_binary_op p sym pretty_dataframe_aux ff Core.OpRecConcat ds1 ds2
  | Core.DSExplode (s,ds) -> fprintf ff "@[explode %s @[<hv 2>from %a@] @]" (string_of_char_list s) (pretty_dataframe_aux p sym) ds
  end

let pretty_plug_dataframe greek ff a =
  let sym = if greek then greeksym else textsym in
  pretty_dataframe_aux 0 sym ff a

let pretty_dnnrc greek margin annot inheritance link_runtime q =
  let ann = pretty_annotate_ignore in
  let plug = pretty_plug_dataframe greek in
  pretty_dnnrc_base ann plug greek margin annot q

(** Pretty tDNNRC *)

let pretty_dnnrc_typed greek margin annot inheritance link_runtime q =
  let ann =
    if annot
    then pretty_annotate_annotated_rtype greek pretty_annotate_ignore
    else pretty_annotate_ignore
  in
  let plug = pretty_plug_dataframe greek in
  pretty_dnnrc_base ann plug greek margin annot q

(** Pretty JavaScript Ast *)

let pretty_js_ast greek margin annot inheritance link_runtime q =
  "(* There is no pretty printer for JavaScript AST at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty JavaScript *)

let pretty_javascript greek margin annot inheritance link_runtime q =
  let runtime = 
    if (link_runtime)
    then Js_runtime.runtime
    else ""
  in
  runtime ^ q

(** Pretty Java *)

let pretty_java greek margin annot inheritance link_runtime q =
  q

(** Pretty SparkDF *)

let pretty_spark_df greek margin annot inheritance link_runtime q =
  q

(** Pretty Error *)

let pretty_error greek margin annot inheritance link_runtime q =
  "Error: "^(string_of_char_list q)

