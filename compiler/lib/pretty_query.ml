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
open DData
open Dataframe
open NRA
open NRAEnv
open CNNRC
open NNRS
open NNRSimp
open Imp
open ImpData
open NNRCMR
open DNNRCBase
open EJsonOperators
open EnhancedReduceOps
open EnhancedCompiler.EnhancedCompiler

open Pretty_common

(** Pretty query wrapper *)

type 'a pretty_fun = bool -> int -> bool -> QData.json -> 'a -> string
	  
let pretty_query pconf (pretty_q:'a pretty_fun) (q:'a) =
  let greek = get_charset_bool pconf in
  let margin = get_margin pconf in
  let annot = get_type_annotations pconf in
  let inheritance = get_inheritance pconf in
  pretty_q greek margin annot inheritance q

(** Pretty CAMPRule *)

let pretty_camp_rule greek margin annot inheritance q =
  "(* There is no pretty printer for CAMPRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty TechRule *)

let pretty_tech_rule greek margin annot inheritance q =
  "(* There is no pretty printer for TechRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty DesignerRule *)

let pretty_designer_rule greek margin annot inheritance q =
  "(* There is no pretty printer for TechRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty CAMP *)

let pretty_camp greek margin annot inheritance q =
  "(* There is no pretty printer for CAMP at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty OQL *)

let pretty_oql greek margin annot inheritance q =
  "(* There is no pretty printer for OQL at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty SQL *)

let pretty_sql greek margin annot inheritance q =
  "(* There is no pretty printer for SQL at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty SQL++ *)

let pretty_sqlpp greek margin annot inheritance q =
  "(* There is no pretty printer for SQL++ at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty LambdaNRA *)

let pretty_lambda_nra greek margin annot inheritance q =
  "(* There is no pretty printer for LambdaNRA at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty NRA *)

let rec pretty_nra_aux p sym ff a =
  begin match a with
  | NRAID -> fprintf ff "%s" "ID"
  | NRAConst d -> fprintf ff "%a" pretty_data d
  | NRABinop (b,a1,a2) -> (pretty_binary_op p sym pretty_nra_aux) ff b a1 a2
  | NRAUnop (u,a1) -> (pretty_unary_op p sym pretty_nra_aux) ff u a1
  | NRAMap (a1,a2) -> pretty_nra_exp p sym sym.chi ff a1 (Some a2)
  | NRAMapProduct (a1,a2) -> pretty_nra_exp p sym sym.djoin ff a1 (Some a2)
  | NRAProduct (a1,a2) -> pretty_infix_exp p 5 sym pretty_nra_aux sym.times ff a1 a2
  | NRASelect (a1,a2) -> pretty_nra_exp p sym sym.sigma ff a1 (Some a2)
  | NRADefault (a1,a2) -> pretty_infix_exp p 8 sym pretty_nra_aux sym.bars ff a1 a2
  | NRAEither (a1,a2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ ID@;<1 -2>with@]@;<1 0>@[<hv 2>| left as ID ->@ %a@]@;<1 0>@[<hv 2>| right as ID ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      (pretty_nra_aux p sym) a1
	      (pretty_nra_aux p sym) a2
  | NRAEitherConcat (a1,a2) -> pretty_infix_exp p 7 sym pretty_nra_aux sym.sqlrarrow ff a1 a2
  | NRAApp (a1,a2) -> pretty_infix_exp p 9 sym pretty_nra_aux sym.circ ff a1 a2
  | NRAGetConstant s -> fprintf ff "Table%a%s%a" pretty_sym sym.lfloor s pretty_sym sym.rfloor
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

let pretty_nra greek margin annot inheritance q =
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
  | NRAEnvID -> fprintf ff "%s" "ID"
  | NRAEnvConst d -> fprintf ff "%a" pretty_data d
  | NRAEnvBinop (b,a1,a2) -> (pretty_binary_op p sym pretty_nraenv_aux) ff b a1 a2
  | NRAEnvUnop (u,a1) -> (pretty_unary_op p sym pretty_nraenv_aux) ff u a1
  | NRAEnvMap (a1,a2) -> pretty_nraenv_exp p sym sym.chi ff a1 (Some a2)
  | NRAEnvMapProduct (a1,a2) -> pretty_nraenv_exp p sym sym.djoin ff a1 (Some a2)
  | NRAEnvProduct (a1,a2) -> pretty_infix_exp p 5 sym pretty_nraenv_aux sym.times ff a1 a2
  | NRAEnvSelect (a1,a2) -> pretty_nraenv_exp p sym sym.sigma ff a1 (Some a2)
  | NRAEnvDefault (a1,a2) -> pretty_infix_exp p 8 sym pretty_nraenv_aux sym.bars ff a1 a2
  | NRAEnvEither (a1,a2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ ID@;<1 -2>with@]@;<1 0>@[<hv 2>| left as ID ->@ %a@]@;<1 0>@[<hv 2>| right as ID ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      (pretty_nraenv_aux p sym) a1
	      (pretty_nraenv_aux p sym) a2
  | NRAEnvEitherConcat (a1,a2) -> pretty_infix_exp p 7 sym pretty_nraenv_aux sym.sqlrarrow ff a1 a2
  | NRAEnvApp (a1,a2) -> pretty_infix_exp p 9 sym pretty_nraenv_aux sym.circ ff a1 a2
  | NRAEnvGetConstant s -> fprintf ff "Table%a%s%a" pretty_sym sym.lfloor s pretty_sym sym.rfloor
  | NRAEnvEnv -> fprintf ff "%s" "ENV"
  | NRAEnvAppEnv (a1,a2) ->  pretty_infix_exp p 10 sym pretty_nraenv_aux sym.circe ff a1 a2
  | NRAEnvMapEnv a1 -> pretty_nraenv_exp p sym sym.chie ff a1 None
  | NRAEnvFlatMap (a1,a2) -> pretty_nraenv_exp p sym sym.chiflat ff a1 (Some a2)
  | NRAEnvJoin (a1,a2,a3) -> pretty_infix_dependent p 5 sym pretty_nraenv_aux sym.join ff a1 a2 a3
  | NRAEnvNaturalJoin (a1,a2) -> pretty_infix_exp p 5 sym pretty_nraenv_aux sym.join ff a1 a2
  | NRAEnvProject (atts,a1) ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.bpi (pretty_squared_names sym) atts (pretty_nraenv_aux 0 sym) a1
  | NRAEnvGroupBy (g,atts,a1) ->
      fprintf ff "@[<hv 0>%a%a%a(%a)@]" pretty_sym sym.gamma (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nraenv_aux 0 sym) a1
  | NRAEnvUnnest (a,b,a1) ->
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


let pretty_nraenv greek margin annot inheritance q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nraenv_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNRAEnv *)

let pretty_nraenv_core greek margin annot inheritance q =
  pretty_nraenv greek margin annot inheritance (QDriver.nraenv_core_to_nraenv q)
    
(** Pretty NNRC *)

let rec pretty_nnrc_aux p sym ff n =
  begin match n with
  | NNRCGetConstant v -> fprintf ff "$$%s" v
  | NNRCVar v -> fprintf ff "$v%s"  v
  | NNRCConst d -> fprintf ff "%a" pretty_data d
  | NNRCBinop (b,n1,n2) -> (pretty_binary_op p sym pretty_nnrc_aux) ff b n1 n2
  | NNRCUnop (u,n1) -> (pretty_unary_op p sym pretty_nnrc_aux) ff u n1
  | NNRCLet (v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	      v
	      (pretty_nnrc_aux p sym) n1
	      (pretty_nnrc_aux p sym) n2
  | NNRCFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	      (pretty_nnrc_aux 0 sym) n2
	      v pretty_sym sym.sin
	      (pretty_nnrc_aux 0 sym) n1
  | NNRCIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	      (pretty_nnrc_aux p sym) n1
	      (pretty_nnrc_aux p sym) n2
	      (pretty_nnrc_aux p sym) n3
  | NNRCEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      (pretty_nnrc_aux p sym) n0
	      v1 (pretty_nnrc_aux p sym) n1
	      v2 (pretty_nnrc_aux p sym) n2
  | NNRCGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrc_aux 0 sym) n1
  end

let pretty_nnrc greek margin annot inheritance q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrc_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNNRC *)

let pretty_nnrc_core greek margin annot inheritance q =
  pretty_nnrc greek margin annot inheritance q

(** Pretty NNRS *)

let rec pretty_nnrs_expr p sym ff e =
  begin match e with
  | NNRSGetConstant v -> fprintf ff "$$%s" v
  | NNRSVar v -> fprintf ff "$v%s" v
  | NNRSConst d -> fprintf ff "%a" pretty_data d
  | NNRSBinop (b,n1,n2) -> (pretty_binary_op p sym pretty_nnrs_expr) ff b n1 n2
  | NNRSUnop (u,n1) -> (pretty_unary_op p sym pretty_nnrs_expr) ff u n1
  | NNRSGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrs_expr 0 sym) n1
  end

let rec pretty_nnrs_stmt p sym ff stmt =
  begin match stmt with
  | NNRSSeq (s1, s2) ->
      fprintf ff "@[<hv 0>%a;@;<1 0>%a@]"
        (pretty_nnrs_stmt 0 sym) s1
        (pretty_nnrs_stmt 0 sym) s2
  | NNRSLet (v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
        v
        (pretty_nnrs_expr p sym) n1
        (pretty_nnrs_stmt p sym) n2
  | NNRSLetMut (v, s1, s2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s from {%a} @]@;<1 0>@[<hv 2>in@ @[<hv 2>%a@]@]@]"
        v
        (pretty_nnrs_stmt p sym) s1
        (pretty_nnrs_stmt p sym) s2
  | NNRSLetMutColl (v, s1, s2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let_coll $v%s from {%a} @]@;<1 0>@[<hv 2>in@ @[<hv 2>%a@]@]@]"
        v
        (pretty_nnrs_stmt p sym) s1
        (pretty_nnrs_stmt p sym) s2
  | NNRSPush (v, e) ->
      fprintf ff "@[<hv 2>push(@,$v%s,@;<1 0>%a@;<0 -2>)@]"
        v
        (pretty_nnrs_expr 0 sym) e
  | NNRSAssign (v, e) ->
      fprintf ff "@[<hv 2>$v%s :=@;<1 0>%a@;<0 -2>)@]"
        v
        (pretty_nnrs_expr 0 sym) e
  | NNRSFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>for (@[<hv 2>$v%s %a@;<1 0>%a@]) {@;<1 2>%a@ }@]"
        v pretty_sym sym.sin
        (pretty_nnrs_expr 0 sym) n1
        (pretty_nnrs_stmt 0 sym) n2
  | NNRSIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
        (pretty_nnrs_expr p sym) n1
        (pretty_nnrs_stmt p sym) n2
        (pretty_nnrs_stmt p sym) n3
  | NNRSEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
        (pretty_nnrs_expr p sym) n0
        v1 (pretty_nnrs_stmt p sym) n1
        v2 (pretty_nnrs_stmt p sym) n2
  end

let pretty_nnrs_aux p sym ff ((s, ret): nnrs) =
  fprintf ff "@[<hv 0>%a;@;<1 0>return $v%s@]@]"
    (pretty_nnrs_stmt 0 sym) s
    ret


let pretty_nnrs greek margin annot inheritance q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrs_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNNRS *)

let pretty_nnrs_core greek margin annot inheritance q =
  pretty_nnrs greek margin annot inheritance q

(** Pretty NNRSimp *)

let rec pretty_nnrs_imp_expr p sym ff e =
  begin match e with
  | NNRSimpGetConstant v -> fprintf ff "$$%s"  v
  | NNRSimpVar v -> fprintf ff "$v%s"  v
  | NNRSimpConst d -> fprintf ff "%a" pretty_data d
  | NNRSimpBinop (b,n1,n2) -> (pretty_binary_op p sym pretty_nnrs_imp_expr) ff b n1 n2
  | NNRSimpUnop (u,n1) -> (pretty_unary_op p sym pretty_nnrs_imp_expr) ff u n1
  | NNRSimpGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrs_imp_expr 0 sym) n1
  end

let rec pretty_nnrs_imp_stmt p sym ff stmt =
  begin match stmt with
  | NNRSimpSkip ->
      fprintf ff "@[<hv 0>()@;<1 0>@]"
  | NNRSimpSeq (s1, s2) ->
      fprintf ff "@[<hv 0>%a;@;<1 0>%a@]"
        (pretty_nnrs_imp_stmt 0 sym) s1
        (pretty_nnrs_imp_stmt 0 sym) s2
  | NNRSimpLet (v,None,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s@]@;<1 0>@[<hv 2>in@ %a@]@]"
        v
        (pretty_nnrs_imp_stmt p sym) n2
  | NNRSimpLet (v,Some n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
        v
        (pretty_nnrs_imp_expr p sym) n1
        (pretty_nnrs_imp_stmt p sym) n2
  | NNRSimpAssign (v, e) ->
      fprintf ff "@[<hv 2>$v%s :=@;<1 0>%a@;<0 -2>@]"
        v
        (pretty_nnrs_imp_expr 0 sym) e
  | NNRSimpFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>for (@[<hv 2>$v%s %a@;<1 0>%a@]) {@;<1 2>%a@ }@]"
        v pretty_sym sym.sin
        (pretty_nnrs_imp_expr 0 sym) n1
        (pretty_nnrs_imp_stmt 0 sym) n2
  | NNRSimpIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
        (pretty_nnrs_imp_expr p sym) n1
        (pretty_nnrs_imp_stmt p sym) n2
        (pretty_nnrs_imp_stmt p sym) n3
  | NNRSimpEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
        (pretty_nnrs_imp_expr p sym) n0
        v1 (pretty_nnrs_imp_stmt p sym) n1
        v2 (pretty_nnrs_imp_stmt p sym) n2
  end

let pretty_nnrs_imp_aux p sym ff ((s, ret): nnrs_imp) =
  fprintf ff "@[<hv 0>%a;@;<1 0>return $v%s@]@]"
    (pretty_nnrs_imp_stmt 0 sym) s
    ret

let pretty_nnrs_imp greek margin annot inheritance q =
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
    | ImpExprVar v -> fprintf ff "%s"  v
    | ImpExprConst d -> fprintf ff "%a" pretty_constant d
    | ImpExprOp (op,args) -> (pretty_op p sym pretty_imp_expr) ff (op, args)
    | ImpExprRuntimeCall (op,args) -> (pretty_runtime p sym pretty_imp_expr) ff (op, args)
    | ImpExprError msg -> fprintf ff "error %s"  msg
    end
  in
  pretty_imp_expr p sym ff e

let pretty_imp_stmt pretty_constant pretty_op pretty_runtime p sym ff stmt =
  let pretty_imp_expr p sym ff e = pretty_imp_expr pretty_constant pretty_op pretty_runtime p sym ff e in
  let pretty_decl p sym ff (v, e_opt) =
    begin match e_opt with
    | None ->
        fprintf ff "@[<hv 0>@[<hv 2>let %s;@]@]"
          v
    | Some e ->
        fprintf ff "@[<hv 0>@[<hv 2>let %s =@ %a;@]@]"
          v
          (pretty_imp_expr p sym) e
    end
  in
  let rec pretty_imp_stmt p sym ff stmt =
    begin match stmt with
    | ImpStmtBlock (decls, stmts) ->
        fprintf ff "@[<hv 0>{@;<1 2>%a@;<1 2>%a@ }@]"
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff "@;<1 0>") (pretty_decl p sym)) decls
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff "@;<1 0>") (pretty_imp_stmt p sym)) stmts
    | ImpStmtAssign (v, e) ->
        fprintf ff "@[<hv 2>%s =@;<1 0>%a;@;<0 -2>@]"
          v
          (pretty_imp_expr 0 sym) e
    | ImpStmtFor (v,e,s) ->
        fprintf ff "@[<hv 0>for (@[<hv 2>%s %a@;<1 0>%a@]) {@;<1 2>%a@ }@]"
          v pretty_sym sym.sin
          (pretty_imp_expr 0 sym) e
          (pretty_imp_stmt 0 sym) s
    | ImpStmtForRange (v,e1,e2,s) ->
        fprintf ff "@[<hv 0>for (@[<hv 2>%s =@;<1 0>%a to@;<1 0>%a@]) {@;<1 2>%a@ }@]"
          v
          (pretty_imp_expr 0 sym) e1
          (pretty_imp_expr 0 sym) e2
          (pretty_imp_stmt 0 sym) s
    | ImpStmtIf (e,s1,s2) ->
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
    (pretty_imp_expr 0 sym) (ImpExprVar ret)

let pretty_imp_function pretty_constant pretty_op pretty_runtime p sym ff f =
  let ImpFun (arg, body, ret) = f in
  fprintf ff "@[<hv 0>function (%a) {@;<1 2>%a@;<1 2>%a@ }@]"
    (fun ff v -> fprintf ff "%s" v) arg
    (pretty_imp_stmt pretty_constant pretty_op pretty_runtime p sym) body
    (pretty_imp_return pretty_constant pretty_op pretty_runtime p sym) ret

let pretty_imp_aux pretty_constant pretty_op pretty_runtime p sym ff ((* ImpLib *) l) =
  List.iter
    (fun (f, def) ->
      fprintf ff "@[<hv 0>@[<hv 2>define %s as@ %a@]@;<0 0>@]"
        f
        (pretty_imp_function pretty_constant pretty_op pretty_runtime p sym) def)
    l

let pretty_imp pretty_constant pretty_op pretty_runtime greek margin annot inheritance q =
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
  | DataOpUnary u, [ e ] ->
      (pretty_unary_op p sym pretty_imp_expr) ff u e
  | DataOpBinary b, [e1;e2] ->
      (pretty_binary_op p sym pretty_imp_expr) ff b e1 e2
  | _ -> assert false
  end

let pretty_imp_data_runtime p sym pretty_imp_expr ff (op, args) =
  begin match op, args with
  | DataRuntimeGroupby(g,atts), [e] ->
      fprintf ff "@[<hv 2>groupBy@[<hv 2>(%a,@ %a,@ %a)@]@]"
        (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_imp_expr 0 sym) e
  | DataRuntimeEither, [e] ->
      fprintf ff "@[<hv 2>either@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | DataRuntimeToLeft, [e] ->
      fprintf ff "@[<hv 2>getLeft@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | DataRuntimeToRight, [e] ->
      fprintf ff "@[<hv 2>getRight@[<hv 2>(%a)@]@]" (pretty_imp_expr 0 sym) e
  | _ -> assert false
  end

let pretty_imp_data = pretty_imp pretty_imp_data_constant pretty_imp_data_op pretty_imp_data_runtime

(** Pretty ImpData *)

let pretty_imp_ejson_constant ff d =
  fprintf ff "%s"
    (QData.cejson_to_string d)

let pretty_imp_ejson_op p sym pretty_imp_expr ff (op, args) =
  begin match op, args with
  | EJsonOpNot, [ e ] ->
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
      let field_arg_list = List.map2 (fun x y -> (x, y)) fields args in
      fprintf ff "@[<hv 2>[@[<hv 2>%a@]@]@]"
        (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ",@;<1 0>")
           (fun ff (f,e) -> fprintf ff "@[<hv 2>'%s': %a@]" f (pretty_imp_expr 0 sym) e))
        field_arg_list
  | EJsonOpAccess field, [ e ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a)['%s']@]@]" (pretty_imp_expr 0 sym) e field
  | EJsonOpHasOwnProperty field, [ e ] ->
      fprintf ff "@[<hv 2>@[<hv 2>(%a).hasOwnProperty('%s')@]@]" (pretty_imp_expr 0 sym) e field
  | _ -> assert false
  end

let pretty_imp_ejson_runtime p sym pretty_imp_expr ff (op, args) =
  fprintf ff "@[<hv 2>%s(@[<hv 2>%a@])@]"
    (QUtil.string_of_ejson_runtime_op op)
    (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ",@;<1 0>") (pretty_imp_expr 0 sym)) args

let pretty_imp_ejson = pretty_imp pretty_imp_ejson_constant pretty_imp_ejson_op pretty_imp_ejson_runtime

(** Pretty NNRCMR *)

let pretty_fun sym ff (x, n) =
  fprintf ff "@[fun ($v%s) ->@ %a@]"
    x
    (pretty_nnrc_aux 0 sym) n

let pretty_default_fun sym ff n =
  fprintf ff "@[fun db_default() ->@ %a@]"
    (pretty_nnrc_aux 0 sym) n

let pretty_reduce_op_to_string op =
  begin match op with
  | RedOpCount -> "count"
  | RedOpSum typ -> "+"
  | RedOpMin typ -> "min"
  | RedOpMax typ -> "max"
  | RedOpArithMean typ -> "arithmean"
  | RedOpStats typ -> "stats"
  end

let pretty_nnrcmr_job_aux sym ff mr =
  let distributed = "distributed" in
  let scalar = "scalar" in
  let input_loc =
    begin match mr.mr_map with
    | MapDist _ -> distributed
    | MapDistFlatten _ -> distributed
    | MapScalar _ -> scalar
    end
  in
  let output_loc =
    begin match mr.mr_reduce with
    | RedId -> distributed
    | RedCollect _ -> scalar
    | RedOp _ -> scalar
    | RedSingleton -> scalar
    end
  in
  fprintf ff "@[<hv 0>input = $v%s : %s;@\n"
    mr.mr_input input_loc;
  fprintf ff "output = $v%s : %s;@\n"
    mr.mr_output output_loc;
  begin match mr.mr_map with
  | MapDist f -> fprintf ff "map(@[%a@]);" (pretty_fun sym) f
  | MapDistFlatten f -> fprintf ff "flatMap(@[%a@]);" (pretty_fun sym) f
  | MapScalar f -> fprintf ff "@[%a@];" (pretty_fun sym) f
  end;
  fprintf ff "@\n";
  begin match mr.mr_reduce with
  | RedId -> ()
  | RedCollect f -> fprintf ff "reduce(@[%a@]);" (pretty_fun sym) f
  | RedOp op ->
      let op_s = pretty_reduce_op_to_string (Obj.magic op)
      in
      fprintf ff "reduce(%s);" op_s
  | RedSingleton ->       fprintf ff "reduce(singleton);"
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
    fprintf ff "%s" x
  in
  let pretty_arg ff (x, loc) =
    begin match loc with
    | Vlocal ->  fprintf ff "(%s: Scalar)" x
    | Vdistr ->  fprintf ff "(%s: Distributed)" x
    end
  in
  fprintf ff "@[(fun (%a) => %a) (%a)@]"
    (pretty_list pretty_param ",") params
    (pretty_nnrc_aux 0 sym) n
    (pretty_list pretty_arg ",") args

let pretty_nnrcmr_aux sym ff mrl =
  pretty_mr_chain sym ff mrl.mr_chain;
  fprintf ff "@[%a@]" (pretty_mr_last sym) mrl.mr_last

let pretty_nnrcmr greek margin annot inheritance mr_chain =
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
  | DNNRCGetConstant (a, v) -> fprintf ff "%a$%s" ann a v
  | DNNRCVar (a, v) -> fprintf ff "%a$v%s" ann a v
  | DNNRCConst (a, d) -> fprintf ff "%a%a" ann a pretty_data d
  | DNNRCBinop (a, b,n1,n2) ->
      fprintf ff "%a(" ann a
        ; ((pretty_binary_op 0 sym (pretty_dnnrc_aux ann plug)) ff b n1 n2)
        ; fprintf ff ")"
  | DNNRCUnop (a,u,n1) ->
      fprintf ff "%a(" ann a
        ; ((pretty_unary_op 0 sym (pretty_dnnrc_aux ann plug)) ff u n1)
        ; fprintf ff ")"
  | DNNRCLet (a,v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>%a let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	      ann a
	      v
	      (pretty_dnnrc_aux ann plug p sym) n1
	      (pretty_dnnrc_aux ann plug p sym) n2
  | DNNRCFor (a,v,n1,n2) ->
      fprintf ff "@[<hv 0>%a{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	      ann a
	      (pretty_dnnrc_aux ann plug 0 sym) n2
	      v pretty_sym sym.sin
	      (pretty_dnnrc_aux ann plug 0 sym) n1
  | DNNRCIf (a,n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>%a if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	      ann a
	      (pretty_dnnrc_aux ann plug p sym) n1
	      (pretty_dnnrc_aux ann plug p sym) n2
	      (pretty_dnnrc_aux ann plug p sym) n3
  | DNNRCEither (a,n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>%a match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	      ann a
	      (pretty_dnnrc_aux ann plug p sym) n0
	      v1 (pretty_dnnrc_aux ann plug p sym) n1
	      v2 (pretty_dnnrc_aux ann plug p sym) n2
  | DNNRCCollect (a,n1) ->
      fprintf ff "@[%a%s[@[%a@]]@]"
	      ann a
	      "COLLECT"
	      (pretty_dnnrc_aux ann plug p sym) n1
  | DNNRCDispatch (a,n1) ->
      fprintf ff "@[%a%s[@[%a@]]@]"
	      ann a
	      "DISPATCH"
	      (pretty_dnnrc_aux ann plug p sym) n1
  | DNNRCAlg (a,body,arglist) ->
      fprintf ff "@[%adataframe(@[fun $%a => @] %a)@[(%a)@]@]"
	      ann a
        (pretty_list (fun ff s -> fprintf ff "%s" s) ",") (List.map fst arglist)
        plug body
	      (pretty_list (pretty_dnnrc_aux ann plug p sym) ",") (List.map snd arglist)
  | DNNRCGroupBy (a,g,atts,n1) ->
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
  | CCol v -> fprintf ff "%a%s%a" pretty_sym sym.langle v pretty_sym sym.rangle
  | CDot (v,c) -> pretty_unary_op p sym pretty_column_aux ff (OpDot v) c
  | CLit (d,rt) -> fprintf ff "@[%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle pretty_data d
  | CPlus (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff (OpNatBinary NatPlus) c1 c2
  | CEq (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff OpEqual c1 c2
  | CLessThan (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff OpLt c1 c2
  | CNeg c -> pretty_unary_op p sym pretty_column_aux ff OpNeg c
  | CToString c -> pretty_unary_op p sym pretty_column_aux ff OpToString c
  | CSConcat (c1,c2) -> pretty_binary_op p sym pretty_column_aux ff OpStringConcat c1 c2
  | CUDFCast (bs,c) -> pretty_unary_op p sym pretty_column_aux ff (OpCast bs) c
  | CUDFUnbrand (rt,c) -> fprintf ff "@[!%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle (pretty_column_aux p sym) c
  end

let pretty_named_column_aux p sym ff (name, col) =
  fprintf ff "%s%@%a" name (pretty_column_aux p sym) col

let rec pretty_dataframe_aux p sym ff ds =
  begin match ds with
  | DSVar v -> fprintf ff "$%s" v
  | DSSelect (cl,ds1) -> fprintf ff "@[select %a @[<hv 2>from %a@] @]"
				(pretty_list (pretty_named_column_aux p sym) ",") cl (pretty_dataframe_aux p sym) ds1
  | DSFilter (c,ds1) -> fprintf ff "@[filter %a @[<hv 2>from %a@] @]"
				(pretty_column_aux p sym) c (pretty_dataframe_aux p sym) ds1
  | DSCartesian (ds1,ds2) ->  pretty_binary_op p sym pretty_dataframe_aux ff OpRecConcat ds1 ds2
  | DSExplode (s,ds) -> fprintf ff "@[explode %s @[<hv 2>from %a@] @]" s (pretty_dataframe_aux p sym) ds
  end

let pretty_plug_dataframe greek ff a =
  let sym = if greek then greeksym else textsym in
  pretty_dataframe_aux 0 sym ff a

let pretty_dnnrc greek margin annot inheritance q =
  let ann = pretty_annotate_ignore in
  let plug = pretty_plug_dataframe greek in
  pretty_dnnrc_base ann plug greek margin annot q

(** Pretty tDNNRC *)

let pretty_dnnrc_typed greek margin annot inheritance q =
  let ann =
    if annot
    then pretty_annotate_annotated_rtype greek pretty_annotate_ignore
    else pretty_annotate_ignore
  in
  let plug = pretty_plug_dataframe greek in
  pretty_dnnrc_base ann plug greek margin annot q

(** Pretty JavaScript Ast *)

let pretty_js_ast greek margin annot inheritance q =
  "(* There is no pretty printer for JavaScript AST at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty JavaScript *)

let pretty_javascript greek margin annot inheritance q =
  q

(** Pretty Java *)

let pretty_java greek margin annot inheritance q =
  q

(** Pretty SparkDF *)

let pretty_spark_df greek margin annot inheritance q =
  q

(** Pretty WASM AST *)

let pretty_wasm_ast greek margin annot inheritance q =
  Wasm_ast.to_string q

let pretty_wasm greek margin annot inheritance q =
  q

(** Pretty Error *)

let pretty_error greek margin annot inheritance q =
  "Error: " ^ q

