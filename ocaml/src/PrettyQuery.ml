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

open PrettyCommon

open QcertCompiler.EnhancedCompiler
open QDriver

(** Pretty query wrapper *)

type 'a pretty_fun = bool -> int -> bool -> QData.json -> string -> 'a -> string
	
let pretty_query pconf (pretty_q:'a pretty_fun) (q:'a) =
  let greek = get_charset_bool pconf in
  let margin = get_margin pconf in
  let annot = get_type_annotations pconf in
  let hierarchy = get_hierarchy pconf in
  let harness = get_harness pconf in
  pretty_q greek margin annot hierarchy harness q

(** Pretty CAMPRule *)

let pretty_camp_rule greek margin annot hierarchy harness q =
  "(* There is no pretty printer for CAMPRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty TechRule *)

let pretty_tech_rule greek margin annot hierarchy harness q =
  "(* There is no pretty printer for TechRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty DesignerRule *)

let pretty_designer_rule greek margin annot hierarchy harness q =
  "(* There is no pretty printer for TechRule at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty CAMP *)

let pretty_camp greek margin annot hierarchy harness q =
  "(* There is no pretty printer for CAMP at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty OQL *)

let pretty_oql greek margin annot hierarchy harness q =
  "(* There is no pretty printer for OQL at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty SQL *)

let pretty_sql greek margin annot hierarchy harness q =
  "(* There is no pretty printer for SQL at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty SQL++ *)

let pretty_sqlpp greek margin annot hierarchy harness q =
  "(* There is no pretty printer for SQL++ at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty LambdaNRA *)

let pretty_lambda_nra greek margin annot hierarchy harness q =
  "(* There is no pretty printer for LambdaNRA at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty NRA *)

let rec pretty_nra_aux p sym ff a =
  match a with
  | QcertCompiler.AID -> fprintf ff "%s" "ID"
  | QcertCompiler.AConst d -> fprintf ff "%a" pretty_data d
  | QcertCompiler.ABinop (b,a1,a2) -> (pretty_binop p sym pretty_nra_aux) ff b a1 a2
  | QcertCompiler.AUnop (u,a1) -> (pretty_unop p sym pretty_nra_aux) ff u a1
  | QcertCompiler.AMap (a1,a2) -> pretty_nra_exp p sym sym.chi ff a1 (Some a2)
  | QcertCompiler.AMapConcat (a1,a2) -> pretty_nra_exp p sym sym.djoin ff a1 (Some a2)
  | QcertCompiler.AProduct (a1,a2) -> pretty_infix_exp p 5 sym pretty_nra_aux sym.times ff a1 a2
  | QcertCompiler.ASelect (a1,a2) -> pretty_nra_exp p sym sym.sigma ff a1 (Some a2)
  | QcertCompiler.ADefault (a1,a2) -> pretty_infix_exp p 8 sym pretty_nra_aux sym.bars ff a1 a2
  | QcertCompiler.AEither (a1,a2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ ID@;<1 -2>with@]@;<1 0>@[<hv 2>| left as ID ->@ %a@]@;<1 0>@[<hv 2>| right as ID ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	 (pretty_nra_aux p sym) a1
	 (pretty_nra_aux p sym) a2
  | QcertCompiler.AEitherConcat (a1,a2) -> pretty_infix_exp p 7 sym pretty_nra_aux sym.sqlrarrow ff a1 a2
  | QcertCompiler.AApp (a1,a2) -> pretty_infix_exp p 9 sym pretty_nra_aux sym.circ ff a1 a2
  | QcertCompiler.AGetConstant s -> fprintf ff "Table%a%s%a" pretty_sym sym.lfloor (Util.string_of_char_list s) pretty_sym sym.rfloor
  
(* resets precedence back to 0 *)
and pretty_nra_exp p sym thissym ff a1 oa2 =
  match oa2 with
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


let pretty_nra greek margin annot hierarchy harness q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nra_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty NRAEnv *)

let rec pretty_nraenv_aux p sym ff a =
  match a with
  | QcertCompiler.NRAEnvID -> fprintf ff "%s" "ID"
  | QcertCompiler.NRAEnvConst d -> fprintf ff "%a" pretty_data d
  | QcertCompiler.NRAEnvBinop (b,a1,a2) -> (pretty_binop p sym pretty_nraenv_aux) ff b a1 a2
  | QcertCompiler.NRAEnvUnop (u,a1) -> (pretty_unop p sym pretty_nraenv_aux) ff u a1
  | QcertCompiler.NRAEnvMap (a1,a2) -> pretty_nraenv_exp p sym sym.chi ff a1 (Some a2)
  | QcertCompiler.NRAEnvMapConcat (a1,a2) -> pretty_nraenv_exp p sym sym.djoin ff a1 (Some a2)
  | QcertCompiler.NRAEnvProduct (a1,a2) -> pretty_infix_exp p 5 sym pretty_nraenv_aux sym.times ff a1 a2
  | QcertCompiler.NRAEnvSelect (a1,a2) -> pretty_nraenv_exp p sym sym.sigma ff a1 (Some a2)
  | QcertCompiler.NRAEnvDefault (a1,a2) -> pretty_infix_exp p 8 sym pretty_nraenv_aux sym.bars ff a1 a2
  | QcertCompiler.NRAEnvEither (a1,a2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ ID@;<1 -2>with@]@;<1 0>@[<hv 2>| left as ID ->@ %a@]@;<1 0>@[<hv 2>| right as ID ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	 (pretty_nraenv_aux p sym) a1
	 (pretty_nraenv_aux p sym) a2
  | QcertCompiler.NRAEnvEitherConcat (a1,a2) -> pretty_infix_exp p 7 sym pretty_nraenv_aux sym.sqlrarrow ff a1 a2
  | QcertCompiler.NRAEnvApp (a1,a2) -> pretty_infix_exp p 9 sym pretty_nraenv_aux sym.circ ff a1 a2
  | QcertCompiler.NRAEnvGetConstant s -> fprintf ff "Table%a%s%a" pretty_sym sym.lfloor (Util.string_of_char_list s) pretty_sym sym.rfloor
  | QcertCompiler.NRAEnvEnv -> fprintf ff "%s" "ENV"
  | QcertCompiler.NRAEnvAppEnv (a1,a2) ->  pretty_infix_exp p 10 sym pretty_nraenv_aux sym.circe ff a1 a2
  | QcertCompiler.NRAEnvMapEnv a1 -> pretty_nraenv_exp p sym sym.chie ff a1 None
  | QcertCompiler.NRAEnvFlatMap (a1,a2) -> pretty_nraenv_exp p sym sym.chiflat ff a1 (Some a2)
  | QcertCompiler.NRAEnvJoin (a1,a2,a3) -> pretty_infix_dependent p 5 sym pretty_nraenv_aux sym.join ff a1 a2 a3
  | QcertCompiler.NRAEnvProject (atts,a1) ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.bpi (pretty_squared_names sym) atts (pretty_nraenv_aux 0 sym) a1
  | QcertCompiler.NRAEnvGroupBy (g,atts,a1) ->
      fprintf ff "@[<hv 0>%a%a%a(%a)@]" pretty_sym sym.gamma (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nraenv_aux 0 sym) a1
  | QcertCompiler.NRAEnvUnnest (a,b,a1) ->
      fprintf ff "@[<hv 0>%a%a(%a)@]" pretty_sym sym.rho (pretty_squared_names sym) [a;b] (pretty_nraenv_aux 0 sym) a1

(* resets precedence back to 0 *)
and pretty_nraenv_exp p sym thissym ff a1 oa2 =
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

and pretty_infix_dependent pouter pinner sym callb thissym ff a1 a2 a3 =
  if pouter > pinner
  then
    fprintf ff "@[<hov 0>(%a@ %a%a%a%a@ %a)@]" (callb pinner sym) a1 pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle (callb pinner sym) a2
  else
    fprintf ff "@[<hov 0>%a@ %a%a%a%a@ %a@]" (callb pinner sym) a1 pretty_sym thissym pretty_sym sym.langle (pretty_nraenv_aux 0 sym) a1 pretty_sym sym.rangle (callb pinner sym) a2


let pretty_nraenv greek margin annot hierarchy harness q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nraenv_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNRAEnv *)

let pretty_nraenv_core greek margin annot hierarchy harness q =
  pretty_nraenv greek margin annot hierarchy harness (QDriver.nraenv_core_to_nraenv q)
    
(** Pretty NNRC *)

let rec pretty_nnrc_aux p sym ff n =
  match n with
  | QcertCompiler.NNRCGetConstant v -> fprintf ff "$%s"  (Util.string_of_char_list v)
  | QcertCompiler.NNRCVar v -> fprintf ff "$v%s"  (Util.string_of_char_list v)
  | QcertCompiler.NNRCConst d -> fprintf ff "%a" pretty_data d
  | QcertCompiler.NNRCBinop (b,n1,n2) -> (pretty_binop p sym pretty_nnrc_aux) ff b n1 n2
  | QcertCompiler.NNRCUnop (u,n1) -> (pretty_unop p sym pretty_nnrc_aux) ff u n1
  | QcertCompiler.NNRCLet (v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	 (Util.string_of_char_list v)
	(pretty_nnrc_aux p sym) n1
	(pretty_nnrc_aux p sym) n2
  | QcertCompiler.NNRCFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	(pretty_nnrc_aux 0 sym) n2
	 (Util.string_of_char_list v) pretty_sym sym.sin
	(pretty_nnrc_aux 0 sym) n1
  | QcertCompiler.NNRCIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	(pretty_nnrc_aux p sym) n1
	(pretty_nnrc_aux p sym) n2
	(pretty_nnrc_aux p sym) n3
  | QcertCompiler.NNRCEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	(pretty_nnrc_aux p sym) n0
	 (Util.string_of_char_list v1) (pretty_nnrc_aux p sym) n1
	(Util.string_of_char_list v2) (pretty_nnrc_aux p sym) n2
  | QcertCompiler.NNRCGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrc_aux 0 sym) n1

let pretty_nnrc greek margin annot hierarchy harness q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrc_aux 0 sym) q;
    flush_str_formatter ()
  end

(** Pretty cNNRC *)

let pretty_nnrc_core greek margin annot hierarchy harness q =
  pretty_nnrc greek margin annot hierarchy harness q

(** Pretty NNRCMR *)

let pretty_fun sym ff (x, n) =
  fprintf ff "@[fun ($v%s) ->@ %a@]"
    (Util.string_of_char_list x)
    (pretty_nnrc_aux 0 sym) n

let pretty_default_fun sym ff n =
  fprintf ff "@[fun db_default() ->@ %a@]"
    (pretty_nnrc_aux 0 sym) n

let pretty_enhanced_numeric_type_to_prefix typ =
  match typ with
  | QcertCompiler.Enhanced_numeric_int -> ""
  | QcertCompiler.Enhanced_numeric_float -> "F"

let pretty_reduce_op_to_string op =
  match op with
  | QcertCompiler.RedOpCount -> "count"
  | QcertCompiler.RedOpSum typ -> "+"
  | QcertCompiler.RedOpMin typ -> "min"
  | QcertCompiler.RedOpMax typ -> "max"
  | QcertCompiler.RedOpArithMean typ -> "arithmean"
  | QcertCompiler.RedOpStats typ -> "stats"

let pretty_nnrcmr_job_aux sym ff mr =
  let distributed = "distributed" in
  let scalar = "scalar" in
  let input_loc =
    match mr.QcertCompiler.mr_map with
    | QcertCompiler.MapDist _ -> distributed
    | QcertCompiler.MapDistFlatten _ -> distributed
    | QcertCompiler.MapScalar _ -> scalar
  in
  let output_loc =
    match mr.QcertCompiler.mr_reduce with
    | QcertCompiler.RedId -> distributed
    | QcertCompiler.RedCollect _ -> scalar
    | QcertCompiler.RedOp _ -> scalar
    | QcertCompiler.RedSingleton -> scalar
  in
  fprintf ff "@[<hv 0>input = $v%s : %s;@\n"
    (Util.string_of_char_list mr.QcertCompiler.mr_input) input_loc;
  fprintf ff "output = $v%s : %s;@\n"
    (Util.string_of_char_list mr.QcertCompiler.mr_output) output_loc;
  begin match mr.QcertCompiler.mr_map with
    | QcertCompiler.MapDist f -> fprintf ff "map(@[%a@]);" (pretty_fun sym) f
    | QcertCompiler.MapDistFlatten f -> fprintf ff "flatMap(@[%a@]);" (pretty_fun sym) f
    | QcertCompiler.MapScalar f -> fprintf ff "@[%a@];" (pretty_fun sym) f
  end;
  fprintf ff "@\n";
  begin match mr.QcertCompiler.mr_reduce with
  | QcertCompiler.RedId -> ()
  | QcertCompiler.RedCollect f -> fprintf ff "reduce(@[%a@]);" (pretty_fun sym) f
  | QcertCompiler.RedOp op ->
     let op_s = pretty_reduce_op_to_string (Obj.magic op)
     in
      fprintf ff "reduce(%s);" op_s
  | QcertCompiler.RedSingleton ->       fprintf ff "reduce(singleton);"
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
    | QcertCompiler.Vlocal ->  fprintf ff "(%s: Scalar)" (Util.string_of_char_list x)
    | QcertCompiler.Vdistr ->  fprintf ff "(%s: Distributed)" (Util.string_of_char_list x)
  in
  fprintf ff "@[(fun (%a) => %a) (%a)@]@\n"
    (pretty_list pretty_param ",") params
    (pretty_nnrc_aux 0 sym) n
    (pretty_list pretty_arg ",") args

let pretty_nnrcmr_aux sym ff mrl =
  pretty_mr_chain sym ff mrl.QcertCompiler.mr_chain;
  fprintf ff "@[%a@]@\n" (pretty_mr_last sym) mrl.QcertCompiler.mr_last

let pretty_nnrcmr greek margin annot hierarchy harness mr_chain =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrcmr_aux sym) mr_chain;
    flush_str_formatter ()
  end

(** Pretty CldMR *)

let pretty_cldmr greek margin annot hierarchy harness q =
  "(* There is no pretty printer for CldMR at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty DNNRC *)

let rec pretty_dnnrc_aux ann plug p sym ff n =
  match n with
  | QcertCompiler.DNNRCGetConstant (a, v) -> fprintf ff "%a$%s" ann a (Util.string_of_char_list v)
  | QcertCompiler.DNNRCVar (a, v) -> fprintf ff "%a$v%s" ann a (Util.string_of_char_list v)
  | QcertCompiler.DNNRCConst (a, d) -> fprintf ff "%a%a" ann a pretty_data d
  | QcertCompiler.DNNRCBinop (a, b,n1,n2) ->
      fprintf ff "%a(" ann a
    ; ((pretty_binop 0 sym (pretty_dnnrc_aux ann plug)) ff b n1 n2)
    ; fprintf ff ")"
  | QcertCompiler.DNNRCUnop (a,u,n1) ->
     fprintf ff "%a(" ann a
    ; ((pretty_unop 0 sym (pretty_dnnrc_aux ann plug)) ff u n1)
    ; fprintf ff ")"
  | QcertCompiler.DNNRCLet (a,v,n1,n2) ->
     fprintf ff "@[<hv 0>@[<hv 2>%a let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	     ann a
	 (Util.string_of_char_list v)
	(pretty_dnnrc_aux ann plug p sym) n1
	(pretty_dnnrc_aux ann plug p sym) n2
  | QcertCompiler.DNNRCFor (a,v,n1,n2) ->
     fprintf ff "@[<hv 0>%a{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	     ann a
	(pretty_dnnrc_aux ann plug 0 sym) n2
	 (Util.string_of_char_list v) pretty_sym sym.sin
	(pretty_dnnrc_aux ann plug 0 sym) n1
  | QcertCompiler.DNNRCIf (a,n1,n2,n3) ->
     fprintf ff "@[<hv 0>@[<hv 2>%a if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	     ann a
	(pretty_dnnrc_aux ann plug p sym) n1
	(pretty_dnnrc_aux ann plug p sym) n2
	(pretty_dnnrc_aux ann plug p sym) n3
  | QcertCompiler.DNNRCEither (a,n0,v1,n1,v2,n2) ->
     fprintf ff "@[<hv 0>@[<hv 2>%a match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	     ann a
	(pretty_dnnrc_aux ann plug p sym) n0
	 (Util.string_of_char_list v1) (pretty_dnnrc_aux ann plug p sym) n1
	 (Util.string_of_char_list v2) (pretty_dnnrc_aux ann plug p sym) n2
  | QcertCompiler.DNNRCCollect (a,n1) ->
     fprintf ff "@[%a%s[@[%a@]]@]"
	     ann a
	     "COLLECT"
	(pretty_dnnrc_aux ann plug p sym) n1
  | QcertCompiler.DNNRCDispatch (a,n1) ->
     fprintf ff "@[%a%s[@[%a@]]@]"
	     ann a
	     "DISPATCH"
	     (pretty_dnnrc_aux ann plug p sym) n1
  | QcertCompiler.DNNRCAlg (a,body,arglist) ->
     fprintf ff "@[%adataframe(@[fun $%a => @] %a)@[(%a)@]@]"
	     ann a
             (pretty_list (fun ff s -> fprintf ff "%s" s) ",") (List.map (fun x -> (Util.string_of_char_list (fst x))) arglist)
             plug body
	     (pretty_list (pretty_dnnrc_aux ann plug p sym) ",") (List.map snd arglist)
  | QcertCompiler.DNNRCGroupBy (a,g,atts,n1) ->
      fprintf ff "@[<hv 2>%agroup by@ %a%a@[<hv 2>(%a)@]@]" ann a (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_dnnrc_aux ann plug 0 sym) n1

let pretty_dnnrc_base ann plug greek margin annot n =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_dnnrc_aux ann plug 0 sym) n;
    flush_str_formatter ()
  end

let pretty_annotate_ignore ff a = ()
let pretty_plug_ignore ff a = ()

let pretty_plug_nraenv greek ff a =
  let sym = if greek then greeksym else textsym in
  pretty_nraenv_aux 0 sym ff (nraenv_core_to_nraenv a)

(* Pretty Spark IR *)
let rec pretty_column_aux p sym ff col =
  match col with
  | QcertCompiler.CCol v -> fprintf ff "%a%s%a" pretty_sym sym.langle (Util.string_of_char_list v) pretty_sym sym.rangle
  | QcertCompiler.CDot (v,c) -> pretty_unop p sym pretty_column_aux ff (QcertCompiler.ADot v) c
  | QcertCompiler.CLit (d,rt) -> fprintf ff "@[%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle pretty_data d
  | QcertCompiler.CPlus (c1,c2) -> pretty_binop p sym pretty_column_aux ff (QcertCompiler.ABArith QcertCompiler.ArithPlus) c1 c2
  | QcertCompiler.CEq (c1,c2) -> pretty_binop p sym pretty_column_aux ff QcertCompiler.AEq c1 c2
  | QcertCompiler.CLessThan (c1,c2) -> pretty_binop p sym pretty_column_aux ff QcertCompiler.ALt c1 c2
  | QcertCompiler.CNeg c -> pretty_unop p sym pretty_column_aux ff QcertCompiler.ANeg c
  | QcertCompiler.CToString c -> pretty_unop p sym pretty_column_aux ff QcertCompiler.AToString c
  | QcertCompiler.CSConcat (c1,c2) -> pretty_binop p sym pretty_column_aux ff QcertCompiler.ASConcat c1 c2
  | QcertCompiler.CUDFCast (bs,c) -> pretty_unop p sym pretty_column_aux ff (QcertCompiler.ACast bs) c
  | QcertCompiler.CUDFUnbrand (rt,c) -> fprintf ff "@[!%a%a%a@](@[%a@])" pretty_sym sym.llangle (pretty_rtype_aux sym) rt pretty_sym sym.rrangle (pretty_column_aux p sym) c

let pretty_named_column_aux p sym ff (name, col) =
  fprintf ff "%s%@%a" (Util.string_of_char_list name) (pretty_column_aux p sym) col

let rec pretty_dataframe_aux p sym ff ds =
  match ds with
  | QcertCompiler.DSVar v -> fprintf ff "$%s" (Util.string_of_char_list v)
  | QcertCompiler.DSSelect (cl,ds1) -> fprintf ff "@[select %a @[<hv 2>from %a@] @]"
				      (pretty_list (pretty_named_column_aux p sym) ",") cl (pretty_dataframe_aux p sym) ds1
  | QcertCompiler.DSFilter (c,ds1) -> fprintf ff "@[filter %a @[<hv 2>from %a@] @]"
				      (pretty_column_aux p sym) c (pretty_dataframe_aux p sym) ds1
  | QcertCompiler.DSCartesian (ds1,ds2) ->  pretty_binop p sym pretty_dataframe_aux ff QcertCompiler.AConcat ds1 ds2
  | QcertCompiler.DSExplode (s,ds) -> fprintf ff "@[explode %s @[<hv 2>from %a@] @]" (Util.string_of_char_list s) (pretty_dataframe_aux p sym) ds

let pretty_dataframe greek margin annot ds =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_dataframe_aux 0 sym) ds;
    flush_str_formatter ()
  end

let pretty_plug_dataframe greek ff a =
  let sym = if greek then greeksym else textsym in
  pretty_dataframe_aux 0 sym ff a

let pretty_dnnrc greek margin annot hierarchy harness q =
  let ann = pretty_annotate_ignore in
  let plug = pretty_plug_dataframe greek in
  pretty_dnnrc_base ann plug greek margin annot q

(** Pretty tDNNRC *)

let pretty_dnnrc_typed greek margin annot hierarchy harness q =
  let ann =
    if annot
    then pretty_annotate_annotated_rtype greek pretty_annotate_ignore
    else pretty_annotate_ignore
  in
  let plug = pretty_plug_dataframe greek in
  pretty_dnnrc_base ann plug greek margin annot q
    
(** Pretty JavaScript *)

let pretty_javascript greek margin annot hierarchy harness q =
  Util.string_of_char_list q

(** Pretty Java *)

let pretty_java greek margin annot hierarchy harness q =
  Util.string_of_char_list q

(** Pretty SparkRDD *)

let pretty_spark_rdd greek margin annot hierarchy harness q =
  Util.string_of_char_list q

(** Pretty SparkDF *)

let pretty_spark_df greek margin annot hierarchy harness q =
  Util.string_of_char_list q

(** Pretty Cloudant *)

let pretty_cloudant greek margin annot hierarchy harness q =
  CloudantUtil.string_of_cloudant (CloudantUtil.add_harness_top harness hierarchy q)

(** Pretty CloudantWhisk *)

let pretty_cloudant_whisk greek margin annot hierarchy harness q =
  "(* There is no pretty printer for CloudantWhisk at the moment. *)\n"  (* XXX TODO XXX *)

(** Pretty Error *)

let pretty_error greek margin annot hierarchy harness q =
  "Error: "^(Util.string_of_char_list q)

