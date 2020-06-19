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

%{
  open Util
  open Core.EnhancedCompiler

  type lambda_or_expression =
  | ParsedLambda of QLambdaNRA.lambda_expr
  | ParsedExpr of QLambdaNRA.expr

  let resolve_one_lambda a el =
    begin match el with
    | [ParsedLambda le] -> le
    | _ -> raise (Qcert_Error ("[LambdaNRA Parser] " ^ a ^ " expecting one lambda"))
    end

  let resolve_one_expr a el =
    begin match el with
    | [ParsedExpr e] -> e
    | _ -> raise (Qcert_Error ("[LambdaNRA Parser] " ^ a ^ " expecting one expression"))
    end

  let resolve_nra_operator a el e0 =
    begin match a with
    | "map" -> QLambdaNRA.lamap (resolve_one_lambda a el) e0
    | "flatmap" -> QLambdaNRA.laflatmap (resolve_one_lambda a el) e0
    | "mapproduct" -> QLambdaNRA.lamapproduct (resolve_one_lambda a el) e0
    | "filter" -> QLambdaNRA.lafilter (resolve_one_lambda a el) e0
    | "product" -> QLambdaNRA.laproduct (resolve_one_expr a el) e0
    | "union" -> QLambdaNRA.labinop Core.OpBagUnion e0 (resolve_one_expr a el)
    | _ -> raise (Qcert_Error ("[LambdaNRA Parser] " ^ a ^ " is not a valid operator"))
    end

  let static_int e =
    begin match e with
    | Core.LNRAConst (Core.Dnat i) -> i
    | _ -> raise Not_found
    end
    
  let static_string e =
    begin match e with
    | Core.LNRAConst (Core.Dstring s) -> s
    | _ -> raise Not_found
    end
    
  let resolve_call fname el =
    begin match fname,el with
    | "not", [e] ->
	      QLambdaNRA.launop QOps.Unary.opneg e
    | "flatten", [e] ->
	      QLambdaNRA.launop QOps.Unary.opflatten e
    | "sum", [e] ->
	      QLambdaNRA.launop QOps.Unary.opnatsum e
    | "fsum", [e] ->
	      QLambdaNRA.launop QOps.Unary.opfloatsum e
    | "avg", [e] ->
	      QLambdaNRA.launop QOps.Unary.opnatmean e
    | "favg", [e] ->
	      QLambdaNRA.launop QOps.Unary.opfloatmean e
    | "count", [e] ->
	      QLambdaNRA.launop QOps.Unary.opcount e
    | "length", [e] ->
	      QLambdaNRA.launop QOps.Unary.oplength e
    | "max", [e] ->
	      QLambdaNRA.launop QOps.Unary.opnatmax e
    | "fmax", [e] ->
	      QLambdaNRA.launop QOps.Unary.opfloatmax e
    | "min", [e] ->
	      QLambdaNRA.launop QOps.Unary.opnatmin e
    | "fmin", [e] ->
	      QLambdaNRA.launop QOps.Unary.opfloatmin e
    | "toString", [e] ->
	      QLambdaNRA.launop QOps.Unary.optostring e
    | "nth", [e1;e2] ->
	      QLambdaNRA.labinop QOps.Binary.opbagnth e1 e2
    | "stringJoin", [e1;e2] ->
	      QLambdaNRA.labinop QOps.Binary.opstringjoin e1 e2
    | "like", [e1;e2] ->
	      let pat =
	        begin try static_string e1 with
	        | Not_found ->
	            raise (Qcert_Error
		                   ("First parameter of like should be a string constant"))
	        end
	      in
	      QLambdaNRA.launop (QOps.Unary.oplike pat) e2
    | "substring", [e1;e2] ->
	      let start =
	        begin try static_int e2 with
	        | Not_found ->
	            raise (Qcert_Error
		                   ("Second parameter of substring should be an integer constant"))
	        end
	      in
	      QLambdaNRA.launop (QOps.Unary.opsubstring start None) e1
    | "substring", [e1;e2;e3] ->
	      let start =
	        begin try static_int e2 with
	        | Not_found ->
	            raise (Qcert_Error
		                   ("Second parameter of substring should be an integer constant"))
	        end
	      in
	      let len =
	        begin try static_int e3 with
	        | Not_found ->
	            raise (Qcert_Error
		                   ("Third parameter of substring should be an integer constant"))
	        end
	      in
	      QLambdaNRA.launop (QOps.Unary.opsubstring start (Some len)) e1
    | _, _ ->
	      raise (Qcert_Error
		             ("Function " ^ fname ^ " with arity " ^ (string_of_int (List.length el)) ^ " unkonwn"))
    end
%}

%token NULL
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token OR AND NOT
%token STRUCT
%token EQUAL NEQUAL EQUALGT
%token GT LT
%token PLUS STAR MINUS
%token DOT ARROW COMMA COLON
%token LPAREN RPAREN
%token LCURLY RCURLY
%token EOF

%right EQUAL NEQUAL
%right GT LT
%right PLUS MINUS
%right AND OR
%right STAR
%left DOT ARROW

%start <Core.EnhancedCompiler.QLambdaNRA.expr> main

%%

main:
| q = query EOF
    { q }

query:
| e = expr
    { e }

lambda_expr:
| v = IDENT EQUALGT e = expr
    { QLambdaNRA.lalambda (char_list_of_string v) e }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Constants *)
| NULL
    { QLambdaNRA.laconst QData.dunit }
| i = INT
    { QLambdaNRA.laconst (QData.dnat (coq_Z_of_int i)) }
| f = FLOAT
    { QLambdaNRA.laconst (QData.dfloat f) }
| s = STRING
    { QLambdaNRA.laconst (QData.dstring (char_list_of_string s)) }
(* Call *)
| fn = IDENT LPAREN el = exprlist RPAREN
    { resolve_call fn el }
(* Expressions *)
| v = IDENT
    { QLambdaNRA.lavar (char_list_of_string v) }
| e = expr DOT a = IDENT LCURLY le = lambda_expr RCURLY
    { resolve_nra_operator a [ParsedLambda le] e }
| e = expr DOT a = IDENT
    { QLambdaNRA.ladot (char_list_of_string a) e }
| e = expr ARROW a = IDENT
    { QLambdaNRA.laarrow (char_list_of_string a) e }
| STRUCT LPAREN r = reclist RPAREN
    { QLambdaNRA.lastruct r }
| e = expr DOT a = IDENT LPAREN el=params RPAREN
    { resolve_nra_operator a el e }
(* Unary operators *)
| NOT LPAREN e1 = expr RPAREN
    { QLambdaNRA.launop QOps.Unary.opneg e1 }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { QLambdaNRA.labinop QOps.Binary.opequal e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { QLambdaNRA.launop QOps.Unary.opneg (QLambdaNRA.labinop QOps.Binary.opequal e1 e2) }
| e1 = expr GT e2 = expr
    { QLambdaNRA.launop QOps.Unary.opneg (QLambdaNRA.labinop QOps.Binary.ople e1 e2) }
| e1 = expr LT e2 = expr
    { QLambdaNRA.labinop QOps.Binary.oplt e1 e2 }
| e1 = expr MINUS e2 = expr
    { QLambdaNRA.labinop QOps.Binary.ZArith.opminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { QLambdaNRA.labinop QOps.Binary.ZArith.opplus e1 e2 }
| e1 = expr STAR e2 = expr
    { QLambdaNRA.labinop QOps.Binary.ZArith.opmult e1 e2 }
| e1 = expr AND e2 = expr
    { QLambdaNRA.labinop QOps.Binary.opand e1 e2 }
| e1 = expr OR e2 = expr
    { QLambdaNRA.labinop QOps.Binary.opor e1 e2 }

(* expression list *)
exprlist:
| 
    { [] }
| e = expr
    { [e] }
| e = expr COMMA el = exprlist
    { e :: el }

reclist:
| 
    { [] }
| r = recatt
    { [r] }
| r = recatt COMMA rl = reclist
    { r :: rl }

recatt:
| a = IDENT COLON e = expr
    { (char_list_of_string a, e) }
    
params:
| e = expr
  { [ParsedExpr e] }
|  LCURLY le = lambda_expr RCURLY
  { [ParsedLambda le] }
| e = expr COMMA el = params
  { (ParsedExpr e)::el }
|  LCURLY le = lambda_expr RCURLY COMMA el = params
  { (ParsedLambda le)::el }
