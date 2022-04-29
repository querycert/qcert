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
  open EnhancedCompiler.EnhancedCompiler
  open OQL

  let static_int e =
    begin match e with
    | OConst (Coq_dnat i) -> i
    | _ -> raise Not_found
    end
    
  let resolve_call fname el =
    begin match fname,el with
    | "not", [e] ->
	      QOQL.ounop QOps.Unary.opneg e
    | "flatten", [e] ->
	      QOQL.ounop QOps.Unary.opflatten e
    | "sum", [e] ->
	      QOQL.ounop QOps.Unary.opnatsum e
    | "fsum", [e] ->
	      QOQL.ounop QOps.Unary.opfloatsum e
    | "avg", [e] ->
	      QOQL.ounop QOps.Unary.opnatmean e
    | "favg", [e] ->
	      QOQL.ounop QOps.Unary.opfloatmean e
    | "count", [e] ->
	      QOQL.ounop QOps.Unary.opcount e
    | "length", [e] ->
	      QOQL.ounop QOps.Unary.oplength e
    | "max", [e] ->
	      QOQL.ounop QOps.Unary.opnatmax e
    | "min", [e] ->
	      QOQL.ounop QOps.Unary.opnatmin e
    | "toString", [e] ->
	      QOQL.ounop QOps.Unary.optostring e
    | "nth", [e1;e2] ->
	      QOQL.obinop QOps.Binary.opbagnth e1 e2
    | "stringJoin", [e1;e2] ->
	      QOQL.obinop QOps.Binary.opstringjoin e1 e2
    | "substring", [e1;e2] ->
	      let start =
	        begin try static_int e2 with
	        | Not_found ->
	            raise (Qcert_Error
		                   ("Second parameter of substring should be an integer constant"))
	        end
	      in
	      QOQL.ounop (QOps.Unary.opsubstring start None) e1
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
	      QOQL.ounop (QOps.Unary.opsubstring start (Some len)) e1
    | "date", [e] ->
        QOQL.ounop Enhanced.Ops.Unary.sql_date_from_string e
    | "getYear", [e] ->
        QOQL.ounop (Enhanced.Ops.Unary.sql_date_get_component Coq_sql_date_YEAR) e
    | "encode", [e] ->
        QOQL.ounop Enhanced.Ops.Unary.uri_encode e
    | "decode", [e] ->
        QOQL.ounop Enhanced.Ops.Unary.uri_decode e
    | _, _ ->
	      raise (Qcert_Error
		             ("Function " ^ fname ^ " with arity " ^ (string_of_int (List.length el)) ^ " unkonwn"))
    end

%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token SELECT DISTINCT FROM WHERE
%token AS IN

%token OR AND
%token NEW STRUCT BAG

%token NIL TRUE FALSE

%token EQUAL NEQUAL
%token LT GT LTEQ GTEQ
%token LTDOT GTDOT LTEQDOT GTEQDOT
%token PLUS STAR MINUS
%token PLUSDOT STARDOT MINUSDOT
%token DOT ARROW COMMA SEMI COLON
%token LPAREN RPAREN
%token EOF

%token DEFINE UNDEFINE

%right FROM IN WHERE
%right COMMA
%right AND OR
%right EQUAL NEQUAL
%right LT GT LTEQ GTEQ LTDOT GTDOT LTEQDOT GTEQDOT
%right PLUS MINUS PLUSDOT MINUSDOT
%right STAR STARDOT
%left DOT ARROW

%start <EnhancedCompiler.EnhancedCompiler.QOQL.program> main

%%

main:
| q = program EOF
    { q }

program:
| DEFINE v = IDENT AS e = query SEMI p = program 
  { QOQL.define v e p  }
| UNDEFINE v = IDENT SEMI p = program 
  { QOQL.undefine v p  }
| e = query
  { QOQL.query e }


query:
| e = expr
    { QOQL.tableify e }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Constants *)
| NIL
    { QOQL.oconst QData.dunit }
| TRUE
    { QOQL.oconst (QData.dbool true) }
| FALSE
    { QOQL.oconst (QData.dbool false) }
| i = INT
    { QOQL.oconst (QData.dnat (coq_Z_of_int i)) }
| f = FLOAT
    { QOQL.oconst (QData.dfloat f) }
| s = STRING
    { QOQL.oconst (QData.dstring s) }
(* Select from where ... *)
| SELECT e = expr FROM fc = from_clause 
    { QOQL.osfw (QOQL.oselect e) fc QOQL.otrue QOQL.onoorder }
| SELECT e = expr FROM fc = from_clause WHERE w = expr
    { QOQL.osfw (QOQL.oselect e) fc (QOQL.owhere w) QOQL.onoorder }
| SELECT DISTINCT e = expr FROM fc = from_clause
    { QOQL.osfw (QOQL.oselectdistinct e) fc QOQL.otrue QOQL.onoorder }
| SELECT DISTINCT e = expr FROM fc = from_clause WHERE w = expr
    { QOQL.osfw (QOQL.oselectdistinct e) fc (QOQL.owhere w) QOQL.onoorder }
(* Call *)
| fn = IDENT LPAREN el = exprlist RPAREN
    { resolve_call fn el }
(* Expressions *)
| v = IDENT
    { QOQL.ovar v }
| e = expr DOT a = IDENT
    { QOQL.odot a e }
| e = expr ARROW a = IDENT
    { QOQL.oarrow a e }
| STRUCT LPAREN r = reclist RPAREN
    { QOQL.ostruct r }
| NEW a = IDENT LPAREN r = reclist RPAREN  (* XXX Spec does not use `new` *)
    { QOQL.onew a r }
| BAG LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.opbag e }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { QOQL.obinop QOps.Binary.opequal e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { QOQL.ounop QOps.Unary.opneg (QOQL.obinop QOps.Binary.opequal e1 e2) }
| e1 = expr LT e2 = expr
    { QOQL.obinop QOps.Binary.oplt e1 e2 }
| e1 = expr LTEQ e2 = expr
    { QOQL.obinop QOps.Binary.ople e1 e2 }
| e1 = expr GT e2 = expr
    { QOQL.ounop QOps.Unary.opneg (QOQL.obinop QOps.Binary.ople e1 e2) }
| e1 = expr GTEQ e2 = expr
    { QOQL.ounop QOps.Unary.opneg (QOQL.obinop QOps.Binary.oplt e1 e2) }
| e1 = expr LTDOT e2 = expr
    { QOQL.obinop QOps.Binary.FloatArith.opfloatlt e1 e2 }
| e1 = expr LTEQDOT e2 = expr
    { QOQL.obinop QOps.Binary.FloatArith.opfloatle e1 e2 }
| e1 = expr GTDOT e2 = expr
    { QOQL.ounop QOps.Unary.opneg (QOQL.obinop QOps.Binary.FloatArith.opfloatle e1 e2) }
| e1 = expr GTEQDOT e2 = expr
    { QOQL.ounop QOps.Unary.opneg (QOQL.obinop QOps.Binary.FloatArith.opfloatlt e1 e2) }
| e1 = expr MINUS e2 = expr
    { QOQL.obinop QOps.Binary.ZArith.opminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { QOQL.obinop QOps.Binary.ZArith.opplus e1 e2 }
| e1 = expr STAR e2 = expr
    { QOQL.obinop QOps.Binary.ZArith.opmult e1 e2 }
| e1 = expr MINUSDOT e2 = expr
    { QOQL.obinop QOps.Binary.FloatArith.opfloatminus e1 e2 }
| e1 = expr PLUSDOT e2 = expr
    { QOQL.obinop QOps.Binary.FloatArith.opfloatplus e1 e2 }
| e1 = expr STARDOT e2 = expr
    { QOQL.obinop QOps.Binary.FloatArith.opfloatmult e1 e2 }
| e1 = expr AND e2 = expr
    { QOQL.obinop QOps.Binary.opand e1 e2 }
| e1 = expr OR e2 = expr
    { QOQL.obinop QOps.Binary.opor e1 e2 }

(* expression list *)
exprlist:
| 
    { [] }
| e = expr
    { [e] }
| e = expr COMMA el = exprlist
    { e :: el }

from_clause:
| v = IDENT IN e = expr
    { (QOQL.oin v e) :: [] }
| v = IDENT AS c = qname IN e = expr
    { (QOQL.oincast v c e) :: [] }
| v = IDENT IN e = expr COMMA fr = from_clause
    { (QOQL.oin v e) :: fr }
| v = IDENT AS c = qname IN e = expr COMMA fr = from_clause
    { (QOQL.oincast v c e) :: fr }

qname:
| i = IDENT
    { i }
| i = IDENT DOT q = qname
    { i ^ "." ^ q }

reclist:
| 
    { [] }
| r = recatt
    { [r] }
| r = recatt COMMA rl = reclist
    { r :: rl }

recatt:
| a = IDENT COLON e = expr
    { (a, e) }
    
