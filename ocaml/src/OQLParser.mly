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

%{
  open Compiler.EnhancedCompiler
%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token SELECT DISTINCT FROM WHERE
%token AS IN

%token OR AND NOT
%token STRUCT BAG
%token FLATTEN
%token FAVG AVG SUM FLOAT_SUM COUNT MIN MAX

%token NIL

%token EQUAL NEQUAL
%token LT GT LTEQ GTEQ
%token PLUS STAR MINUS
%token DOT ARROW COMMA SEMI COLON
%token LPAREN RPAREN
%token EOF

%token DEFINE UNDEFINE

%right FROM IN WHERE
%right COMMA
%right AND OR
%right EQUAL NEQUAL
%right LT GT LTEQ GTEQ
%right PLUS MINUS
%right STAR
%left DOT ARROW

%start <Compiler.EnhancedCompiler.QOQL.program> main

%%

main:
| q = program EOF
    { q }

program:
| DEFINE v = IDENT AS e = query SEMI p = program 
  { QOQL.define (Util.char_list_of_string v) e p  }
| UNDEFINE v = IDENT SEMI p = program 
  { QOQL.undefine (Util.char_list_of_string v) p  }
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
| i = INT
    { QOQL.oconst (QData.dnat (Util.coq_Z_of_int i)) }
| f = FLOAT
    { QOQL.oconst (Enhanced.Data.dfloat f) }
| s = STRING
    { QOQL.oconst (QData.dstring (Util.char_list_of_string s)) }
(* Select from where ... *)
| SELECT e = expr FROM fc = from_clause 
    { QOQL.osfw (QOQL.oselect e) fc QOQL.otrue QOQL.onoorder }
| SELECT e = expr FROM fc = from_clause WHERE w = expr
    { QOQL.osfw (QOQL.oselect e) fc (QOQL.owhere w) QOQL.onoorder }
| SELECT DISTINCT e = expr FROM fc = from_clause
    { QOQL.osfw (QOQL.oselectdistinct e) fc QOQL.otrue QOQL.onoorder }
| SELECT DISTINCT e = expr FROM fc = from_clause WHERE w = expr
    { QOQL.osfw (QOQL.oselectdistinct e) fc (QOQL.owhere e) QOQL.onoorder }
(* Expressions *)
| v = IDENT
    { QOQL.ovar (Util.char_list_of_string v) }
| e = expr DOT a = IDENT
    { QOQL.odot (Util.char_list_of_string a) e }
| e = expr ARROW a = IDENT
    { QOQL.oarrow (Util.char_list_of_string a) e }
| STRUCT LPAREN r = reclist RPAREN
    { QOQL.ostruct r }
| BAG LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.acoll e }
(* Functions *)
| NOT LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.aneg e }
| FLATTEN LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.aflatten e }
| SUM LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.asum e }
| FLOAT_SUM LPAREN e = expr RPAREN
    { QOQL.ounop Enhanced.Ops.Unary.float_sum e }
| AVG LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.aarithmean e }
| FAVG LPAREN e = expr RPAREN
    { QOQL.ounop (Compiler.AForeignUnaryOp (Obj.magic (Compiler.Enhanced_unary_float_op (Compiler.Uop_float_arithmean)))) e }
| COUNT LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.acount e }
| MAX LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.anummax e }
| MIN LPAREN e = expr RPAREN
    { QOQL.ounop QOps.Unary.anummin e }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { QOQL.obinop QOps.Binary.aeq e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { QOQL.ounop QOps.Unary.aneg (QOQL.obinop QOps.Binary.aeq e1 e2) }
| e1 = expr LT e2 = expr
    { QOQL.obinop QOps.Binary.alt e1 e2 }
| e1 = expr LTEQ e2 = expr
    { QOQL.obinop QOps.Binary.ale e1 e2 }
| e1 = expr GT e2 = expr
    { QOQL.ounop QOps.Unary.aneg (QOQL.obinop QOps.Binary.ale e1 e2) }
| e1 = expr GTEQ e2 = expr
    { QOQL.ounop QOps.Unary.aneg (QOQL.obinop QOps.Binary.alt e1 e2) }
| e1 = expr MINUS e2 = expr
    { QOQL.obinop QOps.Binary.ZArith.aminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { QOQL.obinop QOps.Binary.ZArith.aplus e1 e2 }
| e1 = expr STAR e2 = expr
    { QOQL.obinop QOps.Binary.ZArith.amult e1 e2 }
| e1 = expr AND e2 = expr
    { QOQL.obinop QOps.Binary.aand e1 e2 }
| e1 = expr OR e2 = expr
    { QOQL.obinop QOps.Binary.aor e1 e2 }

from_clause:
| v = IDENT IN e = expr
    { (QOQL.oin (Util.char_list_of_string v) e) :: [] }
| v = IDENT AS c = qname IN e = expr
    { (QOQL.oincast (Util.char_list_of_string v) (Util.char_list_of_string c) e) :: [] }
| v = IDENT IN e = expr COMMA fr = from_clause
    { (QOQL.oin (Util.char_list_of_string v) e) :: fr }
| v = IDENT AS c = qname IN e = expr COMMA fr = from_clause
    { (QOQL.oincast (Util.char_list_of_string v) (Util.char_list_of_string c) e) :: fr }

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
    { (Util.char_list_of_string a, e) }
    
