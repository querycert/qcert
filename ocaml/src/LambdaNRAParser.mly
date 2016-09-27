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

  open Util
  open Compiler.EnhancedCompiler

  let resolve_nra_operator a le e =
    begin match a with
    | "map" -> LambdaNRA.lamap le e
    | "mapconcat" -> LambdaNRA.lamapconcat le e
    | "select" -> LambdaNRA.laselect le e
    | _ -> raise (CACo_Error ("[LambdaNRA Parser] " ^ a ^ " is not a valid operator"))
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
%token PLUS STAR MINUS
%token DOT ARROW COMMA COLON
%token LPAREN RPAREN
%token LCURLY RCURLY
%token EOF

%right EQUAL NEQUAL
%right PLUS MINUS
%right AND OR
%right STAR
%left NOT DOT ARROW

%start <Compiler.EnhancedCompiler.LambdaNRA.expr> main

%%

main:
| q = query EOF
    { q }

query:
| e = expr
    { e }

lambda_expr:
| v = IDENT EQUALGT e = expr
    { LambdaNRA.lalambda (Util.char_list_of_string v) e }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Constants *)
| NULL
    { LambdaNRA.laconst Data.dunit }
| i = INT
    { LambdaNRA.laconst (Data.dnat (Util.coq_Z_of_int i)) }
| f = FLOAT
    { LambdaNRA.laconst (Enhanced.Data.dfloat f) }
| s = STRING
    { LambdaNRA.laconst (Data.dstring (Util.char_list_of_string s)) }
(* Expressions *)
| v = IDENT
    { LambdaNRA.lavar (Util.char_list_of_string v) }
| e = expr DOT a = IDENT LCURLY le = lambda_expr RCURLY
    { resolve_nra_operator a le e }
| e = expr DOT a = IDENT
    { LambdaNRA.ladot (Util.char_list_of_string a) e }
| e = expr ARROW a = IDENT
    { LambdaNRA.laarrow (Util.char_list_of_string a) e }
| STRUCT LPAREN r = reclist RPAREN
    { LambdaNRA.lastruct r }
(* Unary operators *)
| NOT e1 = expr
    { LambdaNRA.launop Ops.Unary.aneg e1 }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { LambdaNRA.labinop Ops.Binary.aeq e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { LambdaNRA.launop Ops.Unary.aneg (LambdaNRA.labinop Ops.Binary.aeq e1 e2) }
| e1 = expr MINUS e2 = expr
    { LambdaNRA.labinop Ops.Binary.ZArith.aminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { LambdaNRA.labinop Ops.Binary.ZArith.aplus e1 e2 }
| e1 = expr STAR e2 = expr
    { LambdaNRA.labinop Ops.Binary.ZArith.amult e1 e2 }
| e1 = expr AND e2 = expr
    { LambdaNRA.labinop Ops.Binary.aand e1 e2 }
| e1 = expr OR e2 = expr
    { LambdaNRA.labinop Ops.Binary.aor e1 e2 }

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
    
