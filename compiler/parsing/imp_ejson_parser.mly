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
  open EJson
  open Imp
  open ImpEJson
  open EJsonOperators
  open EJsonRuntimeOperators
  open EnhancedCompiler.EnhancedCompiler

  let runtime_call mname fname =
    if (mname = "Runtime")
    then
      begin match QUtil.ejson_runtime_op_of_string fname with
      | Some op -> op
      | None ->raise (Qcert_Error ("Call to " ^ mname ^ "." ^ fname ^ " unknown"))
      end
    else
	    raise (Qcert_Error ("Call to " ^ mname ^ "." ^ fname ^ " unkonwn"))
%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token NULL
%token TRUE FALSE
%token EQUAL COLON COLONEQUAL
%token SEMI COMMA
%token DOT
%token LPAREN RPAREN
%token LCURLY RCURLY
%token LBRACKET RBRACKET
%token PLUS STAR MINUS SLASH
%token LT GT LTEQ GTEQ

%token LET IF THEN ELSE TO MODULE IN RETURN FOR FAILWITH

%token EOF

%right LT GT LTEQ GTEQ
%right PLUS MINUS
%right STAR SLASH

%start <(EnhancedRuntime.EnhancedRuntime.compiler_foreign_ejson_model,EnhancedEJson.enhanced_foreign_ejson_runtime_op) ImpEJson.imp_ejson> main

%%

main:
| m = imodule EOF
    { m }

imodule:
| MODULE mname = IDENT LCURLY fs = ifunctions RCURLY
      { fs } (* XXX module name is ignored *)

ifunctions:
|
    { [] }
| f = ifunction fs = ifunctions
    { f :: fs }

ifunction:
| fname = IDENT LPAREN aname = IDENT RPAREN RETURN rname = IDENT b = block
    { (fname,ImpFun (aname,b,rname)) }

block:
| LCURLY ds = decls ss = stmts RCURLY
    { ImpStmtBlock (ds,ss) }

stmt:
| b = block
    { b }
| vname = IDENT COLONEQUAL e = expr SEMI
    { ImpStmtAssign (vname,e) }
| FOR LPAREN vname = IDENT IN e = expr RPAREN s = stmt
    { ImpStmtFor (vname,e,s) }
| FOR LPAREN vname = IDENT EQUAL e1 = expr TO e2 = expr RPAREN s = stmt
    { ImpStmtForRange (vname,e1,e2,s) }
| IF e = expr THEN s1 = stmt ELSE s2 = stmt
    { ImpStmtIf (e,s1,s2) }

stmts:
|
    { [] }
| s = stmt ss = stmts
    { s :: ss }

decls:
|
    { [] }
| d = decl ds = decls
    { d :: ds }

decl:
| LET vname = IDENT SEMI
    { (vname, None) }
| LET vname = IDENT COLONEQUAL e = expr SEMI
    { (vname, Some e) }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Failure *)
| FAILWITH s = STRING
    { ImpExprError s }
(* Constants *)
| NULL
    { ImpExprConst Coq_cejnull }
| f = FLOAT
    { ImpExprConst (Coq_cejnumber f) }
| i = INT
    { ImpExprConst (Coq_cejbigint i) }
| TRUE
    { ImpExprConst (Coq_cejbool true) }
| FALSE
    { ImpExprConst (Coq_cejbool false) }
| s = STRING
    { ImpExprConst (Coq_cejstring s) }
(* Constructors *)
| LBRACKET es = exprs RBRACKET (* Arrays *)
    { ImpExprRuntimeCall (EJsonRuntimeArray,es) }
| LCURLY ps = pairs RCURLY (* Object *)
    { let (anames,es) = ps in ImpExprOp (EJsonOpObject anames,es) }
(* Operator *)
| e1 = expr PLUS e2 = expr
    { ImpExprOp (EJsonOpAddNumber,[e1;e2]) }
| e1 = expr MINUS e2 = expr
    { ImpExprOp (EJsonOpSub,[e1;e2]) }
| e1 = expr STAR e2 = expr
    { ImpExprOp (EJsonOpMult,[e1;e2]) }
| e1 = expr SLASH e2 = expr
    { ImpExprOp (EJsonOpDiv,[e1;e2]) }
| e1 = expr LT e2 = expr
    { ImpExprOp (EJsonOpLt,[e1;e2]) }
| e1 = expr GT e2 = expr
    { ImpExprOp (EJsonOpGt,[e1;e2]) }
| e1 = expr LTEQ e2 = expr
    { ImpExprOp (EJsonOpLe,[e1;e2]) }
| e1 = expr GTEQ e2 = expr
    { ImpExprOp (EJsonOpGe,[e1;e2]) }
(* Call *)
| mname = IDENT DOT fname = IDENT LPAREN el = exprs RPAREN
    { ImpExprRuntimeCall (runtime_call mname fname, el) }
(* Expressions *)
| vname = IDENT
    { ImpExprVar vname }

exprs:
| 
    { [] }
| e = expr
    { e :: [] }
| e = expr COMMA es = exprs
    { e :: es }

pairs:
| 
    { ([],[]) }
| aname = IDENT COLON e = expr
    { (aname :: [], e :: []) }
| aname = IDENT COLON e = expr COMMA ps = pairs
    { let (anames,es) = ps in
      (aname :: anames, e :: es) }

