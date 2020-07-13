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
      begin match fname with
      | "equal" -> EJsonRuntimeEqual
      | "compare" -> EJsonRuntimeCompare
      | "dot" -> EJsonRuntimeRecDot
      | "either" -> EJsonRuntimeEither
      | "toLeft" -> EJsonRuntimeToLeft
      | "toRight" -> EJsonRuntimeToRight
      | _ ->
	        raise (Qcert_Error ("Runtime call " ^ mname ^ "." ^ fname ^ " unkonwn"))
      end
    else
	    raise (Qcert_Error ("Runtime call " ^ mname ^ "." ^ fname ^ " unkonwn"))
%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token NULL
%token TRUE FALSE
%token EQUAL COLONEQUAL
%token SEMI COMMA
%token DOT
%token LPAREN RPAREN
%token LCURLY RCURLY

%token LET IF THEN ELSE TO DEFINE IN RETURN FOR FAILWITH

%token EOF

%start <ImpEJson.imp_ejson> main

%%

main:
| m = imodule EOF
    { m }

imodule:
| f = ifunction
    { [f] }

ifunction:
| DEFINE fname = IDENT LPAREN aname = IDENT RPAREN RETURN rname = IDENT LCURLY s = stmt RCURLY
    { (char_list_of_string fname,ImpFun (char_list_of_string aname,s,char_list_of_string rname)) }

stmt:
| LCURLY ds = decls ss = stmts RCURLY
    { ImpStmtBlock (ds,ss) }
| vname = IDENT COLONEQUAL e = expr SEMI
    { ImpStmtAssign (char_list_of_string vname,e) }
| FOR LPAREN vname = IDENT IN e = expr RPAREN s = stmt
    { ImpStmtFor (char_list_of_string vname,e,s) }
| FOR LPAREN vname = IDENT EQUAL e1 = expr TO e2 = expr RPAREN s = stmt
    { ImpStmtForRange (char_list_of_string vname,e1,e2,s) }
| IF e = expr THEN s1 = stmt ELSE s2 = stmt
    { ImpStmtIf (e,s1,s2) }

stmts:
|
    { [] }
| s = stmt SEMI ss = stmts
    { s :: ss }

decls:
|
    { [] }
| d = decl SEMI ds = decls
    { d :: ds }

decl:
| LET vname = IDENT SEMI
    { (char_list_of_string vname, None) }
| LET vname = IDENT COLONEQUAL e = expr SEMI
    { (char_list_of_string vname, Some e) }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
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
    { ImpExprConst (Coq_cejstring (char_list_of_string s)) }
(* Failure *)
| FAILWITH s = STRING
    { ImpExprError (char_list_of_string s) }
(* Call *)
| mname = IDENT DOT fname = IDENT LPAREN el = exprs RPAREN
    { ImpExprRuntimeCall (runtime_call mname fname,el) }
(* Expressions *)
| vname = IDENT
    { ImpExprVar  (char_list_of_string vname) }

exprs:
| 
    { [] }
| e = expr
    { e :: [] }
| e = expr COMMA es = exprs
    { e :: es }

