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

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token TOSTRING CASTTO IDENTITY NOT UNBRAND
%token WHEN RETURN
%token TRUE FALSE
%token IT IN ENV LET

%token PCONST
%token PMAP PASSERT PORELSE
%token PLEFT PRIGHT

%token EQUAL EQUALEQUAL PLUSEQUAL
%token SEMISEMI
%token AND
%token PLUSPLUS
%token TILDE DOT COLON
%token SHARPTICK
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token EOF

%start <Rule.rule> main
%type <Rule.rule -> Rule.rule> rule_rule

%%

main:
| r = rule EOF
    { r }

rule:
| RULERETURN p = pat
    { Rule.Coq_rule_return p }
| RULEWHEN p = pat SEMISEMI r = rule
    { Rule.Coq_rule_when (p,r) }
| RULENOT p = pat SEMISEMI r = rule
    { Rule.Coq_rule_not (p,r) }
| RULEGLOBAL p = pat SEMISEMI r = rule
    { Rule.Coq_rule_global (p,r) }

pat:
(* Parenthesized pattern *)
| LPAREN p = pat RPAREN
    { p }
(* CAMP pattern *)
| PCONST LPAREN d = data RPAREN
    { Pattern.Coq_pconst d }
| u = uop LPAREN p = pat RPAREN
    { Pattern.Coq_punop (u,p) }
| p1 = pat b = bop p2 = pat
    { Pattern.Coq_pbinop (b,p1,p2) }
| PMAP p = pat
    { Pattern.Coq_pmap p }
| PASSERT p = pat
    { Pattern.Coq_passert p }
| PORELSE p1 = pat p2 = pat
    { Pattern.Coq_porElse (p1,p2) }
| IT
    { Pattern.Coq_pit }
| LET ID EQUAL p1 = pat IN p2 = pat
    { Pattern.Coq_pletIt (p1,p2) }
| ENV
    { Pattern.Coq_penv }
| LET ENV PLUSEQUAL p1 = pat IN p2 = pat
    { Pattern.Coq_pletEnv (p1,p2) }
| PLEFT
    { Pattern.Coq_pleft }
| PRIGHT
    { Pattern.Coq_pright }
(* Macros pattern *)
| TOSTRING p = pat
    { PatternSugar.toString p }
| p1 = pat PLUSSPLUS p2 = pat
    { PatternSugar.stringConcat p1 p2 }
| SHARPTICK c = const
    { (Pattern.Coq_pconst c) }

data:
| TRUE
    { RData.Coq_dbool true }
| FALSE
    { RData.Coq_dbool false }
| i = INT
    { RData.Coq_dnat (Util.coq_Z_of_int i) }
| s = STRING
    { RData.Coq_dstring (Util.char_list_of_string s) }
| LBRACKET dl = datalist RBRACKET
    { RData.Coq_dcoll dl }
| LBRACKET rl = reclist RBRACKET
    { RData.Coq_drec rl }

datalist:
| 
    { [] }
| d = data
    { [d] }
| d = data SEMI dl = datalist
    { d :: dl }

reclist:
| 
    { [] }
| r = recatt
    { [r] }
| r = recatt SEMI rl = reclist
    { r :: rl }

recatt:
| a = STRING COLON d = data
    { (Util.char_list_of_string a, d) }
    
patlist:
| p = pat
    { p :: [] }
| p = pat SEMI pl = patlist
    { p :: pl }

stringlist:
| s = STRING
    { (Util.char_list_of_string s) :: [] }
| s = STRING SEMI v = stringlist
    { (Util.char_list_of_string s) :: v }

const:
| i = INT
    { RData.dconst RData.coq_ConstLiteral_nat (Util.coq_Z_of_int i) }
| s = STRING
    { RData.dconst RData.coq_ConstLiteral_string (Util.char_list_of_string s) }

bop:
| EQUALEQUAL
    { Ops.Binary.AEq }
| AND
    { Ops.Binary.AAnd }
| PLUSPLUS
    { Ops.Binary.ASConcat }

uop:
| IDENTITY
    { Ops.Unary.AIdOp }
| NOT
    { Ops.Unary.ANeg }
| TOSTRING
    { Ops.Unary.AToString }
| CASTTO LBRACKET s = stringlist RBRACKET
    { Ops.Unary.ACast s }
| DOT s = STRING
    { Ops.Unary.ADot (Util.char_list_of_string s) }
| UNBRAND
    { Ops.Unary.AUnbrand }

