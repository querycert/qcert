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
  open QcertExtracted
  open QcertCompiler.EnhancedCompiler
%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token DUNIT DNAT DFLOAT DBOOL DSTRING
%token DCOLL DREC
%token DLEFT DRIGHT DBRAND
%token DTIMESCALE

%token SECOND MINUTE HOUR DAY WEEK MONTH YEAR

%token PCONST PUNOP PBINOP
%token PMAP PASSERT PORELSE
%token PIT PLETIT PENV PLETENV
%token PLEFT PRIGHT PGETCONSTANT
%token TRUE FALSE

%token WHERE INSTANCEOF MATCHES EXAMPLE
%token TEMPVAR FETCH KEY
%token IS AGGREGATE DO OVER FLATTEN VARIABLES
%token PACCEPT PBDOT PBSOMEDOT PSOME PNULL PLUSSPLUS PBINOPRED
%token PVARWITH WITHVAR LOOKUP TOSTRING

%token FLOATNEG FLOATSQRT FLOATEXP
%token FLOATLOG FLOATLOG10
%token FLOATOFINT FLOATCEIL FLOATFLOOR FLOATTRUNCATE
%token FLOATABS

%token FLOATPLUS FLOATMINUS FLOATMULT FLOATDIV
%token FLOATPOW FLOATMIN FLOATMAX
(* %token FLOATNE FLOATLT FLOATLE FLOATGT FLOATGE *)

%token AFLOATSUM AFLOATARITHMEAN AFLOATLISTMIN AFLOATLISTMAX

%token TIMEAS TIMESHIFT
%token TIMENE TIMELT TIMELE TIMEGT TIMEGE
%token TIMEDURATIONFROMSCALE TIMEDURATIONBETWEEN

%token SQLDATEPLUS SQLDATEMINUS
%token SQLDATENE SQLDATELT SQLDATELE SQLDATEGT SQLDATEGE
%token SQLDATEINTERVALBETWEEN

%token TIMEFROMSTRING TIMEDURATIONFROMSTRING

%token SQLDATEFROMSTRING SQLDATEINTERVALFROMSTRING
%token SQLGETDATECOMPONENT

%token PNOW

%token AEQ AUNION ACONCAT AMERGECONCAT AAND AOR ALT ALE AMINUS AMIN AMAX ACONTAINS ASCONCAT
%token ABARITH ARITHPLUS ARITHMINUS ARITHMULT ARITHMIN ARITHMAX ARITHDIVIDE ARITHREM
%token AIDOP ANEG ACOLL ACOUNT AFLATTEN ADISTINCT ASUM ATOSTRING ASUBSTRING ALIKE ESCAPE ANUMMIN ANUMMAX AARITHMEAN ACAST ADOT AREC ARECPROJECT AUNBRAND ASINGLETON
%token AUARITH ARITHABS ARITHLOG2 ARITHSQRT
%token RULEWHEN RULEGLOBAL RULERETURN RULENOT
%token COMMA
%token SEMI
%token SEMISEMI
%token SEMISEMISEMI
%token COLONEQUAL DOT
%token DASHTICK DASHUNDER
%token BANGDASHARROW
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token EOF

%nonassoc UINSTANCE
%nonassoc PORELSE
%nonassoc PLETIT PLETENV
%nonassoc PMAP
%nonassoc PBINOP PUNOP
%right PLUSSPLUS
%left PBSOMEDOT PBDOT
%nonassoc BANGDASHARROW
%nonassoc UIS
%right TEMPVAR UFETCH
%nonassoc TOSTRING
%nonassoc UWITHVAR
%nonassoc PASSERT

%start <(string * QcertExtracted.QcertCompiler.EnhancedCompiler.QLang.camp_rule)> rulemain
%start <(string * QcertExtracted.QcertCompiler.EnhancedCompiler.QLang.camp)> campmain
%type <QcertExtracted.QcertCompiler.EnhancedCompiler.QLang.camp_rule -> QcertExtracted.QcertCompiler.EnhancedCompiler.QLang.camp_rule> rule_rule

%%

rulemain:
| EXAMPLE i=IDENT COLONEQUAL r = rule DOT EOF
    { (i, r) }

campmain:
| EXAMPLE i=IDENT COLONEQUAL p = camp DOT EOF
    { (i, p) }

rule:
| p = camp (* This allows pure CAMP tests to be compiled as rules *)
    { QCAMPRule.rule_match p }
| RULERETURN p = camp
    { QCAMPRule.rule_return p }
| RULEWHEN p = camp SEMISEMI r = rule
    { QCAMPRule.rule_when p r }
| RULENOT p = camp SEMISEMI r = rule
    { QCAMPRule.rule_not p r }
| RULEGLOBAL p = camp SEMISEMI r = rule
    { QCAMPRule.rule_global p r }

rule_rule:
| RULEWHEN p = camp
    { (fun r -> QCAMPRule.rule_when p r) }
| RULENOT p = camp
    { (fun r -> QCAMPRule.rule_not p r) }
| RULEGLOBAL p = camp
    { (fun r -> QCAMPRule.rule_global p r) }
| RULEWHEN p = camp SEMISEMISEMI r = rule_rule 
    { (fun r1 -> (QCAMPRule.rule_when p (r r1))) }
| RULENOT p = camp SEMISEMISEMI r = rule_rule
    { (fun r1 -> (QCAMPRule.rule_not p (r r1))) }
| RULEGLOBAL p = camp SEMISEMISEMI r = rule_rule
    { (fun r1 -> (QCAMPRule.rule_global p (r r1))) }

camp:
(* Parenthesized pattern *)
| LPAREN p = camp RPAREN
    { p }
(* CAMP pattern *)
| PCONST DUNIT
    { QCAMP.pconst QData.dunit }
| PCONST LPAREN d = data RPAREN
    { QCAMP.pconst d }
| PUNOP u = uop p = camp
    { QCAMP.punop u p }
| PBINOP b = bop p1 = camp p2 = camp
    { QCAMP.pbinop b p1 p2 }
| PMAP p = camp
    { QCAMP.pmap p }
| PASSERT p = camp
    { QCAMP.passert p }
| PORELSE p1 = camp p2 = camp
    { QCAMP.porelse p1 p2 }
| PIT
    { QCAMP.pit }
| PLETIT p1 = camp p2 = camp
    { QCAMP.pletit p1 p2 }
| PENV
    { QCAMP.penv }
| PLETENV p1 = camp p2 = camp
    { QCAMP.pletenv  p1 p2 }
| PLEFT
    { QCAMP.pleft }
| PRIGHT
    { QCAMP.pright }
| PGETCONSTANT s = STRING
    { QCAMP.pgetConstant (Util.char_list_of_string s) }
(* Macros pattern *)
| PNOW
    { QCAMP.pnow }
| PACCEPT
    { QCAMP.pconst (QData.drec []) }
| LOOKUP s = STRING
    { QCAMP.lookup (Util.char_list_of_string s) }
 | v = STRING IS p = camp %prec UIS
    { QCAMP.pIS (Util.char_list_of_string v) p }
| WITHVAR s = STRING p = camp %prec UWITHVAR
    { QCAMP.withVar (Util.char_list_of_string s) p }
| PVARWITH s = STRING p = camp %prec UWITHVAR
    { QCAMP.pvarwith (Util.char_list_of_string s) p }
| TOSTRING p = camp
    { QCAMP.toString p }
| PBINOPRED b = bop LBRACKET pl = camplist RBRACKET
    { QCAMP.camp_binop_reduce b pl }
| p1 = camp PLUSSPLUS p2 = camp
    { QCAMP.stringConcat p1 p2 }
| DASHUNDER
    { QCAMP.pit }
| DASHTICK c = const
    { (QCAMP.pconst c) }
| s = STRING BANGDASHARROW p = camp
    { QCAMP.pbdot (Util.char_list_of_string s) p }
| PBDOT s = STRING p = camp %prec PBDOT
    { QCAMP.pbdot (Util.char_list_of_string s) p }
| PBSOMEDOT s = STRING p = camp %prec PBSOMEDOT
    { QCAMP.pbsomedot (Util.char_list_of_string s) p }
| PSOME
    { QCAMP.pleft }
| PNULL
    { QCAMP.pnull }
(* INSTANCEOF, FETCH, and MATCHES temporarily have hacks because of signature changes in RuleSugar.v.  TODO fix this *)
| n = STRING INSTANCEOF LBRACKET t = stringlist RBRACKET WHERE p = camp %prec UINSTANCE
    { QCAMPRule.instanceOf (Util.char_list_of_string n) t p }
| p = camp TEMPVAR t = STRING FETCH LBRACKET e = stringlist RBRACKET KEY a = STRING DO pcont = camp %prec UFETCH
    { QCAMPRule.fetchRef e (Util.char_list_of_string a) (Util.char_list_of_string t) p pcont }
| MATCHES LBRACKET t = stringlist RBRACKET WHERE p = camp %prec UINSTANCE
    { QCAMPRule.matches t p }
| AGGREGATE r = rule_rule DO u = uop OVER p = camp FLATTEN f = INT
    { QCAMPRule.aggregate r u p (Util.coq_Z_of_int f) }
| VARIABLES LBRACKET v = stringlist RBRACKET
    { QCAMP.returnVariables v }
data:
| DUNIT
    { QData.dunit }
| DBOOL TRUE
    { QData.dbool true }
| DBOOL FALSE
    { QData.dbool false }
| DFLOAT f = FLOAT
    { QData.dfloat f }
| DNAT i = INT
    { QData.dnat (Util.coq_Z_of_int i) }
| DSTRING s = STRING
    { QData.dstring (Util.char_list_of_string s) }
| DCOLL LBRACKET dl = datalist RBRACKET
    { QData.dcoll dl }
| DREC LBRACKET rl = reclist RBRACKET
    { QData.drec rl }
| DLEFT d = data
    { QData.dleft d }
| DRIGHT d = data
    { QData.dright d }
| DBRAND sl = stringlist d = data
    { QData.dbrand sl d }
| DTIMESCALE ts = timescale
    { Enhanced.Data.dtime_scale ts }

timescale:
| SECOND
  {Enhanced.Data.second}
| MINUTE
  {Enhanced.Data.minute}
| HOUR
  {Enhanced.Data.hour}
| DAY
  {Enhanced.Data.day}
| WEEK
  {Enhanced.Data.week}
| MONTH
  {Enhanced.Data.month}
| YEAR
  {Enhanced.Data.year}

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
| LPAREN a = STRING COMMA d = data RPAREN
    { (Util.char_list_of_string a, d) }
    
camplist:
| p = camp
    { p :: [] }
| p = camp SEMI pl = camplist
    { p :: pl }

stringlist:
| s = STRING
    { (Util.char_list_of_string s) :: [] }
| s = STRING SEMI v = stringlist
    { (Util.char_list_of_string s) :: v }

const:
| i = INT
    { QData.dnat (Util.coq_Z_of_int i) }
| f = FLOAT
    { QData.dfloat f }
| s = STRING
    { QData.dstring (Util.char_list_of_string s) }
| TRUE
    { QData.dbool true }
| FALSE
    { QData.dbool false }

bop:
| FLOATPLUS
  { QOps.Binary.FloatArith.opfloatplus }
| FLOATMINUS
  { QOps.Binary.FloatArith.opfloatminus }
| FLOATMULT
  { QOps.Binary.FloatArith.opfloatmult }
| FLOATDIV
  { QOps.Binary.FloatArith.opfloatdiv }
| FLOATPOW
  { QOps.Binary.FloatArith.opfloatpow }
| FLOATMIN
  { QOps.Binary.FloatArith.opfloatmin }
| FLOATMAX
  { QOps.Binary.FloatArith.opfloatmax }

| TIMEAS
  { Enhanced.Ops.Binary.time_as }
| TIMESHIFT
  { Enhanced.Ops.Binary.time_shift }
| TIMENE
  { Enhanced.Ops.Binary.time_ne }
| TIMELT
  { Enhanced.Ops.Binary.time_lt }
| TIMELE
  { Enhanced.Ops.Binary.time_le }
| TIMEGT
  { Enhanced.Ops.Binary.time_gt }
| TIMEGE
  { Enhanced.Ops.Binary.time_ge }
| TIMEDURATIONFROMSCALE
  { Enhanced.Ops.Binary.time_duration_from_scale }
| TIMEDURATIONBETWEEN
  { Enhanced.Ops.Binary.time_duration_between }
| SQLDATEPLUS
  { Enhanced.Ops.Binary.sql_date_plus }
| SQLDATEMINUS
  { Enhanced.Ops.Binary.sql_date_minus }
| SQLDATENE
  { Enhanced.Ops.Binary.sql_date_ne }
| SQLDATELT
  { Enhanced.Ops.Binary.sql_date_lt }
| SQLDATELE
  { Enhanced.Ops.Binary.sql_date_le }
| SQLDATEGT
  { Enhanced.Ops.Binary.sql_date_gt }
| SQLDATEGE
  { Enhanced.Ops.Binary.sql_date_ge }
| SQLDATEINTERVALBETWEEN
  { Enhanced.Ops.Binary.sql_date_interval_between }
| AEQ
    { QOps.Binary.opequal }
| AUNION
    { QOps.Binary.opbagunion }
| ACONCAT
    { QOps.Binary.oprecconcat }
| AMERGECONCAT
    { QOps.Binary.oprecmerge }
| AAND
    { QOps.Binary.opand }
| AOR
    { QOps.Binary.opor }
| ALT
    { QOps.Binary.oplt }
| ALE
    { QOps.Binary.ople }
| AMINUS
    { QOps.Binary.opbagdiff }
| AMIN
    { QOps.Binary.opbagmin }
| AMAX
    { QOps.Binary.opbagmax }
| ACONTAINS
    { QOps.Binary.opcontains }
| ASCONCAT
    { QOps.Binary.opstringconcat }
| LPAREN ABARITH ARITHPLUS RPAREN
    { QOps.Binary.ZArith.opplus }
| LPAREN ABARITH ARITHMINUS RPAREN
    { QOps.Binary.ZArith.opminus }
| LPAREN ABARITH ARITHMULT RPAREN
    { QOps.Binary.ZArith.opmult }
| LPAREN ABARITH ARITHMIN RPAREN
    { QOps.Binary.ZArith.opmin }
| LPAREN ABARITH ARITHMAX RPAREN
    { QOps.Binary.ZArith.opmax }
| LPAREN ABARITH ARITHDIVIDE RPAREN
    { QOps.Binary.ZArith.opdiv }
| LPAREN ABARITH ARITHREM RPAREN
    { QOps.Binary.ZArith.oprem }

sql_date_component:
| DAY
  { Enhanced.Data.sql_date_day }
| MONTH
  { Enhanced.Data.sql_date_month }
| YEAR
  { Enhanced.Data.sql_date_year }

uop:
| FLOATNEG
  { QOps.Unary.FloatArith.opfloatneg }
| FLOATSQRT
  { QOps.Unary.FloatArith.opfloatsqrt }
| FLOATEXP
  { QOps.Unary.FloatArith.opfloatexp }
| FLOATLOG
  { QOps.Unary.FloatArith.opfloatlog }
| FLOATLOG10
  { QOps.Unary.FloatArith.opfloatlog10 }
| FLOATOFINT
  { QOps.Unary.opfloatofnat }
| FLOATCEIL
  { QOps.Unary.FloatArith.opfloatceil }
| FLOATFLOOR
  { QOps.Unary.FloatArith.opfloatfloor }
| FLOATTRUNCATE
  { QOps.Unary.opfloattruncate }
| FLOATABS
  { QOps.Unary.FloatArith.opfloatabs }
| AIDOP
    { QOps.Unary.opidentity }
| ANEG
    { QOps.Unary.opneg }
| ACOLL
    { QOps.Unary.opbag }
| ACOUNT
    { QOps.Unary.opcount }
| AFLATTEN
    { QOps.Unary.opflatten }
| ADISTINCT
    { QOps.Unary.opdistinct }
| ASUM
    { QOps.Unary.opnatsum }
| ATOSTRING
    { QOps.Unary.optostring }
| ASUBSTRING LPAREN s = INT RPAREN
  { QOps.Unary.opsubstring s None }
| ASUBSTRING LPAREN s = INT COMMA len = INT RPAREN
  { QOps.Unary.opsubstring s (Some len) }
| ALIKE LPAREN s = STRING RPAREN
  { QOps.Unary.oplike (Util.char_list_of_string s) None }
(* This should really be a CHAR escape character, but I don't know how to do that *)
| ALIKE LPAREN s = STRING ESCAPE esc = STRING RPAREN
    { QOps.Unary.oplike (Util.char_list_of_string s) (Some (esc.[0])) }
| ANUMMIN
    { QOps.Unary.opnatmin }
| ANUMMAX
    { QOps.Unary.opnatmax }
| AARITHMEAN
    { QOps.Unary.opnatmean }
| LPAREN AUARITH ARITHABS RPAREN
    { QOps.Unary.ZArith.opabs }
| LPAREN AUARITH ARITHLOG2 RPAREN
    { QOps.Unary.ZArith.oplog2 }
| LPAREN AUARITH ARITHSQRT RPAREN
    { QOps.Unary.ZArith.opsqrt }
| LPAREN ACAST LBRACKET s = stringlist RBRACKET RPAREN
    { QOps.Unary.opcast s }
| LPAREN ARECPROJECT LBRACKET s = stringlist RBRACKET RPAREN
    { QOps.Unary.oprecproject s }
| LPAREN AREC s = STRING RPAREN
    { QOps.Unary.oprec (Util.char_list_of_string s) }
| LPAREN ADOT s = STRING RPAREN
    { QOps.Unary.opdot (Util.char_list_of_string s) }
| AUNBRAND
    { QOps.Unary.opunbrand }
| ASINGLETON
    { QOps.Unary.opsingleton }
| AFLOATSUM
    { QOps.Unary.opfloatsum }
| AFLOATARITHMEAN
    { QOps.Unary.opfloatmean }
| AFLOATLISTMIN
    { QOps.Unary.opfloatmin }
| AFLOATLISTMAX
    { QOps.Unary.opfloatmax }
| TIMEFROMSTRING
    { Enhanced.Ops.Unary.time_from_string }
| TIMEDURATIONFROMSTRING
    { Enhanced.Ops.Unary.time_duration_from_string }
| SQLDATEFROMSTRING
    { Enhanced.Ops.Unary.sql_date_from_string }
| SQLDATEINTERVALFROMSTRING
    { Enhanced.Ops.Unary.sql_date_interval_from_string }
| LPAREN SQLGETDATECOMPONENT c = sql_date_component RPAREN
    { Enhanced.Ops.Unary.sql_get_date_component c }


