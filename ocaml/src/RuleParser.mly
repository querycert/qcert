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
%token FLOATNE FLOATLT FLOATLE FLOATGT FLOATGE

%token AFLOATSUM AFLOATARITHMEAN AFLOATLISTMIN AFLOATLISTMAX

%token TIMEAS TIMESHIFT
%token TIMENE TIMELT TIMELE TIMEGT TIMEGE
%token TIMEDURATIONFROMSCALE TIMEDURATIONBETWEEN

%token TIMEFROMSTRING TIMEDURATIONFROMSTRING

%token PNOW

%token AEQ AUNION ACONCAT AMERGECONCAT AAND AOR ALT ALE AMINUS AMIN AMAX ACONTAINS ASCONCAT
%token ABARITH ARITHPLUS ARITHMINUS ARITHMULT ARITHMIN ARITHMAX ARITHDIVIDE ARITHREM
%token AIDOP ANEG ACOLL ACOUNT AFLATTEN ADISTINCT ASUM ATOSTRING ANUMMIN ANUMMAX AARITHMEAN ACAST ADOT AREC ARECPROJECT AUNBRAND ASINGLETON
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

%start <(string * Compiler.EnhancedCompiler.CompDriver.query)> rulemain
%start <Compiler.EnhancedCompiler.Pattern.pat> patmain
%type <Compiler.EnhancedCompiler.Rule.rule -> Compiler.EnhancedCompiler.Rule.rule> rule_rule

%%

rulemain:
| EXAMPLE i=IDENT COLONEQUAL r = rule DOT EOF
    { (i, CompDriver.Q_rule r) }
| EXAMPLE i=IDENT COLONEQUAL p = pat DOT EOF
    { (i, CompDriver.Q_camp p) }

patmain:
| p = pat EOF
    { p }

rule:
| RULERETURN p = pat
    { Rule.rule_return p }
| RULEWHEN p = pat SEMISEMI r = rule
    { Rule.rule_when p r }
| RULENOT p = pat SEMISEMI r = rule
    { Rule.rule_not p r }
| RULEGLOBAL p = pat SEMISEMI r = rule
    { Rule.rule_global p r }

rule_rule:
| RULEWHEN p = pat
    { (fun r -> Rule.rule_when p r) }
| RULENOT p = pat
    { (fun r -> Rule.rule_not p r) }
| RULEGLOBAL p = pat
    { (fun r -> Rule.rule_global p r) }
| RULEWHEN p = pat SEMISEMISEMI r = rule_rule 
    { (fun r1 -> (Rule.rule_when p (r r1))) }
| RULENOT p = pat SEMISEMISEMI r = rule_rule
    { (fun r1 -> (Rule.rule_not p (r r1))) }
| RULEGLOBAL p = pat SEMISEMISEMI r = rule_rule
    { (fun r1 -> (Rule.rule_global p (r r1))) }

pat:
(* Parenthesized pattern *)
| LPAREN p = pat RPAREN
    { p }
(* CAMP pattern *)
| PCONST DUNIT
    { Pattern.pconst Data.dunit }
| PCONST LPAREN d = data RPAREN
    { Pattern.pconst d }
| PUNOP u = uop p = pat
    { Pattern.punop u p }
| PBINOP b = bop p1 = pat p2 = pat
    { Pattern.pbinop b p1 p2 }
| PMAP p = pat
    { Pattern.pmap p }
| PASSERT p = pat
    { Pattern.passert p }
| PORELSE p1 = pat p2 = pat
    { Pattern.porelse p1 p2 }
| PIT
    { Pattern.pit }
| PLETIT p1 = pat p2 = pat
    { Pattern.pletit p1 p2 }
| PENV
    { Pattern.penv }
| PLETENV p1 = pat p2 = pat
    { Pattern.pletenv  p1 p2 }
| PLEFT
    { Pattern.pleft }
| PRIGHT
    { Pattern.pright }
| PGETCONSTANT s = STRING
    { Pattern.pgetconstant (Util.char_list_of_string s) }
(* Macros pattern *)
| PNOW
    { Pattern.pnow }
| PACCEPT
    { Pattern.pconst (Data.drec []) }
| LOOKUP s = STRING
    { Pattern.lookup (Util.char_list_of_string s) }
 | v = STRING IS p = pat %prec UIS
    { Pattern.pIS (Util.char_list_of_string v) p }
| WITHVAR s = STRING p = pat %prec UWITHVAR
    { Pattern.withVar (Util.char_list_of_string s) p }
| PVARWITH s = STRING p = pat %prec UWITHVAR
    { Pattern.pvarwith (Util.char_list_of_string s) p }
| TOSTRING p = pat
    { Pattern.toString p }
| PBINOPRED b = bop LBRACKET pl = patlist RBRACKET
    { Pattern.pat_binop_reduce b pl }
| p1 = pat PLUSSPLUS p2 = pat
    { Pattern.stringConcat p1 p2 }
| DASHUNDER
    { Pattern.pit }
| DASHTICK c = const
    { (Pattern.pconst c) }
| s = STRING BANGDASHARROW p = pat
    { Pattern.pbdot (Util.char_list_of_string s) p }
| PBDOT s = STRING p = pat %prec PBDOT
    { Pattern.pbdot (Util.char_list_of_string s) p }
| PBSOMEDOT s = STRING p = pat %prec PBSOMEDOT
    { Pattern.pbsomedot (Util.char_list_of_string s) p }
| PSOME
    { Pattern.pleft }
| PNULL
    { Pattern.pnull }
(* INSTANCEOF, FETCH, and MATCHES temporarily have hacks because of signature changes in RuleSugar.v.  TODO fix this *)
| n = STRING INSTANCEOF LBRACKET t = stringlist RBRACKET WHERE p = pat %prec UINSTANCE
    { Pattern.instanceOf (Util.char_list_of_string n) t p }
| p = pat TEMPVAR t = STRING FETCH LBRACKET e = stringlist RBRACKET KEY a = STRING DO pcont = pat %prec UFETCH
    { Pattern.fetchRef e (Util.char_list_of_string a) (Util.char_list_of_string t) p pcont }
| MATCHES LBRACKET t = stringlist RBRACKET WHERE p = pat %prec UINSTANCE
    { Pattern.matches t p }
| AGGREGATE r = rule_rule DO u = uop OVER p = pat FLATTEN f = INT
    { Rule.aggregate r u p (Util.coq_Z_of_int f) }
| VARIABLES LBRACKET v = stringlist RBRACKET
    { Pattern.returnVariables v }

data:
| DUNIT
    { Data.dunit }
| DBOOL TRUE
    { Data.dbool true }
| DBOOL FALSE
    { Data.dbool false }
| DFLOAT f = FLOAT
    { Enhanced.Data.dfloat f }
| DNAT i = INT
    { Data.dnat (Util.coq_Z_of_int i) }
| DSTRING s = STRING
    { Data.dstring (Util.char_list_of_string s) }
| DCOLL LBRACKET dl = datalist RBRACKET
    { Data.dcoll dl }
| DREC LBRACKET rl = reclist RBRACKET
    { Data.drec rl }
| DLEFT d = data
    { Data.dleft d }
| DRIGHT d = data
    { Data.dright d }
| DBRAND sl = stringlist d = data
    { Data.dbrand sl d }
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
    { Data.dnat (Util.coq_Z_of_int i) }
| f = FLOAT
    { Enhanced.Data.dfloat f }
| s = STRING
    { Data.dstring (Util.char_list_of_string s) }

bop:
| FLOATPLUS
  { Enhanced.Ops.Binary.float_plus }
| FLOATMINUS
  { Enhanced.Ops.Binary.float_minus }
| FLOATMULT
  { Enhanced.Ops.Binary.float_mult }
| FLOATDIV
  { Enhanced.Ops.Binary.float_div }
| FLOATPOW
  { Enhanced.Ops.Binary.float_pow }
| FLOATMIN
  { Enhanced.Ops.Binary.float_min }
| FLOATMAX
  { Enhanced.Ops.Binary.float_max }
| FLOATNE
  { Enhanced.Ops.Binary.float_ne }
| FLOATLT
  { Enhanced.Ops.Binary.float_lt }
| FLOATLE
  { Enhanced.Ops.Binary.float_le }
| FLOATGT
  { Enhanced.Ops.Binary.float_gt }
| FLOATGE
  { Enhanced.Ops.Binary.float_ge }

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
| AEQ
    { Ops.Binary.aeq }
| AUNION
    { Ops.Binary.aunion }
| ACONCAT
    { Ops.Binary.aconcat }
| AMERGECONCAT
    { Ops.Binary.amergeconcat }
| AAND
    { Ops.Binary.aand }
| AOR
    { Ops.Binary.aor }
| ALT
    { Ops.Binary.alt }
| ALE
    { Ops.Binary.ale }
| AMINUS
    { Ops.Binary.aminus }
| AMIN
    { Ops.Binary.amin }
| AMAX
    { Ops.Binary.amax }
| ACONTAINS
    { Ops.Binary.acontains }
| ASCONCAT
    { Ops.Binary.asconcat }
| LPAREN ABARITH ARITHPLUS RPAREN
    { Ops.Binary.ZArith.aplus }
| LPAREN ABARITH ARITHMINUS RPAREN
    { Ops.Binary.ZArith.aminus }
| LPAREN ABARITH ARITHMULT RPAREN
    { Ops.Binary.ZArith.amult }
| LPAREN ABARITH ARITHMIN RPAREN
    { Ops.Binary.ZArith.amin }
| LPAREN ABARITH ARITHMAX RPAREN
    { Ops.Binary.ZArith.amax }
| LPAREN ABARITH ARITHDIVIDE RPAREN
    { Ops.Binary.ZArith.adiv }
| LPAREN ABARITH ARITHREM RPAREN
    { Ops.Binary.ZArith.arem }

uop:
| FLOATNEG
  { Enhanced.Ops.Unary.float_neg }
| FLOATSQRT
  { Enhanced.Ops.Unary.float_sqrt }
| FLOATEXP
  { Enhanced.Ops.Unary.float_exp }
| FLOATLOG
  { Enhanced.Ops.Unary.float_log }
| FLOATLOG10
  { Enhanced.Ops.Unary.float_log10 }
| FLOATOFINT
  { Enhanced.Ops.Unary.float_of_int }
| FLOATCEIL
  { Enhanced.Ops.Unary.float_ceil }
| FLOATFLOOR
  { Enhanced.Ops.Unary.float_floor }
| FLOATTRUNCATE
  { Enhanced.Ops.Unary.float_truncate }
| FLOATABS
  { Enhanced.Ops.Unary.float_abs }
| AIDOP
    { Ops.Unary.aidop }
| ANEG
    { Ops.Unary.aneg }
| ACOLL
    { Ops.Unary.acoll }
| ACOUNT
    { Ops.Unary.acount }
| AFLATTEN
    { Ops.Unary.aflatten }
| ADISTINCT
    { Ops.Unary.adistinct }
| ASUM
    { Ops.Unary.asum }
| ATOSTRING
    { Ops.Unary.atostring }
| ANUMMIN
    { Ops.Unary.anummin }
| ANUMMAX
    { Ops.Unary.anummax }
| AARITHMEAN
    { Ops.Unary.aarithmean }
| LPAREN AUARITH ARITHABS RPAREN
    { Ops.Unary.ZArith.aabs }
| LPAREN AUARITH ARITHLOG2 RPAREN
    { Ops.Unary.ZArith.alog2 }
| LPAREN AUARITH ARITHSQRT RPAREN
    { Ops.Unary.ZArith.asqrt }
| LPAREN ACAST LBRACKET s = stringlist RBRACKET RPAREN
    { Ops.Unary.acast s }
| LPAREN ARECPROJECT LBRACKET s = stringlist RBRACKET RPAREN
    { Ops.Unary.arecproject s }
| LPAREN AREC s = STRING RPAREN
    { Ops.Unary.arec (Util.char_list_of_string s) }
| LPAREN ADOT s = STRING RPAREN
    { Ops.Unary.adot (Util.char_list_of_string s) }
| AUNBRAND
    { Ops.Unary.aunbrand }
| ASINGLETON
    { Ops.Unary.asingleton }
| AFLOATSUM
    { Enhanced.Ops.Unary.float_sum }
| AFLOATARITHMEAN
    { Enhanced.Ops.Unary.float_arithmean }
| AFLOATLISTMIN
    { Enhanced.Ops.Unary.float_listmin }
| AFLOATLISTMAX
    { Enhanced.Ops.Unary.float_listmax }
| TIMEFROMSTRING
    { Enhanced.Ops.Unary.time_from_string }
| TIMEDURATIONFROMSTRING
    { Enhanced.Ops.Unary.time_duration_from_string }

