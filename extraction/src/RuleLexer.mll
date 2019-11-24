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

{
  open Util
  open LexUtil
  open RuleParser

  let keyword_table =
    let tbl = Hashtbl.create 97 in
    begin
      List.iter (fun (key, data) -> Hashtbl.add tbl key data)
	[ "Example", EXAMPLE;
	  (* Binary ops *)
 	  "AFloatPlus", FLOATPLUS;
	  "AFloatMinus", FLOATMINUS;
	  "AFloatMult", FLOATMULT;
	  "AFloatDiv", FLOATDIV;
	  "AFloatPow", FLOATPOW;
	  "AFloatMin", FLOATMIN;
	  "AFloatMax", FLOATMAX;
(*	  "AFloatNe", FLOATNE;
	  "AFloatLt", FLOATLT;
	  "AFloatLe", FLOATLE;
	  "AFloatGt", FLOATGT;
	  "AFloatGe", FLOATGE;*)
	  "ATimeAs", TIMEAS;
	  "ATimeShift", TIMESHIFT;
	  "ATimeNe", TIMENE;
	  "ATimeLt", TIMELT;
	  "ATimeLe", TIMELE;
	  "ATimeGt", TIMEGT;
	  "ATimeGe", TIMEGE;
	  "ATimeDurationFromScale", TIMEDURATIONFROMSCALE;
	  "ATimeDurationBetween", TIMEDURATIONBETWEEN;
	  "ASqlDatePlus", SQLDATEPLUS;
 	  "ASqlDateMinus", SQLDATEMINUS;
	  "ASqlDateNe", SQLDATENE;
	  "ASqlDateLt", SQLDATELT;
	  "ASqlDateLe", SQLDATELE;
	  "ASqlDateGt", SQLDATEGT;
	  "ASqlDateGe", SQLDATEGE;
	  "ASqlDateIntervalBetween", SQLDATEINTERVALBETWEEN;
	  "AEq", AEQ;
	  "AUnion", AUNION;
	  "AConcat", ACONCAT;
	  "AMergeConcat", AMERGECONCAT;
	  "AAnd", AAND;
	  "AOr", AOR;
	  "ALt", ALT;
	  "ALe", ALE;
	  "AMinus", AMINUS;
	  "AMin", AMIN;
	  "AMax", AMAX;
	  "AContains", ACONTAINS;
	  "ASConcat", ASCONCAT;
	  "ABArith", ABARITH;
	  "ArithPlus", ARITHPLUS;
	  "ArithMinus", ARITHMINUS;
	  "ArithMult", ARITHMULT;
	  "ArithMin", ARITHMIN;
	  "ArithMax", ARITHMAX;
	  "ArithDivide", ARITHDIVIDE;
	  "ArithRem", ARITHREM;
	  (* Unary ops *)
	  "AFloatNeg", FLOATNEG;
	  "AFloatSqrt", FLOATSQRT;
	  "AFloatExp", FLOATEXP;
	  "AFloatLog", FLOATLOG;
	  "AFloatLog10", FLOATLOG10;
	  "AFloatOfInt", FLOATOFINT;
	  "AFloatCeil", FLOATCEIL;
	  "AFloatFloor", FLOATFLOOR;
	  "AFloatTruncate", FLOATTRUNCATE;
	  "AFloatAbs", FLOATABS;
	  "AIdOp", AIDOP;
	  "ANeg", ANEG;
	  "AColl", ACOLL;
	  "ACount", ACOUNT;
	  "AFlatten", AFLATTEN;
	  "ADistinct", ADISTINCT;
	  "ASum", ASUM;
	  "AToString", ATOSTRING;
 	  "ASubstring", ASUBSTRING;
	  "ALike", ALIKE;
 	  "ESCAPE", ESCAPE;
	  "ANumMin", ANUMMIN;
	  "ANumMax", ANUMMAX;
	  "AArithMean", AARITHMEAN;
	  "AUArith", AUARITH;
	  "ArithAbs", ARITHABS;
	  "ArithLog2", ARITHLOG2;
	  "ArithSqrt", ARITHSQRT;
	  "ACast", ACAST;
	  "ADot", ADOT;
	  "ARec", AREC;
	  "ARecProject", ARECPROJECT;
	  "AUnbrand", AUNBRAND;
 	  "ASingleton", ASINGLETON;
          "AFloatSum", AFLOATSUM;
          "AFloatArithMean", AFLOATARITHMEAN;
          "AFloatListMin", AFLOATLISTMIN;
          "AFloatListMax", AFLOATLISTMAX;
	  "ATimeFromString", TIMEFROMSTRING;
	  "ATimeDurationFromString", TIMEDURATIONFROMSTRING;
	  "ASqlDateFromString", SQLDATEFROMSTRING;
	  "ASqlDateIntervalFromString", SQLDATEINTERVALFROMSTRING;
 	  "ASqlGetDateComponent", SQLGETDATECOMPONENT;
	  (* Top-level rule *)
	  "rule_when", RULEWHEN;
	  "rule_global", RULEGLOBAL;
	  "rule_not", RULENOT;
	  "rule_return", RULERETURN;
	  (* Data *)
	  "dunit", DUNIT;
	  "dnat", DNAT;
	  "dbool", DBOOL;
	  "dstring", DSTRING;
	  "dcoll", DCOLL;
	  "drec", DREC;
	  "dleft", DLEFT;
	  "dright", DRIGHT;
	  "dbrand", DBRAND;
	  "true", TRUE;
	  "false", FALSE;
	  "dtime_scale", DTIMESCALE;
	  "SECOND", SECOND;
	  "MINUTE", MINUTE;
	  "HOUR", HOUR;
	  "DAY", DAY;
	  "WEEK", WEEK;
	  "MONTH", MONTH;
	  "YEAR", YEAR;
	  (* Pattern *)
	  "pconst", PCONST;
	  "punop", PUNOP;
	  "pbinop", PBINOP;
	  "pmap", PMAP;
	  "passert", PASSERT;
	  "porElse", PORELSE;
	  "pit", PIT;
	  "pletIt", PLETIT;
	  "penv", PENV;
	  "pletEnv", PLETENV;
	  "pleft", PLEFT;
	  "pright", PRIGHT;
		"pgetconstant", PGETCONSTANT;
	  (* Pattern macros *)
  	  "pnow", PNOW;
	  "pat_binop_reduce", PBINOPRED;
	  "VARIABLES", VARIABLES;
	  "INSTANCEOF", INSTANCEOF;
	  "MATCHES", MATCHES;
	  "WHERE", WHERE;
	  "AGGREGATE", AGGREGATE;
	  "DO", DO;
	  "OVER", OVER;
		"FLATTEN", FLATTEN;
	  "IS", IS;
	  "paccept", PACCEPT;
	  "pbdot", PBDOT;
	  "pbsomedot", PBSOMEDOT;
	  "psome", PSOME;
	  "pnull", PNULL;
	  "withVar", WITHVAR;
	  "pvarwith", PVARWITH;
	  "toString", TOSTRING;
	  "lookup", LOOKUP;
	  "TEMPVAR", TEMPVAR;
	  "FETCH", FETCH;
	  "KEY", KEY
	]; tbl
    end
    
}

let newline = ('\010' | '\013' | "\013\010")
let letter = ['A'-'Z' 'a'-'z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '.' '0'-'9']

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* (frac exp? | exp)

rule token sbuff = parse
| eof
    { EOF }
| ":="
    { COLONEQUAL }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| '['
    { LBRACKET }
| ']'
    { RBRACKET }
| ","
    { COMMA }
| ";"
    { SEMI }
| ";;"
    { SEMISEMI }
| ";;;"
    { SEMISEMISEMI }
| "#`"
    { DASHTICK }
| "#_"
    { DASHUNDER }
| "+s+"
    { PLUSSPLUS }
| "!#->"
    { BANGDASHARROW }
| '.'
    { DOT }
| [' ' '\t']
    { token sbuff lexbuf }
| newline
    { Lexing.new_line lexbuf; token sbuff lexbuf }
| float as f
    { FLOAT (float_of_string f) }
| ('-'? ['0'-'9']+) as i
    { INT (int_of_string i) }
| '"'
    { reset_string sbuff; string sbuff lexbuf }
| letter identchar*
    { let s = Lexing.lexeme lexbuf in
      try Hashtbl.find keyword_table s
      with Not_found -> IDENT s }
| "(*"
    { comment 1 lexbuf; token sbuff lexbuf }
| _
    { raise (LexError (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }

and string sbuff = parse
  | "\"\"" { add_char_to_string sbuff '"'; string sbuff lexbuf }                         (* Escaped quote *)
  | "\013\n" { add_char_to_string sbuff '\n'; string sbuff lexbuf }
  | "\013" { add_char_to_string sbuff '\n'; string sbuff lexbuf }
  | '"'    { let s = get_string sbuff in STRING s }  (* End of string *)
  | eof    { raise (LexError "String not terminated.\n") }
  | _      { add_char_to_string sbuff (Lexing.lexeme_char lexbuf 0); string sbuff lexbuf }

and comment cpt = parse
  | "(*"
      { comment (cpt + 1) lexbuf }
  | "*)"
      { if cpt > 1 then comment (cpt - 1) lexbuf }
  | eof
      { raise (LexError "Unterminated comment\n") }
  | newline
      { Lexing.new_line lexbuf; comment cpt lexbuf }
  | _
      { comment cpt lexbuf }

