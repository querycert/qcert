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
%token NULL TRUE FALSE
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token COMMA COLON
%token LCURLY RCURLY
%token LBRACKET RBRACKET
%token EOF
  
%start <Asts.json_ast> main
%%

main:
| d = data EOF
    { d }

data:
| NULL
    { Data.dunit }
| i = INT
    { Data.dnat (Util.coq_Z_of_int i) }
| f = FLOAT
    { Enhanced.Data.dfloat f }
| s = STRING
    { Data.dstring (Util.char_list_of_string s) }
| TRUE
    { Data.dbool true }
| FALSE
    { Data.dbool false }
| LCURLY r = jrec RCURLY
    { Data.drec r }
| LCURLY RCURLY
    { Data.drec [] }
| LBRACKET l = jarray RBRACKET
    { Data.dcoll l }
| LBRACKET RBRACKET
    { Data.dcoll [] }

jrec:
| a = attribute
    { [a] }
| a = attribute COMMA r = jrec
    { a :: r }

attribute:
| s = STRING COLON d = data
    { ((Util.char_list_of_string s), d) }

jarray:
| d = data
    { [d] }
| d = data COMMA l = jarray
    { d :: l }

