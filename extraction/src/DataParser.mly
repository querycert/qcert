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
  open QcertCompiler.EnhancedCompiler
%}
%token NULL TRUE FALSE
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token COMMA COLON
%token LCURLY RCURLY
%token LBRACKET RBRACKET
%token EOF
  
%start <QcertCompiler.EnhancedCompiler.QData.json> main
%%

main:
| d = json EOF
    { d }

json:
| NULL
    { QData.jnull }
| i = INT
    { QData.jnumber (float_of_int i) }
| f = FLOAT
    { QData.jnumber f }
| s = STRING
    { QData.jstring (Util.char_list_of_string s) }
| TRUE
    { QData.jbool true }
| FALSE
    { QData.jbool false }
| LCURLY r = jobject RCURLY
    { QData.jobject r }
| LCURLY RCURLY
    { QData.jobject [] }
| LBRACKET l = jarray RBRACKET
    { QData.jarray l }
| LBRACKET RBRACKET
    { QData.jarray [] }

jobject:
| a = attribute
    { [a] }
| a = attribute COMMA r = jobject
    { a :: r }

attribute:
| s = STRING COLON d = json
    { ((Util.char_list_of_string s), d) }

jarray:
| d = json
    { [d] }
| d = json COMMA l = jarray
    { d :: l }

