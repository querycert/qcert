(*
 * Copyright 2015-2017 IBM Corporation and portions Copyright 2017 by Joshua Auerbach
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

Require Import String.
Require Import ZArith.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.

Section SQLPP.
  Context {fruntime:foreign_runtime}.

  Unset Elimination Schemes.
  
  Definition sqlpp_order_spec : Set := SortDesc.
  Inductive sqlpp_distinct : Set := SPDistinct | SPAll.
  Inductive sqlpp_join_type : Set := SPInner | SPLeftOuter.

  (** The set of function names currently supported *)
  Inductive sqlpp_function_name : Set :=
  		  SPFget_year
		| SPFget_month
		| SPFget_day
		| SPFget_hour
		| SPFget_minute
		| SPFget_second
		| SPFget_millisecond
		| SPFavg
		| SPFmin
		| SPFmax
		| SPFcount
		| SPFsum
		| SPFcoll_avg
		| SPFcoll_min
		| SPFcoll_max
		| SPFcoll_count
		| SPFcoll_sum
		| SPFarray_avg
		| SPFarray_min
		| SPFarray_max
		| SPFarray_count
		| SPFarray_sum
		| SPFsqrt
		| SPFsubstring
		| SPFregexp_contains
		| SPFcontains
		.
  
  (** The SQLPP grammar according to AsterixDB

<<
Statement ::= ( SingleStatement ( ";" )? )* <EOF>

SingleStatement ::= DatabaseDeclaration
                  | FunctionDeclaration
                  | CreateStatement
                  | DropStatement
                  | LoadStatement
                  | SetStatement
                  | InsertStatement
                  | DeleteStatement
                  | Query ";"
>>

We currently support source files containing all possible statement types but only Query statements are passed along
by the initial front end.   Other statements are silently elided.  Of course, this can result in semantic nonsense when,
for example, a FunctionDeclaration is elided but is then used in a subsequent Query.  However, eliding most other statement
types works in practice since they are present for bookkeeping purposes and don't affect the semantics of the Query statements.

<<
Query ::= (Expression | SelectStatement) ";" 
>>

The distinction between Expression and SelectStatement is a superficial grammar technicality, because a
parenthesized SelectStatement is an Expression.  The duality at this production amounts to saying it is ok to
omit the parentheses at top level when followed by a semi-colon.  At the level of the AST, though, a Query is
an Expression and Expression is actually the top-level production.

Most of the non-terminals below "Expression" are there to show precedence, which is important in the grammar but
is not needed in the AST.  So, the AST is basically a huge inductive set on Expression.  *)

  Inductive sqlpp_expr : Set :=

(**
<<
Expression ::= OperatorExpression | CaseExpression | QuantifiedExpression

OperatorExpression ::= PathExpression
                       | Operator OperatorExpression
                       | OperatorExpression Operator (OperatorExpression)?
                       | OperatorExpression <BETWEEN> OperatorExpression 
                       <AND> OperatorExpression
>>
Valid operators for the first form (unary operators) are 
positive, negative, exists, not, isNull, isMissing, isUnknown
*)

  | SPPositive : sqlpp_expr -> sqlpp_expr
  | SPNegative : sqlpp_expr -> sqlpp_expr
  | SPExists : sqlpp_expr -> sqlpp_expr
  | SPNot : sqlpp_expr -> sqlpp_expr
  | SPIsNull : sqlpp_expr -> sqlpp_expr
  | SPIsMissing : sqlpp_expr -> sqlpp_expr
  | SPIsUnknown : sqlpp_expr -> sqlpp_expr                                  

(**                                 
Valid operators for the second form (binary operators) are
plus, minus, mult, div, mod, exp, concat, in, fuzzy-eq, eq, neq, lt, gt, le, ge, like, and, or
(Actually, fuzzy-eq isn't listed in the SQL++ grammar, but it's in the AQL grammar and supported for SQL++ by AsterixDB).
Note that we restrict the RHS of 'like' to be a String literal, which is more restrictive than the language spec.
*)

  | SPPlus : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPMinus : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPMult : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPDiv : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPMod : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPExp : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPConcat : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPIn : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPEq : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPFuzzyEq : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPNeq : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPLt : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPGt : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPLe : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPGe : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPLike : sqlpp_expr -> string -> sqlpp_expr (* Note special restriction *)
  | SPAnd : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPOr : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  
(** Finally, the ternery BETWEEN operator *)

  | SPBetween : sqlpp_expr -> sqlpp_expr -> sqlpp_expr -> sqlpp_expr                                         
                                         
(**
<<    
CaseExpression ::= SimpleCaseExpression | SearchedCaseExpression

SimpleCaseExpression ::= <CASE> Expression ( <WHEN> Expression <THEN> Expression )+ 
						( <ELSE> Expression )? <END>

SearchedCaseExpression ::= <CASE> ( <WHEN> Expression <THEN> Expression )+ 
						( <ELSE> Expression )? <END>
>>
 *)

  | SPSimpleCase : sqlpp_expr -> list sqlpp_when_then -> option sqlpp_expr -> sqlpp_expr
  | SPSearchedCase : list sqlpp_when_then -> option sqlpp_expr -> sqlpp_expr
                                                                         
(**
<<                                                           
QuantifiedExpression ::= ( (<ANY>|<SOME>) | <EVERY> ) 
                           Variable <IN> Expression ( "," Variable "in" Expression )*
                           f<SATISFIES> Expression (<END>)?
>>
*)

  | SPSome : list (string * sqlpp_expr) -> sqlpp_expr -> sqlpp_expr
  | SPEvery : list (string * sqlpp_expr) -> sqlpp_expr -> sqlpp_expr
  
(**
<<
PathExpression  ::= PrimaryExpression ( Field | Index )*

Field           ::= "." Identifier
>>
 *)

  | SPDot : sqlpp_expr -> string -> sqlpp_expr                                                            

(**
<<                                    
Index           ::= "[" ( Expression | "?" ) "]"
>>
 *)

  | SPIndex : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPIndexAny : sqlpp_expr -> sqlpp_expr

(**
<<                                         
PrimaryExpr ::= Literal
              | VariableReference
              | ParenthesizedExpression
              | FunctionCallExpression
              | Constructor
>>
Let's assume we can use existing support for literals, so I have omitted some details in the following:
<<
Literal        ::= StringLiteral
                   | IntegerLiteral
                   | FloatLiteral
                   | DoubleLiteral
                   | <NULL>
                   | <MISSING>
                   | <TRUE>
                   | <FALSE>
>>                   
 *)

  | SPLiteral : data -> sqlpp_expr (* For string, int, float, double, true and false *)
  | SPNull | SPMissing

(**
<<
VariableReference     ::= <IDENTIFIER>|<DelimitedIdentifier>
>>

The parsing of delimited identifiers will be handled by the AsterixDB parser, so, in Coq we just have string
representations of identifiers, whether delimited or not (with the delimiters omitted).
 *)

  | SPVarRef : string -> sqlpp_expr                                   

(**
<<
ParenthesizedExpression ::= "(" Expression ")" | Subquery
>>
The parenthesized expression is needed for parsing but does not need to be distinguished in the AST
<<
FunctionCallExpression ::= FunctionName "(" ( Expression ( "," Expression )* )? ")"
>>
*)

  | SPFunctionCall : sqlpp_function_name -> list sqlpp_expr -> sqlpp_expr
                        
(**
<<
Constructor              ::= ArrayConstructor | MultisetConstructor | ObjectConstructor

ArrayConstructor         ::= "[" ( Expression ( "," Expression )* )? "]"
>>
 *)

  | SPArray : list sqlpp_expr -> sqlpp_expr                                                   

(**
<<
MultisetConstructor      ::= "{{" ( Expression ( "," Expression )* )? "}}"
>>
 *)

  | SPBag : list sqlpp_expr -> sqlpp_expr                                  

(**
<<                                  
ObjectConstructor        ::= "{" ( FieldBinding ( "," FieldBinding )* )? "}"

FieldBinding             ::= Expression ":" Expression
>>
Although SQL++ does not restrict the first expression to be a string literal, we impose that restriction in our implementation.  The
front-end rejects violating cases.
 *)

  | SPObject : list (string * sqlpp_expr) -> sqlpp_expr
                             
(**
<<
SelectStatement    ::= ( WithClause )?
                       SelectSetOperation (OrderbyClause )? ( LimitClause )?
>>                       
For now, the front-end elides the limit clause                       
<<
SelectSetOperation ::= SelectBlock (<UNION> <ALL> ( SelectBlock | Subquery ) )*

Subquery           ::= "(" SelectStatement ")"
>>
*)

  | SPQuery : sqlpp_select_statement -> sqlpp_expr
  
with sqlpp_select_statement : Set :=
	SPSelectStmt :
		list (string * sqlpp_expr)     (* The 'with' clause.  Empty list if missing *)
		-> sqlpp_select_block (* The first or only select block *) 
		-> list sqlpp_union_element (* additional select blocks or subqueries, unioned with the first *) 
		-> sqlpp_order_by  (* order by; limit clause elided earlier *)
		-> sqlpp_select_statement

(**
<<
SelectBlock        ::= SelectClause
                       ( FromClause ( LetClause )?)?
                       ( WhereClause )?
                       ( GroupbyClause ( LetClause )? ( HavingClause )? )?
                       |
                       FromClause ( LetClause )?
                       ( WhereClause )?
                       ( GroupbyClause ( LetClause )? ( HavingClause )? )?
                       SelectClause

HavingClause       ::= <HAVING> Expression
>>
That is, a select block has a required select clause with optional from, where, and group by clauses (also, up to two let clauses
loosely tied to the from and groupby clauses, and an optional having clause tied to the groupby clause).  The two branches
of the production say that the from clause, if present, can come first, which is meaningless at the AST level.                       
<<
FromClause         ::= <FROM> FromTerm ( "," FromTerm )*
>>
*)

with sqlpp_select_block : Set :=
	SPSelectBlock : sqlpp_select -> list sqlpp_from   (* The 'from' clause as a list of from terms.  Empty list if missing *)
	    -> list (string * sqlpp_expr)  (* the first let clause, empty list if missing *)
        -> sqlpp_where -> sqlpp_group_by
        -> list (string * sqlpp_expr)  (* the second let clause, empty list if missing *)
        -> option sqlpp_expr  (* the optional having clause *) 
        -> sqlpp_select_block

with sqlpp_union_element : Set :=
  | SPBlock : sqlpp_select_block -> sqlpp_union_element
  | SPSubquery : sqlpp_select_statement -> sqlpp_union_element        

(**
<<
SelectClause       ::= <SELECT> ( <ALL> | <DISTINCT> )? ( SelectRegular | SelectValue )

SelectRegular      ::= Projection ( "," Projection )*

SelectValue      ::= ( <VALUE> | <ELEMENT> | <RAW> ) Expression

Projection         ::= ( Expression ( <AS> )? Identifier | "*" )
>>
*)

with sqlpp_select : Set :=
  | SPSelectSQL : sqlpp_distinct -> list sqlpp_project -> sqlpp_select
  | SPSelectValue: sqlpp_distinct -> sqlpp_expr -> sqlpp_select
  
with sqlpp_project : Set :=
  | SPProject : (sqlpp_expr * option string) -> sqlpp_project
  | SPProjectStar
  
(**
<<
FromTerm           ::= Expression (( <AS> )? Variable)?
                       ( ( JoinType )? ( JoinClause | UnnestClause ) )*

JoinType           ::= ( <INNER> | <LEFT> ( <OUTER> )? )

JoinClause         ::= <JOIN> Expression (( <AS> )? Variable)? <ON> Expression

UnnestClause       ::= ( <UNNEST> | <CORRELATE> | <FLATTEN> ) Expression
                       ( <AS> )? Variable ( <AT> Variable )?
>>
*)

with sqlpp_from : Set :=
  | SPFrom : sqlpp_expr -> option string -> list sqlpp_join_clause -> sqlpp_from

with sqlpp_join_clause : Set :=
  | SPJoin : sqlpp_join_type -> sqlpp_expr -> option string -> sqlpp_expr -> sqlpp_join_clause
  | SPUnnest : sqlpp_join_type -> sqlpp_expr -> option string -> option string -> sqlpp_join_clause  

(**	
Let and with clauses are distinct in the grammar but use the same AsterixDB AST element so will not be distinct internally.
When these clauses appear in the grammar, the AST simply uses (string * sqlpp_expr)
<<
WithClause         ::= <WITH> WithElement ( "," WithElement )*

LetClause          ::= (<LET> | <LETTING>) LetElement ( "," LetElement )*

LetElement         ::= Variable "=" Expression

WithElement        ::= Variable <AS> Expression

WhereClause        ::= <WHERE> Expression
>>
*)

with sqlpp_where : Set :=
  | SPWhere : sqlpp_expr -> sqlpp_where
  | SPNoWhere

(**
<<  
GroupbyClause      ::= <GROUP> <BY> ( Expression ( (<AS>)? Variable )? 
                       ( "," Expression ( (<AS>)? Variable )? )*
                       ( <GROUP> <AS> Variable
                       	  ("(" Variable <AS> VariableReference 
                       	  ("," Variable <AS> VariableReference )* ")")?
                       )?
>>                       
*)

with sqlpp_group_by : Set :=
	| SPGroupBy : list (sqlpp_expr * option string)   (* group by section *)
		-> option (string * list (string * string))  (* group as section *)
		-> sqlpp_group_by
    | SPNoGroupBy

(**
<<		
OrderbyClause      ::= <ORDER> <BY> Expression ( <ASC> | <DESC> )? 
                            ( "," Expression ( <ASC> | <DESC> )? )*
>>
 *)
 
with sqlpp_order_by : Set :=
	| SPOrderBy : list (sqlpp_expr * sqlpp_order_spec) -> sqlpp_order_by
	| SPNoOrderBy
	
with sqlpp_when_then : Set:=
	| SPWhenThen : sqlpp_expr -> sqlpp_expr -> sqlpp_when_then	
.	

  (* Let's finally give our languages a proper name! *)
  Definition sqlpp : Set := sqlpp_expr.

  
End SQLPP.

