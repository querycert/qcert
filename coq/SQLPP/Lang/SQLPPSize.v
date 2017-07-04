(*
 * Copyright 2015-2017 IBM Corporation
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

Section SQLPPSize.

  Require Import String.
  Require Import ZArith.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicSystem.

  Require Import SQLPP.
  
  Context {fruntime:foreign_runtime}.

  Section size.
  	(* Temp. until I figure out how to get the real one to work: *)
  	Definition sqlpp_expr_size (q:sqlpp_expr) := 1.
    Definition sqlpp_statement_size (stmt: sqlpp_select_statement) := 1.

	(*
    Fixpoint sqlpp_expr_size (q:sqlpp_expr) := (* XXX To check XXX *)
      match q with
	| SPPositive expr
	| SPNegative expr
  	| SPExists expr
  	| SPNot expr
  	| SPIsNull expr
  	| SPIsMissing expr
  	| SPIsUnknown expr
  		=> 1 + sqlpp_expr_size  expr
	| SPPlus  e1 e2
  	| SPMinus  e1 e2
  	| SPMult  e1 e2
  	| SPDiv  e1 e2
  	| SPMod  e1 e2
  	| SPExp  e1 e2
  	| SPConcat  e1 e2
  	| SPIn  e1 e2
  	| SPEq  e1 e2
  	| SPNeq  e1 e2
  	| SPLt  e1 e2
  	| SPGt  e1 e2
  	| SPLe  e1 e2
  	| SPGe  e1 e2
  	| SPLike  e1 e2
  	| SPAnd  e1 e2
  	| SPOr  e1 e2
  		=> 1 + sqlpp_expr_size  e1 + sqlpp_expr_size  e2
	| SPBetween  e1 e2 e3
		=> 1 + sqlpp_expr_size  e1 + sqlpp_expr_size  e2 + sqlpp_expr_size  e3
	| SPSimpleCase  e l o
		=> match o with
		| None => 1 + sqlpp_expr_size e + (List.fold_left (fun acc whenthen => acc + (whenthen_size whenthen)) l 0)
		| Some oe => 1 + sqlpp_expr_size e + (List.fold_left (fun acc whenthen => acc + (whenthen_size whenthen)) l 0) + sqlpp_expr_size oe
		end
	| SPSearchedCase l o
		=> match o with
		| None => 1 + (List.fold_left (fun acc whenthen => acc (whenthen_size whenthen)) l 0)
		| Some oe => 1 + (List.fold_left (fun acc whenthen => acc + (whenthen_size whenthen)) l 0) + sqlpp_expr_size oe
		end
	| SPSome  l e
    | SPEvery l e
		=> 1 + list_string_expr_pair_size l + sqlpp_expr_size  e
	| SPDot  expr _
		=> 1 + sqlpp_expr_size  expr                                                              
	| SPIndex  e i
		=> 1 + sqlpp_expr_size  e + sqlpp_expr_size  i
	| SPLiteral _
  	| SPNull | SPMissing | SPTrue | SPFalse
  		=> 1                       
	| SPVarRef _
		=> 1                                  
	| SPFunctionCall _ l
		=> 1 + list_expr_size l
	| SPArray l
	| SPBag l
		=> 1 + list_expr_size l
	| SPObject l
		=> 1 + list_string_expr_pair_size l
	| SPQuery stmt
		=> 1 + (sqlpp_statement_size stmt)
      end
      
  with sqlpp_statement_size (stmt: sqlpp_select_statement) :=
  	(* TODO *) 1       

  with whenthen_size (wt : sqlpp_when_then) :=
  	match wt with
  	| SPWhenThen w t
		=> 1 + (sqlpp_expr_size w) + (sqlpp_expr_size t)
	end
      
  with list_string_expr_pair_size (l : list (string * sqlpp_expr)) :=
	List.fold_left (fun acc pair => acc + 1 + (sqlpp_expr_size (snd pair))) l 0
  	  
  with list_expr_size (l : list sqlpp_expr) :=
	List.fold_left (fun acc e => acc + (sqlpp_expr_size  e)) l 0.   		  	  
*)

  Definition sqlpp_size (l : list sqlpp_expr) :=
	List.fold_left (fun acc e => acc + (sqlpp_expr_size e)) l 0.

  End size.

  Section depth.
	(* Temp:*)
    Definition sqlpp_depth (q:sqlpp) := 1.

  End depth.

End SQLPPSize.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
