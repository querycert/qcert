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
    Fixpoint sqlpp_expr_size (q:sqlpp_expr) :=
      match q with
	| SPPositive expr
	| SPNegative expr
  	| SPExists expr
  	| SPNot expr
  	| SPIsNull expr
  	| SPIsMissing expr
  	| SPIsUnknown expr
  		=> 1 + (sqlpp_expr_size  expr)
	| SPPlus  e1 e2
  	| SPMinus  e1 e2
  	| SPMult  e1 e2
  	| SPDiv  e1 e2
  	| SPMod  e1 e2
  	| SPExp  e1 e2
  	| SPConcat  e1 e2
  	| SPIn  e1 e2
  	| SPEq  e1 e2
  	| SPFuzzyEq e1 e2
  	| SPNeq  e1 e2
  	| SPLt  e1 e2
  	| SPGt  e1 e2
  	| SPLe  e1 e2
  	| SPGe  e1 e2
  	| SPLike  e1 e2
  	| SPAnd  e1 e2
  	| SPOr  e1 e2
  		=> 1 + (sqlpp_expr_size  e1) + (sqlpp_expr_size  e2)
	| SPBetween  e1 e2 e3
		=> 1 + (sqlpp_expr_size  e1) + (sqlpp_expr_size  e2) + (sqlpp_expr_size  e3)
	| SPSimpleCase  e l o
		=> match o with
		| None => 1 + (sqlpp_expr_size e) + (List.fold_left (fun acc whenthen => acc + (whenthen_size whenthen)) l 0)
		| Some oe => 1 + (sqlpp_expr_size e) + (List.fold_left (fun acc whenthen => acc + (whenthen_size whenthen)) l 0) + (sqlpp_expr_size oe)
		end
	| SPSearchedCase l o
		=> match o with
		| None => 1 + (List.fold_left (fun acc whenthen => acc + (whenthen_size whenthen)) l 0)
		| Some oe => 1 + (List.fold_left (fun acc whenthen => acc + (whenthen_size whenthen)) l 0) + (sqlpp_expr_size oe)
		end
	| SPSome  l e
    | SPEvery l e
		=> 1 + (List.fold_left (fun acc p => acc + (string_expr_pair_size p)) l 0) + (sqlpp_expr_size  e)
	| SPDot  expr _
		=> 1 + (sqlpp_expr_size  expr)                                                              
	| SPIndex  e i
		=> 1 + (sqlpp_expr_size  e) + (sqlpp_expr_size  i)
	| SPIndexAny e
		=> 1 + (sqlpp_expr_size e)
	| SPLiteral _ => 1
  	| SPNull
  	| SPMissing
  		=> 1                       
	| SPVarRef _
		=> 1                                  
	| SPFunctionCall _ l
		=> 1 + (List.fold_left (fun acc expr => acc + 1 + sqlpp_expr_size expr) l 0)
	| SPArray l
	| SPBag l
		=> 1 + (List.fold_left (fun acc expr => acc + 1 + sqlpp_expr_size expr) l 0)
	| SPObject l
		=> 1 + (List.fold_left (fun acc p => acc + (expr_pair_size p)) l 0)
	| SPQuery stmt
		=> 1 + (sqlpp_statement_size stmt)
      end
      
  with sqlpp_statement_size (stmt: sqlpp_select_statement) :=
  	match stmt with
  	| SPSelectStmt lets block unions (SPOrderBy orders)
  		=> 1 + (List.fold_left (fun acc p => acc + (string_expr_pair_size p)) lets 0) + (sqlpp_select_block_size block) +
  			(List.fold_left (fun acc u => acc + sqlpp_union_size u) unions 0) + 
  			(List.fold_left (fun acc o => acc + sqlpp_order_pair_size o) orders 0)
  	| SPSelectStmt lets block unions SPNoOrderBy
  		=> 1 + (List.fold_left (fun acc p => acc + (string_expr_pair_size p)) lets 0) + (sqlpp_select_block_size block) +
  			(List.fold_left (fun acc u => acc + sqlpp_union_size u) unions 0)
  	end
  	
  with sqlpp_select_block_size (block : sqlpp_select_block) := 
  	match block with
	| SPSelectBlock select froms lets1 whr groupby lets2 having
		=> 1 + (sqlpp_select_clause_size select) + (List.fold_left (fun acc fr => acc + (sqlpp_from_size fr)) froms 0) + 
			(List.fold_left (fun acc p => acc + (string_expr_pair_size p)) lets1 0) +
	    match whr with
	    | SPNoWhere => 0
	    | SPWhere e =>	1 + (sqlpp_expr_size e)
	    end + 
		 	(sqlpp_group_by_size groupby) + (List.fold_left (fun acc p => acc + (string_expr_pair_size p)) lets1 0) +
		match having with
		| None => 0
		| Some expr => sqlpp_expr_size expr
		end
  	end
  
  with sqlpp_union_size (union : sqlpp_union_element) :=
  	match union with
  	| SPBlock block => 1 + (sqlpp_select_block_size block)
  	| SPSubquery q => 1 + (sqlpp_statement_size q)
  	end

  with sqlpp_order_pair_size (order : (sqlpp_expr * sqlpp_order_spec)) :=
  	match order with
  	| (o, _) => 1 + (sqlpp_expr_size o)
  	end

  with sqlpp_select_clause_size (select : sqlpp_select) := 
  	match select with
  	| SPSelectSQL _ prs => 1 + (List.fold_left (fun acc pr => acc + (sqlpp_project_size pr)) prs 0)
  	| SPSelectValue _ val => 1 + (sqlpp_expr_size val)
  	end
  	
  with sqlpp_project_size (proj : sqlpp_project) :=
  	match proj with
  	| SPProject p => 1 + (sqlpp_expr_size (fst p))
  	| SPProjecStar => 1
  	end

  with sqlpp_group_by_size (groupby : sqlpp_group_by) := 1 (* TODO *)

  with sqlpp_from_size (from : sqlpp_from) := 1 (* TODO *)

  with whenthen_size (wt : sqlpp_when_then) :=
  	match wt with
  	| SPWhenThen w t
		=> 1 + (sqlpp_expr_size w) + (sqlpp_expr_size t)
	end
      
  with string_expr_pair_size (pair : (string * sqlpp_expr)) :=
	 1 + (sqlpp_expr_size (snd pair))
  	  
  with expr_pair_size (pair : (sqlpp_expr * sqlpp_expr)) :=
	1 + (sqlpp_expr_size (fst pair)) + (sqlpp_expr_size (snd pair)).
  	  
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
