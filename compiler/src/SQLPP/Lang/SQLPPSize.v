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

Require Import String.
Require Import ZArith.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.
Require Import SQLPP.
  
Section SQLPPSize.
  Context {fruntime:foreign_runtime}.

  Section size.
  	Definition sqlpp_string_option_size (name : option string) :=
	match name with
		| None => 0
		| Some _ => 1
	end.
  
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
  	| SPAnd  e1 e2
  	| SPOr  e1 e2
  		=> 1 + (sqlpp_expr_size  e1) + (sqlpp_expr_size  e2)
  	| SPLike  e1 e2
  		=> 1 + (sqlpp_expr_size  e1)
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
		=> 1 + (List.fold_left (fun acc p => acc + (1 + (sqlpp_expr_size (snd p)))) l 0) + (sqlpp_expr_size  e)
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
		=> 1 + (List.fold_left (fun acc pair => acc + (1 + (sqlpp_expr_size (snd pair)))) l 0)
	| SPQuery stmt
		=> 1 + (sqlpp_statement_size stmt)
      end
      
  with sqlpp_statement_size (stmt: sqlpp_select_statement) :=
  	match stmt with
  	| SPSelectStmt lets block unions (SPOrderBy orders)
  		=> 1 + (List.fold_left (fun acc p => acc + (1 + (sqlpp_expr_size (snd p)))) lets 0) + (sqlpp_select_block_size block) +
  			(List.fold_left (fun acc u => acc + sqlpp_union_size u) unions 0) + 
  			(List.fold_left (fun acc o => acc + (let '(oo,_) := o in 1 + (sqlpp_expr_size oo))) orders 0)
  	| SPSelectStmt lets block unions SPNoOrderBy
  		=> 1 + (List.fold_left (fun acc p => acc + (1 + (sqlpp_expr_size (snd p)))) lets 0) + (sqlpp_select_block_size block) +
  			(List.fold_left (fun acc u => acc + sqlpp_union_size u) unions 0)
  	end
  	
  with sqlpp_select_block_size (block : sqlpp_select_block) := 
  	match block with
	| SPSelectBlock select froms lets1 whr groupby lets2 having
		=> 1 + (sqlpp_select_clause_size select) + (List.fold_left (fun acc fr => acc + (sqlpp_from_size fr)) froms 0) + 
			(List.fold_left (fun acc p => acc + (1 + (sqlpp_expr_size (snd p)))) lets1 0) +
	    match whr with
	    | SPNoWhere => 0
	    | SPWhere e =>	1 + (sqlpp_expr_size e)
	    end + 
		 	(sqlpp_group_by_size groupby) + (List.fold_left (fun acc p => acc + (1 + (sqlpp_expr_size (snd p)))) lets1 0) +
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

  with sqlpp_group_by_size (groupby : sqlpp_group_by) :=
  	match groupby with
  	| SPNoGroupBy => 0
  	| SPGroupBy groups aspart => 1 + (List.fold_left (fun acc g => acc + (let '(gg,_) := g in 1 + (sqlpp_expr_size gg))) groups 0) +
  		match aspart with
  		| None => 0
  		| Some (_ , pairs) => 1 + 2 * (List.length pairs)
  		end
	end

  with sqlpp_from_size (from : sqlpp_from) := 
  	match from with
  	| SPFrom expr name joins => 1 + (sqlpp_expr_size expr) + (sqlpp_string_option_size name) + 
  		(List.fold_left (fun acc join => acc + (sqlpp_join_size join)) joins 0)
  	end
  	
  with sqlpp_join_size (join : sqlpp_join_clause) :=
  	match join with
  	| SPJoin _ expr name onexpr => 2 + (sqlpp_expr_size expr) + (sqlpp_string_option_size name) + (sqlpp_expr_size onexpr)
  	| SPUnnest _ expr asname atname => 2 + (sqlpp_expr_size expr) + (sqlpp_string_option_size asname) + (sqlpp_string_option_size atname)
  	end

  with whenthen_size (wt : sqlpp_when_then) :=
  	match wt with
  	| SPWhenThen w t
		=> 1 + (sqlpp_expr_size w) + (sqlpp_expr_size t)
	end
    .
    
  Definition sqlpp_size (e : sqlpp_expr) := sqlpp_expr_size e.

  End size.

  Section depth.
	Fixpoint sqlpp_expr_depth (e : sqlpp_expr) :=
	match e with
	| SPPositive expr
	| SPNegative expr
  	| SPExists expr
  	| SPNot expr
  	| SPIsNull expr
  	| SPIsMissing expr
  	| SPIsUnknown expr
  		=> sqlpp_expr_depth expr
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
  	| SPAnd  e1 e2
  	| SPOr  e1 e2
  		=> max (sqlpp_expr_depth e1) (sqlpp_expr_depth e2)
  	| SPLike  e1 e2
  		=> sqlpp_expr_depth e1
	| SPBetween  e1 e2 e3
		=> max (sqlpp_expr_depth e1) (max (sqlpp_expr_depth e2) (sqlpp_expr_depth e3))
	| SPSimpleCase  e l o
		=> match o with
		| None => max (sqlpp_expr_depth e) (List.fold_left (fun acc whenthen => max acc (whenthen_depth whenthen)) l 0)
		| Some oe => max (sqlpp_expr_depth e) 
			(max (List.fold_left (fun acc whenthen => max acc (whenthen_depth whenthen)) l 0) (sqlpp_expr_depth oe))
		end
	| SPSearchedCase l o
		=> match o with
		| None => (List.fold_left (fun acc whenthen => max acc (whenthen_depth whenthen)) l 0)
		| Some oe => max (List.fold_left (fun acc whenthen => max acc (whenthen_depth whenthen)) l 0) (sqlpp_expr_depth oe)
		end
	| SPSome  l e
    | SPEvery l e
		=> max (List.fold_left (fun acc p => max acc (sqlpp_expr_depth (snd p))) l 0) (sqlpp_expr_depth  e)
	| SPDot  expr _
		=> sqlpp_expr_depth  expr                                                              
	| SPIndex  e i
		=> max  (sqlpp_expr_depth  e) (sqlpp_expr_depth  i)
	| SPIndexAny e
		=> sqlpp_expr_depth e
	| SPLiteral _ => 0
  	| SPNull
  	| SPMissing
  		=> 0             
	| SPVarRef _
		=> 0                                  
	| SPFunctionCall _ l
		=> (List.fold_left (fun acc expr => max acc (sqlpp_expr_depth expr)) l 0)
	| SPArray l
	| SPBag l
		=> (List.fold_left (fun acc expr => max acc (sqlpp_expr_depth expr)) l 0)
	| SPObject l
		=> List.fold_left (fun acc pair => max acc (sqlpp_expr_depth (snd pair))) l 0
	| SPQuery stmt
		=> sqlpp_statement_depth stmt
	end
      
  with sqlpp_statement_depth (stmt: sqlpp_select_statement) :=
  	match stmt with
  	| SPSelectStmt lets block unions (SPOrderBy orders)
  		=> max (max (max (List.fold_left (fun acc p => max acc (sqlpp_expr_depth (snd p))) lets 0) (sqlpp_select_block_depth block))
  			(List.fold_left (fun acc u => max acc (sqlpp_union_depth u)) unions 0)) 
  			(List.fold_left (fun acc o => max acc (let '(oo,_) := o in (sqlpp_expr_depth oo))) orders 0)
  	| SPSelectStmt lets block unions SPNoOrderBy
  		=> max (max (List.fold_left (fun acc p => max acc (sqlpp_expr_depth (snd p))) lets 0) (sqlpp_select_block_depth block))
  			(List.fold_left (fun acc u => max acc (sqlpp_union_depth u)) unions 0)
  	end
  	
  with sqlpp_select_block_depth (block : sqlpp_select_block) := 
  	match block with
	| SPSelectBlock select froms lets1 whr groupby lets2 having
		=> max (sqlpp_select_clause_depth select) 
		   (max (List.fold_left (fun acc fr => max acc (sqlpp_from_depth fr)) froms 0) 
		   (max (List.fold_left (fun acc p => max acc (sqlpp_expr_depth (snd p))) lets1 0)
	       (max (match whr with
	       | SPNoWhere => 0
	       | SPWhere e =>	sqlpp_expr_depth e
	       end)  
		   (max (sqlpp_group_by_depth groupby)
		   (max (List.fold_left (fun acc p => max acc (sqlpp_expr_depth (snd p))) lets1 0)
		   (match having with
		   | None => 0
		   | Some expr => sqlpp_expr_depth expr
		   end))))))
  	end
  
  with sqlpp_union_depth (union : sqlpp_union_element) :=
  	match union with
  	| SPBlock block => sqlpp_select_block_depth block
  	| SPSubquery q => sqlpp_statement_depth q
  	end

  with sqlpp_select_clause_depth (select : sqlpp_select) := 
  	match select with
  	| SPSelectSQL _ prs => List.fold_left (fun acc pr => max acc (sqlpp_project_depth pr)) prs 0
  	| SPSelectValue _ val => sqlpp_expr_depth val
  	end
  	
  with sqlpp_project_depth (proj : sqlpp_project) :=
  	match proj with
  	| SPProject p => sqlpp_expr_depth (fst p)
  	| SPProjectStar => 1
  	end

  with sqlpp_group_by_depth (groupby : sqlpp_group_by) :=
  	match groupby with
  	| SPNoGroupBy => 0
  	| SPGroupBy groups aspart => max (List.fold_left (fun acc g => acc + (let '(gg,_) := g in 1 + (sqlpp_expr_depth gg))) groups 0)
  		match aspart with
  		| None => 0
  		| Some (_ , pairs) => 1 + 2 * (List.length pairs)
  		end
	end

  with sqlpp_from_depth (from : sqlpp_from) := 
  	match from with
  	| SPFrom expr _ joins => max (sqlpp_expr_depth expr)
  		(List.fold_left (fun acc join => max acc (sqlpp_join_depth join)) joins 0)
  	end
  	
  with sqlpp_join_depth (join : sqlpp_join_clause) :=
  	match join with
  	| SPJoin _ expr _ onexpr => max (sqlpp_expr_depth expr) (sqlpp_expr_depth onexpr)
  	| SPUnnest _ expr _ _ => sqlpp_expr_depth expr
  	end

  with whenthen_depth (wt : sqlpp_when_then) :=
  	match wt with
  	| SPWhenThen w t
		=> max (sqlpp_expr_depth w) (sqlpp_expr_depth t)
	end
    .
      
   Definition sqlpp_depth (e : sqlpp_expr) := sqlpp_expr_depth e. 

  End depth.

End SQLPPSize.

