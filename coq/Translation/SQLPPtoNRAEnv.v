 (*
 * Copyright 2015-2017 IBM Corporation.  Portions Copyright 2017 Joshua Auerbach.
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
Require Import CommonRuntime.
Require Import SQLPPRuntime.
Require Import NRAEnvRuntime.
Require Import SQLtoNRAEnv.

Section SQLPPtoNRAEnv.
  Context {fruntime:foreign_runtime}.

(* Translate two expressions and build the binary equality comparison (used as a subroutine for the SPSimpleCase clause) *)
Definition sqlpp_to_nraenv_SPEq sqlpp_to_nraenv (e1 e2:sqlpp_expr) : nraenv
  := NRAEnvBinop OpEqual (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2).
  
(* Indicates that expected functionality is not yet implemented.  *)
Definition sqlpp_to_nraenv_not_implemented (what : string) : nraenv :=
	NRAEnvConst (dstring ("NRAEnv translation not Implemented: " ++ what)).
           
(* Central translation function *)	
Fixpoint sqlpp_to_nraenv (q:sqlpp) : nraenv :=
  	match q with
	| SPPositive expr
		=> NRAEnvBinop (OpNatBinary NatPlus) (NRAEnvConst (dnat 0)) (sqlpp_to_nraenv expr)
	| SPNegative expr
        => NRAEnvBinop (OpNatBinary NatMinus) (NRAEnvConst (dnat 0)) (sqlpp_to_nraenv expr)
  	| SPExists expr
        => NRAEnvUnop OpNeg (NRAEnvBinop OpLe (NRAEnvUnop OpCount (sqlpp_to_nraenv expr)) (NRAEnvConst (dnat 0)))
  	| SPNot expr
  		=> NRAEnvUnop OpNeg (sqlpp_to_nraenv expr)
 	(* TODO: Our internal data model has null but not 'missing' (unless we add a new convention).  For now, both are translated
	   to null.  Also, we should really be using sum types to get around type problems like comparing a number to null. *)
  	| SPIsNull expr
  	| SPIsMissing expr
  	| SPIsUnknown expr
		=> NRAEnvBinop OpEqual (sqlpp_to_nraenv expr) (NRAEnvConst dunit)
	| SPPlus e1 e2
        => NRAEnvBinop (OpNatBinary NatPlus) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPMinus  e1 e2
        => NRAEnvBinop (OpNatBinary NatMinus) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPMult e1 e2
        => NRAEnvBinop (OpNatBinary NatMult) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPDiv e1 e2
        => NRAEnvBinop (OpNatBinary NatDiv) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPMod e1 e2
        => NRAEnvBinop (OpNatBinary NatRem) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPExp e1 e2
		=> sqlpp_to_nraenv_not_implemented "exp operator" (* TODO.  We either need our own binary exponent operator, or we need to
		      program out the logic (convert to floating point, perform operation then convert back depending on the expected type).
		      A possibly adequate "good enough for now" solution would be to define the operation when e1 and e2 are floating point
		      and not otherwise. *)
  	| SPConcat e1 e2
        => NRAEnvBinop OpStringConcat (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPIn e1 e2
        => NRAEnvBinop OpContains (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPEq  e1 e2
  	| SPFuzzyEq e1 e2 (* TODO.  We don't currently have "fuzzy equals" so translating as Eq for now *)
  		=> sqlpp_to_nraenv_SPEq sqlpp_to_nraenv e1 e2
  	| SPNeq  e1 e2
        => NRAEnvUnop OpNeg (NRAEnvBinop OpEqual (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2))
  	| SPLt  e1 e2
  		=> NRAEnvBinop OpLt (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPGt  e1 e2
  		=> NRAEnvBinop OpLt (sqlpp_to_nraenv e2) (sqlpp_to_nraenv e1)
  	| SPLe  e1 e2
  		=> NRAEnvBinop OpLe (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPGe  e1 e2
  		=> NRAEnvBinop OpLe (sqlpp_to_nraenv e2) (sqlpp_to_nraenv e1)
  	| SPLike  e s
  		=> NRAEnvUnop (OpLike s None) (sqlpp_to_nraenv e)
  	| SPAnd  e1 e2
  		=> NRAEnvBinop OpAnd (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPOr  e1 e2
  		=> NRAEnvBinop OpOr (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
	| SPBetween  e1 e2 e3
  		=> NRAEnvBinop OpAnd (NRAEnvBinop OpLe (sqlpp_to_nraenv e2) (sqlpp_to_nraenv e1))
                         (NRAEnvBinop OpLe (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e3))
	| SPSimpleCase value whenthens deflt
	  => 
           let last := match deflt with
	                   | Some dflt => sqlpp_to_nraenv dflt
	                   | None => NRAEnvConst dunit
	                   end 
           in
	   List.fold_right (fun wt acc =>
                              match
                                wt
                              with
                                SPWhenThen whn thn =>
                                nraenv_if (sqlpp_to_nraenv_SPEq sqlpp_to_nraenv whn value) (sqlpp_to_nraenv thn) acc
                              end) 
		           last whenthens
	| SPSearchedCase whenthens deflt
		=> let last := match deflt with
	                   | Some dflt => sqlpp_to_nraenv dflt
	                   | None => NRAEnvConst dunit
	                   end 
           in
		   List.fold_right (fun wt acc => match wt with SPWhenThen w t => nraenv_if (sqlpp_to_nraenv w) (sqlpp_to_nraenv t) acc end) 
		     last whenthens
    (* TODO: deferring translation of quantified expressions until select is translated since some of the infrastructure can be
       reused *)
	| SPSome  _ _
    | SPEvery _ _
    	=> sqlpp_to_nraenv_not_implemented "quantified expressions (SOME | EVERY)"
	| SPDot  expr name
		=> NRAEnvUnop (OpDot name) (sqlpp_to_nraenv expr)
    (* TODO: the index operation has no obvious translation since our internal data model has only bags, not ordered lists.  We could
      implement IndexAny without fixing this since order doesn't matter in a random selection, but we would have to tackle the issue
      of how to achieve randomness in Coq *)
	| SPIndex  _ _
	| SPIndexAny _
    	=> sqlpp_to_nraenv_not_implemented "indexing expressions"
	| SPLiteral d
		=> NRAEnvConst d
	(* TODO: Our internal data model has null but not 'missing' (unless we add a new convention).  For now, both are translated
	   to null *)
  	| SPNull
  	| SPMissing
  		=> NRAEnvConst dunit
	| SPVarRef name
		=> NRAEnvUnop (OpDot name) NRAEnvID
	| SPFunctionCall name args
		=> match name with
		| SPFget_year
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
		(* TODO: none of these are implemented yet.  The intent is to eventually implement (only) those in the explicit list of
		 well-known built-in functions above. Calls involving names not on the list are screened in the front-end and won't reach 
		 this function. *)
    	=> sqlpp_to_nraenv_not_implemented "function call expressions"
    	end
	(* Note: we don't have ordered lists in our data model so the distinction between array and bag isn't obvious.  We construct what our
	  data model calls a bag in both cases.  Because the elements of the constructor can be arbitrary expressions, we have to
	  construct the list programmatically.  Perhaps we should have a special case for when the elements are all constants, in which case
	  the resulting expression can be bag constant.  *)
	| SPArray items
	| SPBag items
		=> List.fold_right (fun expr acc => NRAEnvBinop OpBagUnion (sqlpp_to_nraenv expr) acc) (NRAEnvConst (dcoll nil)) items
	| SPObject items (*Note: we only support objects whose field names are literals. *)
        => List.fold_right (fun (item : (string * sqlpp)) acc => let (name , expr) := item in 
			NRAEnvBinop OpRecConcat (NRAEnvUnop (OpRec name) (sqlpp_to_nraenv expr)) acc) (NRAEnvConst (drec nil)) items
	| SPQuery stmt
		=> sqlpp_to_nraenv_not_implemented "select"
	end.

(* External entry point. *)
Definition sqlpp_to_nraenv_top := sqlpp_to_nraenv.

End SQLPPtoNRAEnv.

