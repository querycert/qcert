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

Section SQLPPtoNRAEnv.
  Require Import String.
  Require Import ZArith.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import BasicSystem.
  Require Import RDataSort. (* For SortCriterias *)
  Require Import SQLPP.
  Require Import SQLtoNRAEnv.
  Require Import NRAEnvRuntime.

  Context {fruntime:foreign_runtime}.

(** Converts the most general form of a when/then clause
  (in which the 'when' part isn't necessarily boolean) into a specific form where it is certainly boolean. *)	
Definition sqlpp_make_when_then_boolean  (value : sqlpp) (whenthen : sqlpp_when_then) : sqlpp_when_then :=
	match whenthen with
	| SPWhenThen whn thn => SPWhenThen (SPEq whn value) thn
	end.

(** Convert the list of when/then clauses in a simple case expression to the form used in a searched case expression
   to aid in efficient factoring of code *)
Definition sqlpp_absorb_value (value : sqlpp) (whenthens : list sqlpp_when_then) : list sqlpp_when_then := 
	List.map (sqlpp_make_when_then_boolean  value) whenthens.

(* Central translation function *)	
Fixpoint sqlpp_to_nraenv (q:sqlpp) : nraenv :=
  	match q with
	| SPPositive expr
		=> NRAEnvBinop (ABArith ArithPlus) (NRAEnvConst (dnat 0)) (sqlpp_to_nraenv expr)
	| SPNegative expr
        => NRAEnvBinop (ABArith ArithMinus) (NRAEnvConst (dnat 0)) (sqlpp_to_nraenv expr)
  	| SPExists expr
        => NRAEnvUnop ANeg (NRAEnvBinop ALe (NRAEnvUnop ACount (sqlpp_to_nraenv expr)) (NRAEnvConst (dnat 0)))
  	| SPNot expr
  		=> NRAEnvUnop ANeg (sqlpp_to_nraenv expr)
  	| SPIsNull expr
  	| SPIsMissing expr
  	| SPIsUnknown expr
		=> NRAEnvConst dunit (* TODO: what is the correct translation of null / missing / unknown in a data model in which (usually) only
		 				objects are optional?  Do we need a revised data model for SQL++? *)
	| SPPlus e1 e2
        => NRAEnvBinop (ABArith ArithPlus) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPMinus  e1 e2
        => NRAEnvBinop (ABArith ArithMinus) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPMult e1 e2
        => NRAEnvBinop (ABArith ArithMult) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPDiv e1 e2
        => NRAEnvBinop (ABArith ArithDivide) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPMod e1 e2
        => NRAEnvBinop (ABArith ArithRem) (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPExp e1 e2
		=> NRAEnvConst dunit (* TODO.  We either need our own binary exponent operator, or this is a foreign operator, or we need to
		      program out the logic (convert to floating point and back, or whatever) *)
  	| SPConcat e1 e2
        => NRAEnvBinop ASConcat (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPIn e1 e2
        => NRAEnvBinop AContains (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPEq  e1 e2
  	| SPFuzzyEq e1 e2 (* TODO.  We don't currently have "fuzzy equals" so translating as Eq for now *)
  		=> NRAEnvBinop AEq (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPNeq  e1 e2
        => NRAEnvUnop ANeg (NRAEnvBinop AEq (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2))
  	| SPLt  e1 e2
  		=> NRAEnvBinop ALt (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPGt  e1 e2
  		=> NRAEnvBinop ALt (sqlpp_to_nraenv e2) (sqlpp_to_nraenv e1)
  	| SPLe  e1 e2
  		=> NRAEnvBinop ALe (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPGe  e1 e2
  		=> NRAEnvBinop ALe (sqlpp_to_nraenv e2) (sqlpp_to_nraenv e1)
  	| SPLike  e s
  		(* TODO: modeling on the SQL equivalent, it would be nice to use:
  		=> NRAEnvUnop (ALike s None) (sqlpp_to_nraenv e)
  		However, in SQL++ the RHS of 'like' may be any expression of string type, and is not constrained to be a string literal.  So,
  		the static type of s is sqlpp_expr, not string. *)
  		=> NRAEnvConst dunit
  	| SPAnd  e1 e2
  		=> NRAEnvBinop AAnd (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
  	| SPOr  e1 e2
  		=> NRAEnvBinop AOr (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e2)
	| SPBetween  e1 e2 e3
  		=> NRAEnvBinop AAnd (NRAEnvBinop ALe (sqlpp_to_nraenv e2) (sqlpp_to_nraenv e1))
                         (NRAEnvBinop ALe (sqlpp_to_nraenv e1) (sqlpp_to_nraenv e3))
	| SPSimpleCase value whenthens deflt
	    (* TODO: This is apparently not contractive enough to satisfy Coq
		=> let canonical := sqlpp_absorb_value value whenthens in
           let last := match deflt with
	                   | Some dflt => sqlpp_to_nraenv dflt
	                   | None => NRAEnvConst dunit
	                   end 
           in
		   List.fold_right (fun wt acc => match wt with SPWhenThen w t => nraenv_if (sqlpp_to_nraenv w) (sqlpp_to_nraenv t) acc end) 
		     last canonical
		 *)
		=> NRAEnvConst dunit
	| SPSearchedCase whenthens deflt
	    (* TODO: This is apparently not contractive enough to satisfy Coq
		=> let last := match deflt with
	                   | Some dflt => sqlpp_to_nraenv dflt
	                   | None => NRAEnvConst dunit
	                   end 
           in
		   List.fold_right (fun wt acc => match wt with SPWhenThen w t => nraenv_if (sqlpp_to_nraenv w) (sqlpp_to_nraenv t) acc end) 
		     last whenthens
		*)
		=> NRAEnvConst dunit
    (* TODO: deferring translation of quantified expressions since there is no good precedent in plain SQL *)
	| SPSome  _ _
    | SPEvery _ _
    	=> NRAEnvConst dunit
	| SPDot  expr name
		=> NRAEnvUnop (ADot name) (sqlpp_to_nraenv expr)
    (* TODO the index operation has no obvious translation since our internal data model has only bags, not ordered lists *)
	| SPIndex  _ _
	| SPIndexAny _
    	=> NRAEnvConst dunit
	| SPLiteral _(* TODO remainder *)
  	| SPNull
  	| SPMissing
	| SPVarRef _
	| SPFunctionCall _ _
	| SPArray _ (* TODO Note: we don't have ordered lists in our data model so the distinction between array and bag isn't obvious *)
	| SPBag _
	| SPObject _ (* TODO Note: the best we are likely to do is support objects whose field names are literals.  Consider adding that
	    restriction to the SQL++ front-end *)
	| SPQuery _
		=> NRAEnvConst dunit (* TODO: placeholder *)
	end.

(* External entry point. *)
Definition sqlpp_to_nraenv_top := sqlpp_to_nraenv.

End SQLPPtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
