/**
 * Copyright (C) 2016-2017 Joshua Auerbach 
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
 */
package org.qcert.camp;

import java.util.Collections;
import java.util.List;
import java.util.UUID;

import org.qcert.camp.data.CampData;
import org.qcert.camp.pattern.AssertPattern;
import org.qcert.camp.pattern.BinaryOperator;
import org.qcert.camp.pattern.BinaryPattern;
import org.qcert.camp.pattern.CampPattern;
import org.qcert.camp.pattern.CompoundPattern;
import org.qcert.camp.pattern.ConstPattern;
import org.qcert.camp.pattern.GetConstPattern;
import org.qcert.camp.pattern.LetEnvPattern;
import org.qcert.camp.pattern.LetItPattern;
import org.qcert.camp.pattern.MapPattern;
import org.qcert.camp.pattern.UnaryOperator;
import org.qcert.camp.pattern.UnaryPattern;
import org.qcert.camp.rule.CampRule;
import org.qcert.camp.rule.ReturnRule;

/**
 * Static macro constructions on top of Rules or CAMP
 */
public class CampMacros {
	private CampMacros() {}
	
	/**	 A macro equivalent to the 'paccept' sugar in Coq, defined as pconst (drec nil). */
	public static CampPattern accept() {
		return new ConstPattern(CampData.EMPTY_REC);
	}

	/** A macro equivalent to the aggregate function in Coq:
      Definition aggregate (rules:rule->rule) (op:unaryOp) (secondMap:pat) (nflat:nat): pat
        :=  pletIt
          (rule_to_pattern (rules (rule_return penv)))
          (punop op (flattenn nflat (pmap (pletEnv pit secondMap)))).
	 */
	public static CampPattern aggregate(CampRule rule, UnaryOperator op, CampPattern secondMap, int nflat) {
		CampPattern convertedRule = rule.applyTo(new ReturnRule(CampPattern.ENV)).convertToPattern();
		CampPattern peSecond = new LetEnvPattern(CampPattern.IT, secondMap);
		CampPattern puMap = new UnaryPattern(op, flattenn(new MapPattern(peSecond), nflat));
		return new LetItPattern(convertedRule, puMap);
	}
	
	/** A macro equivalent to the 'BINDINGS' notation in Coq, defined as (pWithBindings pit)
	  Definition pWithBindings : pat -> pat := pletIt penv.
	*/
	public static CampPattern BINDINGS() {
		return new LetItPattern(CampPattern.ENV, CampPattern.IT);
	}

	/** A convenient macro for OpRecConcat */
	public static BinaryPattern concat(CampPattern left, CampPattern right) {
		return new BinaryPattern(BinaryOperator.OpRecConcat, left, right);
	}
	
	/** A convenient macro for 'dot' */
	public static UnaryPattern dot(CampPattern receiver, String field) {
		return new UnaryPattern(UnaryOperator.OpDot, field, receiver);
	}
	
	/** A convenient macro for equality of two patterns */
	public static BinaryPattern eq(CampPattern left, CampPattern right) {
		return new BinaryPattern(BinaryOperator.OpEqual, left, right);
	}
	
	/** A macro equivalent to the fetchRef function in Coq, with 'keyval' implicitly bound to 'it':
	 *  Definition fetchRef (entity:brands) (keyatt:string) (tempvar:string) (keyval:pat) : pat -> pat
	 *    := pletIt
	 *         (pletEnv (pvarwith tempvar keyval)
	 *                  (WW
	 *                     (pletIt
	 *                        (pmap
	 *                           (pletIt (pcast entity) (pand ((pletIt punbrand (keyatt #-> pit) |p-eq| (lookup tempvar))) pit)))
	 *	                    psingleton))).
	 */
	public static CampPattern fetchRef(String brand, String keyatt) {
		final String tempVar = "tmp" + UUID.randomUUID().toString().substring(0,8);
		CampPattern pvarwith = varWith(tempVar, CampPattern.IT);
		CampPattern lookup = lookup(tempVar);
		CampPattern letItPcastPand = new LetItPattern(cast(brand), pandClause(lookup, keyatt));
		CampPattern letItPmap = new LetItPattern(new MapPattern(letItPcastPand), singleton());
		CampPattern letEnv = new LetEnvPattern(pvarwith, WW(letItPmap));
		return new LetItPattern(letEnv);
	}
	
	/**  A macro equivalent to the instanceof sugar in Coq:
	 * Definition instanceOf n t p := namedObject n t (p RETURN BINDINGS).
	 */
	public static CampPattern instanceOf(String varName, String typeName, CampPattern tests) {
		CampPattern returnBindings = RETURN(tests, BINDINGS());
		return namedObject(varName, typeName, returnBindings);
	}

	/** A macro equivalent to the IS notation backed by the pIs function in Coq
	 * Definition pIS var p := pletIt p (pvar var).
	 * Definition pvar f : pat := pvarwith f pit.
	 */
	public static CampPattern is(String varName, CampPattern pattern) {
		CampPattern pvar = varWith(varName, CampPattern.IT);
		return new LetItPattern(pattern, pvar);
	}

	/** A macro equivalent to the lookup function in Coq:
	 * Definition lookup c := (pWithBindings (pdot c pit)).
	 * Definition pWithBindings : pat -> pat := pletIt penv.
	 */
	public static CampPattern lookup(String var) {
		CampPattern pWithBindings = new LetItPattern(CampPattern.ENV);
		CampPattern pdot = dot(CampPattern.IT, var);
		return pWithBindings.applyTo(pdot);
	}

	/** A convenient macro equivalent to makeSingleton in Coq code
      Definition makeSingleton (p:pat) : pat := punop OpBag p.
	 */
	public static CampPattern makeSingleton(CampPattern p) {
		return new UnaryPattern(UnaryOperator.OpBag, p);
	}

	/** A macro equivalent to the matches function in Coq:
	 *  Definition matches t p := typedObject t (p RETURN BINDINGS).
	 */
	public static CampPattern matches(String typeName, CampPattern tests) {
		CampPattern returnBindings = RETURN(tests, BINDINGS());
		return typedObject(typeName, returnBindings);
	}

	/** A convenient macro for the notholds PatternSugar function
       Definition notholds p := WW (mapsnone p).
	 */
	public static CampPattern notholds(CampPattern p) {
		return WW(mapsnone(p));
	}

	/** The ^ macro from the paper, called 'pand' in the coq */
	public static LetEnvPattern pand(CampPattern asserted, CampPattern successor) {
		return new LetEnvPattern(new AssertPattern(asserted), successor);
	}

	/** A convenient macro for OpRec */
	public static UnaryPattern rec(String name, CampPattern value) {
		return new UnaryPattern(UnaryOperator.OpRec, name, value);
	}

	/** A macro equivalent to the 'RETURN' notion in Coq (which is an infix for pletEnv) */
	public static CampPattern RETURN(CampPattern op1, CampPattern op2) {
		return new LetEnvPattern(op1,  op2);
	}

	/** Convenience macro for toString */
	public static UnaryPattern stringify(CampPattern arg) {
		return new UnaryPattern(UnaryOperator.OpToString, arg);
	}

	/** A macro equivalent to the pbdot (unbrand dot) function in Coq but with the 'p' argument elided (partially applied)
	 * Definition pbdot s p : pat := (pletIt punbrand (pdot s p)).
   	 * Definition punbrand := punbrand' pit.
	 * Definition punbrand' p := punop AUnbrand p.
	 * Definition pdot f : pat -> pat := pletIt (punop (ADot f) pit).
	 */
	public static CampPattern unbrandDot(String name) {
		CampPattern pdot = new LetItPattern(dot(CampPattern.IT, name));
		CampPattern punbrand = unbrandIt();
		return new CompoundPattern(new LetItPattern(punbrand), pdot);
	}

	/** Convenience macro for unbranding "it" */
	public static UnaryPattern unbrandIt() {
		return new UnaryPattern(UnaryOperator.OpUnbrand, CampPattern.IT);
	}

	/** A macro equivalent to the VARIABLES notation, fronting for returnVariables function:
	 *   Definition returnVariables (sl:list string) : pat
     *      := punop (OpRecProject sl) penv.
	 */
	public static CampPattern variables(List<String> variableNames) {
		return new UnaryPattern(UnaryOperator.OpRecProject, variableNames, CampPattern.ENV);
	}

	/** A macro equivalent to the varWith function in Coq:
	 * Definition pvarwith f : pat -> pat := punop (OpRec f).
	 * @see org.qcert.camp.translator.CampASTNode#expand()
	 */
	public static CampPattern varWith(String variableName, CampPattern operand) {
		return new UnaryPattern(UnaryOperator.OpRec, variableName, operand);
	}

	/** A macro equivalent to the WW macro in coq, used in rule expansion
	   Definition WW p := pletIt (pgetconstant ("WORLD")) p.
	 */
	public static CampPattern WW(CampPattern p) {
		return new LetItPattern(new GetConstPattern("WORLD"), p);
	}

	/** A macro equivalent to the cast sugar in Coq:
	 * Definition pcast' b p:= pletIt (punop (OpCast b) p) psome.
     * Definition pcast b := pcast' b pit.
     * ... := pletIt (punop (OpCast b) pit) psome
	 */
	private static CampPattern cast(String typeName) {
		CampPattern punopCast = new UnaryPattern(UnaryOperator.OpCast, Collections.singletonList(typeName), CampPattern.IT);
		return new LetItPattern(punopCast, CampPattern.LEFT);
	}

	/** A macro equivalent to the flattenn fixpoint in Coq:
  	  Fixpoint flattenn (n:nat) (p:pat)
         := match n with
       	  | 0 => p
       	  | S m =>flattenn m (punop OpFlatten p)
      end.
	 */
	private static CampPattern flattenn(CampPattern pattern, int count) {
		if (count == 0)
			return pattern;
		return flattenn(new UnaryPattern(UnaryOperator.OpFlatten, pattern), count - 1);
	}

	/** A macro equivalent to the mapsnone macro on coq
      Definition mapsnone p := (passert (pbinop OpEqual (punop OpCount (pmap p)) 0)).
	 **/
	private static CampPattern mapsnone(CampPattern p) {
		CampPattern count = new UnaryPattern(UnaryOperator.OpCount, new MapPattern(p));
		return new AssertPattern(eq(count, new ConstPattern(0)));
	}

	/**  A macro equivalent to the namedObject sugar in Coq:
	 *    	Definition namedObject (varName:string) (type:brands) (p:pat) :=
	 *    		pletIt (pcast type)
	 *           		(pletEnv (pvar varName)
	 *                    p).
	 *      Definition pvar f : pat := pvarwith f pit.
	 */
	private static CampPattern namedObject(String varName, String typeName, CampPattern refinement) {
		CampPattern cast = cast(typeName);
		CampPattern pvar = varWith(varName, CampPattern.IT);
		CampPattern letEnvPvarP = new LetEnvPattern(pvar, refinement);
		return new LetItPattern(cast, letEnvPvarP);
	}

	/**
	 * Fragment of the full fetchRef definition consisting of
	 * (pand ((pletIt punbrand (keyatt #-> pit) |p-eq| (lookup tempvar))) pit)
	 *   Definition pand (p1 p2:pat):= pletEnv (passert p1) p2.
         Definition punbrand' p := punop OpUnbrand p.
         Definition punbrand := punbrand' pit.
         Notation "s #-> p" := (pdot s p)
         Definition pdot f : pat -> pat := pletIt (punop (OpDot f) pit).
	 */
	private static CampPattern pandClause(CampPattern lookup, String keyatt) {
		CampPattern pdot = dot(CampPattern.IT, keyatt);
		CampPattern punbrand = unbrandIt(); // p is bound to 'it' in this treatment
		CampPattern letItUnbrandPdot = new LetItPattern(punbrand, pdot);
		CampPattern eq = new BinaryPattern(BinaryOperator.OpEqual, letItUnbrandPdot, lookup);
		return new LetEnvPattern(new AssertPattern(eq), CampPattern.IT);
	}

	/** A macro equivalent to the psingleton function in Coq:
       Definition psingleton' p := pletIt (punop OpSingleton p) psome.
       Definition psingleton := psingleton' pit.
	 */
	private static CampPattern singleton() {
		CampPattern unsing = new UnaryPattern(UnaryOperator.OpSingleton, CampPattern.IT);
		return new LetItPattern(unsing, CampPattern.LEFT);
	}

	/** A macro equivalent to the typedObject function in Coq:
	 *   Definition typedObject (type:brands) (p:pat) := pletIt (pcast type) p.
	 */
	private static CampPattern typedObject(String typeName, CampPattern operand) {
		return new LetItPattern (cast(typeName), operand);
	}
}
