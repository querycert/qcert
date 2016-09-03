/**
 * Copyright (C) 2016 Joshua Auerbach 
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

import org.qcert.camp.pattern.AssertPattern;
import org.qcert.camp.pattern.BinaryOperator;
import org.qcert.camp.pattern.BinaryPattern;
import org.qcert.camp.pattern.CampPattern;
import org.qcert.camp.pattern.ConstPattern;
import org.qcert.camp.pattern.GetConstPattern;
import org.qcert.camp.pattern.LetEnvPattern;
import org.qcert.camp.pattern.LetItPattern;
import org.qcert.camp.pattern.MapPattern;
import org.qcert.camp.pattern.UnaryOperator;
import org.qcert.camp.pattern.UnaryPattern;

/**
 * Static macro constructions on top of Rules or CAMP
 */
public class CampMacros {
	/** A macro equivalent to the 'BINDINGS' notation in Coq, defined as (pWithBindings pit)
	  Definition pWithBindings : pat -> pat := pletIt penv.
	*/
	public static CampPattern BINDINGS() {
		return new LetItPattern(CampPattern.ENV, CampPattern.IT);
	}
	
	/** A convenient macro for AConcat */
	public static BinaryPattern concat(CampPattern left, CampPattern right) {
		return new BinaryPattern(BinaryOperator.AConcat, left, right);
	}
	
	/** A convenient macro for 'dot' */
	public static UnaryPattern dot(CampPattern receiver, String field) {
		return new UnaryPattern(UnaryOperator.ADot, field, receiver);
	}
	
	/** A convenient macro for equality of two patterns */
	public static BinaryPattern eq(CampPattern left, CampPattern right) {
		return new BinaryPattern(BinaryOperator.AEq, left, right);
	}
	
	/** A convenient macro equivalent to makeSingleton in Coq code
      Definition makeSingleton (p:pat) : pat := punop AColl p.
	 */
	public static CampPattern makeSingleton(CampPattern p) {
		return new UnaryPattern(UnaryOperator.AColl, p);
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

	/** A convenient macro for ARec */
	public static UnaryPattern rec(String name, CampPattern value) {
		return new UnaryPattern(UnaryOperator.ARec, name, value);
	}

	/** A macro equivalent to the 'RETURN' notion in Coq (which is an infix for pletEnv) */
	public static CampPattern RETURN(CampPattern op1, CampPattern op2) {
		return new LetEnvPattern(op1,  op2);
	}

	/** A macro equivalent to the WW macro in coq, used in rule expansion
	   Definition WW p := pletIt (pgetconstant ("WORLD")) p.
	 */
	public static CampPattern WW(CampPattern p) {
		return new LetItPattern(new GetConstPattern("WORLD"), p);
	}

	/** A macro equivalent to the mapsnone macro on coq
      Definition mapsnone p := (punop ACount (pmap p) == 0).
	 **/
	private static CampPattern mapsnone(CampPattern p) {
		CampPattern count = new UnaryPattern(UnaryOperator.ACount, new MapPattern(p));
		return eq(count, new ConstPattern(0));
	}
}
