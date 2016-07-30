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
import org.qcert.camp.pattern.LetEnvPattern;
import org.qcert.camp.pattern.UnaryOperator;
import org.qcert.camp.pattern.UnaryPattern;

/**
 * Static macro constructions on top of Rules or CAMP
 */
public class CampMacros {
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
	
	/** The ^ macro from the paper, called 'pand' in the coq */
	public static LetEnvPattern pand(CampPattern asserted, CampPattern successor) {
		return new LetEnvPattern(new AssertPattern(asserted), successor);
	}
	
	/** A convenient macro for ARec */
	public static UnaryPattern rec(String name, CampPattern value) {
		return new UnaryPattern(UnaryOperator.ARec, name, value);
	}
}
