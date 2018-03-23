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
package org.qcert.camp.rule;

import org.qcert.camp.CampMacros;
import org.qcert.camp.pattern.CampPattern;
import org.qcert.camp.pattern.LetEnvPattern;
import org.qcert.camp.pattern.UnaryOperator;
import org.qcert.camp.pattern.UnaryPattern;

/**
 * Represents rule_not in the Rule macro language
 */
public final class NotRule extends PatternRule {
	/**
	 * Make a NotRule in functional form, given its pattern
	 */
	public NotRule(CampPattern pattern) {
		super(pattern, null);
	}
	
	/**
	 * Make a new NotRule from a functional NotRule and an operand 
	 * @param functional the functional NotRule
	 * @param operand the operand
	 */
	private NotRule(NotRule functional, CampRule operand) {
		super(functional.getPattern(), operand);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#apply(org.qcert.camp.rule.CampRule)
	 */
	@Override
	public CampRule applyTo(CampRule operand) {
		return new NotRule(this, operand);
	}

	/**
	 * Implement according to logic in rule_to_pattern in Coq code
         | rule_not p ps =>
           punop OpFlatten
                 (makeSingleton
                    (pletEnv
                       (notholds p RETURN BINDINGS)
                       (rule_to_pattern ps)))
	 * @see org.qcert.camp.rule.CampRule#convertToPattern()
	 */
	@Override
	public CampPattern convertToPattern() {
		CampPattern not = CampMacros.notholds(CampMacros.RETURN(getPattern(), CampMacros.BINDINGS()));
		CampPattern single = CampMacros.makeSingleton(new LetEnvPattern(not, getOperand().convertToPattern()));
		return new UnaryPattern(UnaryOperator.OpFlatten, single);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.Not;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "rule_not (" + getPattern() + ") ;; " + getOperand();
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "rule_not";
	}
}
