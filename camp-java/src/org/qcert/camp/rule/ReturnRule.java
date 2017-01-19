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

/**
 * Represnts rule_return in the Rule macro language 
 */
public final class ReturnRule extends PatternRule {
	/**
	 * Make a ReturnRule given its pattern
	 */
	public ReturnRule(CampPattern pattern) {
		super(pattern, null); // never has a rule operand
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#apply(org.qcert.camp.rule.CampRule)
	 */
	@Override
	public CampRule applyTo(CampRule operand) {
		throw new IllegalStateException("A ReturnRule cannot be applied as a function");
	}

	/**
	 * Implement according to logic in rule_to_pattern in Coq code
         | rule_return p =>
           makeSingleton p
	 * @see org.qcert.camp.rule.CampRule#convertToPattern()
	 */
	@Override
	public CampPattern convertToPattern() {
		return CampMacros.makeSingleton(getPattern());
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.Return;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "rule_return (" + getPattern() + ")";
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "rule_return";
	}
}
