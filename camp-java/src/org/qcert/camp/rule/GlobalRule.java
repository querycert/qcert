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
package org.qcert.camp.rule;

import org.qcert.camp.pattern.CampPattern;

/**
 * Represnts rule_global in the Rule macro language 
 */
public final class GlobalRule extends PatternRule {
	/**
	 * Make a new GlobalRule in functional form, given its pattern
	 */
	public GlobalRule(CampPattern pattern) {
		super(pattern, null);
	}
	
	/**
	 * Make a new GlobalRule from a functional GlobalRule and an operand 
	 * @param functional the functional GlobalRule
	 * @param operand the operand
	 */
	private GlobalRule(GlobalRule functional, CampRule operand) {
		super(functional.getPattern(), operand);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#apply(org.qcert.camp.rule.CampRule)
	 */
	@Override
	public CampRule apply(CampRule operand) {
		return new GlobalRule(this, operand);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.Global;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "rule_global";
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "rule_global (" + getPattern() + ")";
	}
}
