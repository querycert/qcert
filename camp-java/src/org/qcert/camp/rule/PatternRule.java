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
 * Abstract parent of all CampRule specializations that contain a pattern.  This covers all
 *   four kinds defined in the Rule ADT  ... however, Rules formed from composing simpler rules 
 *   do not directly contain a pattern and so do not inherit from this parent.
 * This class also provides a field for a rule operand.  However, a ReturnRule never has one
 *   and other pattern rules may or may not have one depending on whether they are in their
 *   functional form or applied form.
 */
public abstract class PatternRule extends CampRule {
	private final CampPattern pattern;
	private final CampRule operand;

	/**
	 * Subroutine constructor
	 */
	protected PatternRule(CampPattern pattern, CampRule operand) {
		this.pattern = pattern;
		this.operand = operand;
	}
	
	/**
	 * @return the rule operand
	 */
	public CampRule getOperand() {
		return operand;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getOperands()
	 */
	@Override
	protected final Object[] getOperands() {
		if (operand == null)
			return new Object[] {pattern};
		else
			return new Object[] {pattern, operand};
	}

	public final CampPattern getPattern() {
		return pattern;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#isFunction()
	 */
	@Override
	public boolean isFunction() {
		return operand == null;
	}
}
