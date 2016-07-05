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

import java.io.PrintWriter;

/**
 * Represents a rule formed from a chain of FunctionRules applied to a single
 *   RuleReturn on the right (right-associative application)
 */
public final class CompleteRule extends CampRule implements SimpleRule {
	private final FunctionRule left;
	private final ReturnRule right;
	
	public CompleteRule(FunctionRule left, SimpleRule right) {
		FunctionRule effectiveLeft;
		ReturnRule effectiveRight;
		if (right instanceof CompleteRule) {
			effectiveLeft = new CompoundRule(left, ((CompleteRule) right).left);
			effectiveRight = ((CompleteRule) right).right;
		} else {
			effectiveLeft = left;
			effectiveRight = (ReturnRule) right;
		}
		this.left = effectiveLeft;
		this.right = effectiveRight;
	}
	
	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#emit(java.io.PrintWriter)
	 */
	@Override
	public void emit(PrintWriter pw) {
		// TODO Auto-generated method stub
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.Complete;
	}
}
