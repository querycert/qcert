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
package org.qcert.camp.pattern;


/**
 * Represents the CAMP letIt pattern.  This pattern can exist in a partially applied form (with only one operand bound, making
 *   the resulting signature pat->pat instead of pat.
 */
public class LetItPattern extends CampPattern {
	/** Make a partially applied LetItPattern to be completed using applyTo */
	public LetItPattern(CampPattern operand1) {
		this(operand1, null);
	}

	/** Make a complete LetItPattern of type 'pat' */
	public LetItPattern(CampPattern operand1, CampPattern operand2) {
		super(operand1, operand2);
	}
	
	@Override
	public CampPattern applyTo(CampPattern operand2) {
		return new LetItPattern(getOperand1(), operand2);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.pattern.CampPattern#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.pletIt;
	}

	@Override
	public boolean isFunction() {
		return getOperand2() == null;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		CampPattern op2 = getOperand2();
		return "let IT = " + getOperand1() + " in " + (op2 == null ? "??" : op2);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "PletIt";
	}
}
