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
 * Represents a CAMP Map pattern.  This pattern can exist in a partially applied form (with only one operand bound, making
 *   the resulting signature pat->pat instead of pat.
 */
public class MapPattern extends CampPattern {
	/** Make a complete Map pattern */
	public MapPattern(CampPattern operand) {
		super(operand);
	}
	
	/** Make a partially applied map pattern */
	public MapPattern() {
		super((CampPattern) null);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.pattern.CampPattern#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.pmap;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "Pmap";
	}

	@Override
	public boolean isFunction() {
		return getOperand() == null;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		CampPattern op = getOperand();
		return "map " + (op == null ? "??" : op);
	}
}
