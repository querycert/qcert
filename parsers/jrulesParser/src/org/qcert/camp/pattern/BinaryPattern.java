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
package org.qcert.camp.pattern;


/**
 * Represents a CAMP Binary Operator pattern 
 */
public class BinaryPattern extends CampPattern {
	private final BinaryOperator operator;
	
	public BinaryPattern(BinaryOperator operator, CampPattern operand1, CampPattern operand2) {
		super(operand1, operand2);
		this.operator = operator;
	}
	
	/* (non-Javadoc)
	 * @see org.qcert.camp.pattern.CampPattern#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.pbinop;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getOperands()
	 */
	@Override
	protected Object[] getOperands() {
		return new Object[] {operator, getOperand1(), getOperand2()};
	}

	/**
	 * @return the operator
	 */
	public BinaryOperator getOperator() {
		return operator;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "Pbinop";
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return operator + "(" + getOperand1() + ", " + getOperand2() + ")";
	}
}
