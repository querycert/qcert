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

import org.qcert.camp.CampAST;


/**
 * Represents all Patterns (expressions in CAMP rather than Rules or Data)
 */
public abstract class CampPattern extends CampAST {
	/** Single instance of the env pattern */
	public static final EnvPattern ENV = new EnvPattern();

	/** Single instance of the it pattern */
	public static final ItPattern IT = new ItPattern();
	/** Single instance of the left pattern */
	public static final CampPattern LEFT = new LeftPattern();
	/** Single instance of the right pattern */
	public static final RightPattern RIGHT = new RightPattern();
	private final CampPattern[] operands;
	
	CampPattern(CampPattern ... operands) {
		this.operands = operands;
	}
	
	/**
	 * A few subclasses can exist in partially applied form and complete themselves using this call.
	 * The default implementation throws an exception
	 * @param operand the operand to which the partially applied pattern is to be applied in order to complete itself
	 * @return the completed pattern
	 */
	public CampPattern applyTo(CampPattern operand) {
		throw new UnsupportedOperationException("This pattern does not support 'applyTo'");
	}
	
	public abstract Kind getKind();
	
	public final CampPattern getOperand() {
		return getOperand1();
	}
	
	public final CampPattern getOperand1() {
		return operands[0];
	}
	
	public final CampPattern getOperand2() {
		return operands[1];
	}
	
	/**
	 * Default implementation for those AST types that have only CampPattern operands
	 * @see org.qcert.camp.CampAST#getOperands()
	 */
	@Override
	protected Object[] getOperands() {
		return operands;
	}
	
	/**
	 * Those subclasses that can be partially applied and have not been applied (have a current signature of pat->pat) should
	 *   return true.  Default returns false.
	 * @return whether this pattern is a function
	 */
	public boolean isFunction() {
		return false;
	}
	
	public enum Kind {
		  pconst, punop, pbinop, pmap, passert, 
		  porElse, pit, pletIt, pgetconstant, penv, 
		  pletEnv, pleft, pright; 
	}
}
