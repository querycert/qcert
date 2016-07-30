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
import java.util.ArrayList;
import java.util.List;

import org.qcert.camp.CampAST;

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

	/**
	 * Override emit to apply all rules right-associatively.
	 * @see org.qcert.camp.CampAST#emit(java.io.PrintWriter)
	 */
	@Override
	public void emit(PrintWriter pw) {
		pw.append("(");
		int close = 1;
		if (left instanceof CompoundRule) {
			for (CampRule rule : ((CompoundRule) left).getMembers()) {
				rule.emit(pw);
				pw.append(" (");
				close++;
			}
		} else {
			((CampRule) left).emit(pw);
			pw.append(" ");
		}
		right.emit(pw);
		pw.append(new String(new char[close]).replace('\0', ')'));
	}
	
	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.Complete;
	}
	
	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getOperands()
	 */
	@Override
	protected Object[] getOperands() {
		throw new IllegalStateException();  // should not be called since we override emit
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		throw new IllegalStateException();  // should not be called since we override emit
	}

	/**
	 * The toString() for CompleteRule overrules the toString of its 'left' functionRule so that,
	 *   if that were to be a CompoundRule, we can write a simple application instead of forming
	 *   the composition and then applying it.
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		List<CampRule> rules = new ArrayList<>();
		if (left instanceof CompoundRule) {
			rules.addAll(((CompoundRule) left).getMembers());
		} else
			rules.add((CampRule) left);
		rules.add(right);
		String delim = "";
		StringBuilder bldr = new StringBuilder();
		for (CampRule rule : rules) {
			bldr.append(delim).append(rule);
			delim = String.format(" ;;%n");
		}
		return bldr.toString();
	}
}
