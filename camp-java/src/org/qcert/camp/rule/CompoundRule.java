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

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.qcert.camp.pattern.CampPattern;

/**
 * Represents a compound rule formed from other parially applied rules (for which isFunction() is true)
 */
public final class CompoundRule extends CampRule {
	private final List<CampRule> members;

	public CompoundRule(CampRule left, CampRule right) {
		ArrayList<CampRule> members = new ArrayList<>();
		if (left instanceof CompoundRule)
			members.addAll(((CompoundRule) left).members);
		else if (left.isFunction())
			members.add(left);
		else
			throw new IllegalArgumentException("First rule argument is not a function");
		if (right instanceof CompoundRule)
			members.addAll(((CompoundRule) right).members);
		else if (right.isFunction())
			members.add(right);
		else
			throw new IllegalArgumentException("Second rule argument is not a function");
		this.members = Collections.unmodifiableList(members);
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#apply(org.qcert.camp.rule.CampRule)
	 */
	@Override
	public CampRule applyTo(CampRule rule) {
		List<CampRule> toApply = new ArrayList<>(members);
		Collections.reverse(toApply);
		for (CampRule next : toApply) {
			rule = next.applyTo(rule);
		}
		return rule;
	}

	/** See comment in "convertToPattern" */
	public CampPattern convertForAggregate() {
		return applyTo(new ReturnRule(CampPattern.ENV)).convertToPattern();
	}

	/**
	 * In the Coq implementation of Rules, things of signature Rule->Rule are not converted
	 *  to patterns as such; they typically appear inside aggregates, where they are always
	 *  first applied to '(rule_return penv)' before conversion.
	 * Consequently, this method is a "should not occur" to avoid accidentally calling it
	 * in a context in which the Rule->Rule signature is invalid.   In aggregate processing,
	 * use "convertForAggregate," which will do the right thing.
	 * @see org.qcert.camp.rule.CampRule#convertToPattern()
	 */
	@Override
	public CampPattern convertToPattern() {
		throw new IllegalStateException("Improper context for convertToPattern on compound rule");
	}

	/**
	 * Special emitting function.  Note: the format for this case is not well-established.
	 * @see org.qcert.camp.CampAST#emit(java.io.PrintWriter)
	 */
	@Override
	public void emit(PrintWriter pw) {
		pw.append("(compound ");
		for (CampRule rule : members) {
			rule.emit(pw);
			pw.append(" ");
		}
		pw.append(")");
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.Compound;
	}

	/**
	 * @return the members
	 */
	public List<CampRule> getMembers() {
		return members;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.rule.CampRule#isFunction()
	 */
	@Override
	public boolean isFunction() {
		return true;
	}

	/**
	 * If the CompoundRule is the lhs of a CompleteRule, this method is not called by the toString() method of the latter.
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String delim = "";
		StringBuilder bldr = new StringBuilder();
		for (CampRule rule : members) {
			bldr.append(delim).append(rule);
			delim = String.format(" ;;;%n");
		}
		return bldr.toString();
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
}
