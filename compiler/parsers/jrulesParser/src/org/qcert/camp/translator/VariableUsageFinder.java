/**
 * (c) Copyright IBM Corp. 2015-2017
 * Copyright (C) 2017 Joshua Auerbach 
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
package org.qcert.camp.translator;

import java.util.HashSet;
import java.util.List;

import com.ibm.rules.engine.lang.semantics.SemLocalVariableDeclaration;
import com.ibm.rules.engine.lang.semantics.SemValue;
import com.ibm.rules.engine.lang.semantics.SemValueDeepVisitor;
import com.ibm.rules.engine.lang.semantics.SemVariableDeclaration;
import com.ibm.rules.engine.lang.semantics.SemVariableValue;
import com.ibm.rules.engine.ruledef.semantics.SemAggregateCondition;
import com.ibm.rules.engine.ruledef.semantics.SemClassCondition;
import com.ibm.rules.engine.ruledef.semantics.SemCondition;
import com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor;
import com.ibm.rules.engine.ruledef.semantics.SemEvaluateCondition;
import com.ibm.rules.engine.ruledef.semantics.SemExistsCondition;
import com.ibm.rules.engine.ruledef.semantics.SemInstanciatedCondition;
import com.ibm.rules.engine.ruledef.semantics.SemModalCondition;
import com.ibm.rules.engine.ruledef.semantics.SemNotCondition;
import com.ibm.rules.engine.ruledef.semantics.SemOrCondition;
import com.ibm.rules.engine.ruledef.semantics.SemProductCondition;

/** Find usages of a variable in a Condition */ 
class VariableUsageFinder extends SemValueDeepVisitor<Boolean> implements SemConditionVisitor<Boolean, Boolean> {
	private final SemLocalVariableDeclaration toFind;
	private final HashSet<SemCondition> seenConditions = new HashSet<>();
	
	VariableUsageFinder(SemLocalVariableDeclaration toFind) {
		this.toFind = toFind;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemAggregateCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemAggregateCondition cond, Boolean parameter) {
		if (visitList(cond.getAggregateApplication().getArguments())) return true;
		parameter = cond.getGeneratorCondition().accept(this, parameter);
		if (parameter) return parameter;
		return visitList(cond.getTests());
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemClassCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemClassCondition cond, Boolean parameter) {
		if (cond.hasGenerator())
			if (cond.getGenerator().getValueConditionGenerator().getValue().accept(this)) return true;
		return visitList(cond.getTests());
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemEvaluateCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemEvaluateCondition cond, Boolean parameter) {
		return visitList(cond.getTests());
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemExistsCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemExistsCondition cond, Boolean parameter) {
		return cond.getCondition().accept(this, parameter);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemInstanciatedCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemInstanciatedCondition cond, Boolean parameter) {
		if (visitList(cond.getArguments())) return true;
		return cond.getTemplate().getCondition().accept(this, parameter);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemModalCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemModalCondition cond, Boolean parameter) {
		parameter = cond.getSubCondition().accept(this, parameter);
		if (parameter) return parameter;
		return cond.getModalValue().accept(this);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemNotCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemNotCondition cond, Boolean parameter) {
		return cond.getCondition().accept(this, parameter);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemOrCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemOrCondition cond, Boolean parameter) {
		return visitConditionList(cond.getConditions());
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemProductCondition, java.lang.Object)
	 */
	@Override
	public Boolean visit(SemProductCondition cond, Boolean parameter) {
		return visitConditionList(cond.getConditions());
	}

	/**
	 * Check for a match.  If no match, ensure chasing of local variables, but avoid stack overflow
	 * @see com.ibm.rules.engine.lang.semantics.SemValueDeepVisitor#visit(com.ibm.rules.engine.lang.semantics.SemVariableValue)
	 */
	@Override
	public Boolean visit(SemVariableValue variableValue) {
		SemVariableDeclaration decl = variableValue.getVariableDeclaration();
		if (decl == toFind) return true;
		if (decl instanceof SemLocalVariableDeclaration) {
			SemValue init = ((SemLocalVariableDeclaration) decl).getInitialValue();
			if (init.accept(this)) return true;
		} else if (decl instanceof SemCondition) {
			if (seenConditions.add((SemCondition) decl)) 
				if (((SemCondition) decl).accept(this, false)) return true;
		}
		return super.visit(variableValue);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueDeepVisitor#add(java.lang.Object, java.lang.Object)
	 */
	@Override
	protected Boolean add(Boolean t1, Boolean t2) {
		return t1 || t2;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueDeepVisitor#defaultValue()
	 */
	@Override
	protected Boolean defaultValue() {
		return false;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueDeepVisitor#isAbsorbingElement(java.lang.Object)
	 */
	@Override
	protected boolean isAbsorbingElement(Boolean t) {
		return t == Boolean.TRUE;
	}

	/**
	 * Extend visiting to lists of conditions
	 * @param conditions
	 */
	protected Boolean visitConditionList(List<SemCondition> conditions) {
		Boolean ans = false;
		if (conditions != null)
			for (SemCondition cond : conditions) {
				ans = cond.accept(this, ans);
				if (ans) return ans;
			}
		return ans;
	}

	/**
	 * Extend visiting to lists of values as in lists of tests
	 * @param tests the list to visit
	 */
	protected Boolean visitList(List<SemValue> tests) {
		return tests == null ? defaultValue() : visitValues(tests);
	}
}
