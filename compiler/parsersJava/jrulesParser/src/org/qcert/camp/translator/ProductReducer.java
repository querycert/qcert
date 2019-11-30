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

import java.util.Collection;
import java.util.List;

import com.ibm.rules.engine.lang.semantics.SemAggregateApplication;
import com.ibm.rules.engine.lang.semantics.SemClass;
import com.ibm.rules.engine.lang.semantics.SemLocalVariableDeclaration;
import com.ibm.rules.engine.lang.semantics.SemMetadata;
import com.ibm.rules.engine.lang.semantics.SemMethod;
import com.ibm.rules.engine.lang.semantics.SemMethodInvocation;
import com.ibm.rules.engine.lang.semantics.SemNewObject;
import com.ibm.rules.engine.lang.semantics.SemType;
import com.ibm.rules.engine.lang.semantics.SemValue;
import com.ibm.rules.engine.lang.semantics.SemVariableValue;
import com.ibm.rules.engine.ruledef.semantics.SemAggregateCondition;
import com.ibm.rules.engine.ruledef.semantics.SemCondition;
import com.ibm.rules.engine.ruledef.semantics.SemEvaluateCondition;
import com.ibm.rules.engine.ruledef.semantics.SemProductCondition;
import com.ibm.rules.engine.ruledef.semantics.SemRuleLanguageFactory;
import com.ibm.rules.engine.ruledef.transform.copier.SemRulesetCopier;

/** Copier that reduces the conditions in a SemProductCondition by eliminating one.  The intent is that this will be used repeatedly until nothing
 *   can be eliminated.
 *  Two kinds of nodes can be eliminated:
 *  <ol>
 *  <li>One that assigns one variable name to another where the rhs variable is otherwise unreferenced.
 *  <li>One that assigns a variable name to the count of a collection named by a variable that is otherwise unreferenced.
 *  </ol>
 *  The first case is preferred over the second since, in a multiple passes, the second is more easily identified after cases of the first have
 *  been elided.
 *  For the moment we assume that these variable assignments appear as SemEvaluateConditions with one binding and no tests.
 *  This may be an oversimplification.
 *  The motivation for this is that the main rules-to-coq translation doesn't use full variable scoping and lookup techniques, so the elimination
 *  of temporaries that tend to arise in berl rules makes the rest of the translation work in a wider number of cases.
 */
public class ProductReducer extends SemRulesetCopier {
	private final static String COLLECTION_UTIL = "ilog.rules.brl.IlrCollectionUtil";
	private final SemProductCondition original;
	private SemEvaluateCondition toEliminate;
	private String nameToKeep;
	private SemCondition absorbingCondition;
	private String nameToDiscard;
	
	/**
	 * Make a new instance
	 * @param languageFactory the SemRuleLanguageFactory to use
	 * @param original the original SemProductCondition that will be reduced by calling transformCondition()
	 */
	public ProductReducer(SemRuleLanguageFactory languageFactory, SemProductCondition original) {
		super(languageFactory);
		this.original = original;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.transform.copier.SemRulesetCopier#visit(com.ibm.rules.engine.ruledef.semantics.SemAggregateCondition, java.lang.Void)
	 */
	@Override
	public SemCondition visit(SemAggregateCondition oldCond, Void parameter) {
		if (oldCond == absorbingCondition) {
			SemCondition generatorCond = transformCondition(oldCond.getGeneratorCondition());
			SemAggregateApplication oldAppl = oldCond.getAggregateApplication();
			SemAggregateApplication appl = makeCountingApplication(oldAppl.getArguments(), oldAppl.getMetadataArray());
			SemAggregateCondition newCond = getFactory().aggregateCondition(generatorCond, cloneValue(oldCond.getGroupbyValue()), 
					appl);
			transformCopy(oldCond, newCond);
			return newCond;
		}
		return super.visit(oldCond, parameter);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.util.SemLanguageCloner#visit(com.ibm.rules.engine.lang.semantics.SemLocalVariableDeclaration)
	 */
	@Override
	public Object visit(SemLocalVariableDeclaration oldVar) {
		if (nameToDiscard.equals(oldVar.getVariableName())) {
			SemLocalVariableDeclaration newVar = getLanguageFactory().declareVariable(nameToKeep, translate(oldVar.getVariableType()), 
					transformValue(oldVar.getInitialValue()), transformMetadata(oldVar));
			declareVariableMapping(oldVar, newVar);
			return newVar;
		}
		return super.visit(oldVar);
	}

	/**
	 * Override to recognize the top level and perform initialization.
	 * @see com.ibm.rules.engine.ruledef.transform.copier.SemRulesetCopier#visit(com.ibm.rules.engine.ruledef.semantics.SemProductCondition, java.lang.Void)
	 */
	@Override
	public SemCondition visit(SemProductCondition cond, Void parameter) {
		if (cond == original) {
			initialize();
			SemProductCondition newCond = getFactory().productCondition(cond.getMetadataArray());
			for (SemCondition subCond : cond.getConditions()) {
				if (subCond != toEliminate)
					newCond.addCondition(transformCondition(subCond));
			}
			return newCond;
		}
		return super.visit(cond, parameter);
	}

	/**
	 * Initialize the state of the visitor by recording the declaration to be eliminated and some other things
	 *   derived from that.  All for convenience (the information is contained in the original SemProductCondition).
	 */
	private void initialize() {
		List<SemCondition> conditions = original.getConditions();
		toEliminate = findLastRemovableCondition(conditions);
		SemLocalVariableDeclaration decl = toEliminate.getBindings().get(0);
		nameToKeep = decl.getVariableName();
		SemValue rhs = decl.getInitialValue();
		boolean count = false;
		if (rhs instanceof SemMethodInvocation) {
			rhs = getCollectionIfSizeMethod((SemMethodInvocation) rhs); // won't return null here
			count = true;
		}
		SemLocalVariableDeclaration rhsDecl = (SemLocalVariableDeclaration) ((SemVariableValue) rhs).getVariableDeclaration();
		nameToDiscard = rhsDecl.getVariableName();
		if (count)
			absorbingCondition = getAbsorbingCondition(conditions, nameToDiscard);
	}

	/**
	 * Make the appropriate SemAggregateApplication for counting
	 * @param arguments the arguments to use
	 * @return the requested ast node
	 */
	private SemAggregateApplication makeCountingApplication(List<SemValue> arguments, SemMetadata[] metadata) {
		SemRuleLanguageFactory factory = getFactory();
		SemType countClass = factory.getObjectModel().getType("com.ibm.rules.generated.util.aggregate.Count_Object");
		SemNewObject aggClsInst = factory.newObject(countClass);
		return factory.aggregateApplication(aggClsInst, arguments, metadata);
	}

	/**
	 * Determine if a SemProductCondition is reducible by this copier
	 * @param product the condition to check
	 * @return true iff it is reducible
	 */
	public static boolean isReducible(SemProductCondition product) {
		List<SemCondition> conditions = product.getConditions();
		return findLastRemovableCondition(conditions) != null;
	}

	/**
	 * Find the last removable SemEvaluateCondition in a list (there may be none)
	 * @param conditions the list of conditions to analyze
	 * @return the last removable SemEvaluateCondition or null if none
	 */
	private static SemEvaluateCondition findLastRemovableCondition(List<SemCondition> conditions) {
		if (conditions.size() < 2) return null;
		SemEvaluateCondition countCase = null;
		search:
		for (int i = conditions.size() -1 ; i >=0; i--) {
			SemCondition test = conditions.get(i);
			/* The condition must be a SemEvaluateCondition */
			if (test instanceof SemEvaluateCondition) {
				SemEvaluateCondition eval = (SemEvaluateCondition) test;
				/* It must have no tests and exactly one binding */
				if (!eval.getTests().isEmpty()) continue search;;
				List<SemLocalVariableDeclaration> decls = eval.getBindings();
				if (decls.size() != 1) continue search;
				SemLocalVariableDeclaration decl = decls.get(0);
				/* The declaration's rhs must be one of the two forms we're prepared to handle */
				SemValue toTest = decl.getInitialValue();
				boolean count = false;
				if (toTest instanceof SemMethodInvocation) {
					SemValue collection = getCollectionIfSizeMethod((SemMethodInvocation) toTest);
					if (collection != null) {
						toTest = collection;
						count = true;
					}
				}
				if (toTest instanceof SemVariableValue && 
						((SemVariableValue) toTest).getVariableDeclaration() instanceof SemLocalVariableDeclaration) {
					SemLocalVariableDeclaration toRename = (SemLocalVariableDeclaration) 
							((SemVariableValue) toTest).getVariableDeclaration();
					/* There must be an absorbing condition, and, for a count, it must be an aggregate producing a collection */
					SemCondition absorbing = getAbsorbingCondition(conditions, toRename.getVariableName());
					if (absorbing == null || count && !isCollectionAggregate(absorbing)) continue search;
					/* There must be no other references to the declaration that will be renamed */
					VariableUsageFinder finder = new VariableUsageFinder(toRename);
					for (SemCondition cond : conditions) {
						if (cond == eval) break;
						if (cond.accept(finder, false)) continue search;
					}
					/* All conditions met, but prefer simple cases over count cases unless only count cases remain. */
					if (count) 
						if (countCase == null) countCase = eval;
						else continue;
					else return eval;
				}
			}
		}
		/* No simple cases found.  Either nothing found, or a countCase was found */
		return countCase;
	}
	
	/**
	 * Get the 'absorbing condition' (the one that will acquire the name of eliminated declaration)
	 * @param conditions the complete list of conditions
	 * @param marker the variable name appearance as the declared name of a condition marks it as the absorbing one
	 */
	private static SemCondition getAbsorbingCondition(List<SemCondition> conditions, String marker) {
		for (SemCondition cond : conditions) {
			if (cond.getBindings().size() > 0 && marker.equals(cond.getBindings().get(0).getVariableName())) {
				return cond;
			}
		}
		return null;
	}


	/**
	 * Determine if a condition is an aggregate condition produces a collection result
	 * @param cond the condition to test
	 * @return true if it is an aggregate condition that produces a collection result
	 */
	private static boolean isCollectionAggregate(SemCondition cond) {
		if (cond instanceof SemAggregateCondition) {
			SemType type = ((SemAggregateCondition) cond).getAggregateApplication().getReturnType();
			if (type instanceof SemClass) {
				return Collection.class.isAssignableFrom(((SemClass) type).getNativeClass());
			}
		}
		return false;
	}

	/**
	 * Implement some heuristics (probably inadequate) for identifying collection size extractions
	 * @param method the SemMethodInvocation to analyze
	 * @return the SemValue from the invocation that represents the collection
	 */
	private static SemValue getCollectionIfSizeMethod(SemMethodInvocation method) {
		SemMethod callee = method.getMethod();
		List<SemValue> args = method.getArguments();
		if (args.size() == 1 && callee.getName().equals("getSize") && 
				callee.getDeclaringType().getDisplayName().equals(COLLECTION_UTIL)) {
			return args.get(0);
		}
		if (args.size() == 0 && callee.getName().equals("size")) {
			SemType declaringType = callee.getDeclaringType();
			if (declaringType instanceof SemClass) {
				if (Collection.class.isAssignableFrom(((SemClass) declaringType).getNativeClass())) {
					return method.getCurrentObject();
				}
			}
		}
		return null;
	}
}
