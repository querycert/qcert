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

import java.lang.reflect.Field;
import java.time.Duration;
import java.time.Instant;
import java.time.LocalTime;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.ZonedDateTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.qcert.camp.CampMacros;
import org.qcert.camp.pattern.AssertPattern;
import org.qcert.camp.pattern.BinaryOperator;
import org.qcert.camp.pattern.BinaryPattern;
import org.qcert.camp.pattern.CampPattern;
import org.qcert.camp.pattern.CompoundPattern;
import org.qcert.camp.pattern.ConstPattern;
import org.qcert.camp.pattern.LetItPattern;
import org.qcert.camp.pattern.MapPattern;
import org.qcert.camp.pattern.UnaryOperator;
import org.qcert.camp.pattern.UnaryPattern;
import org.qcert.camp.rule.CampRule;
import org.qcert.camp.rule.CompoundRule;
import org.qcert.camp.rule.GlobalRule;
import org.qcert.camp.rule.NotRule;
import org.qcert.camp.rule.PatternRule;
import org.qcert.camp.rule.ReturnRule;
import org.qcert.camp.rule.WhenRule;

import com.ibm.rules.engine.lang.semantics.SemAbstractAnnotatedElement;
import com.ibm.rules.engine.lang.semantics.SemAggregate;
import com.ibm.rules.engine.lang.semantics.SemAggregateFunctionMetadata;
import com.ibm.rules.engine.lang.semantics.SemAnnotatedElement;
import com.ibm.rules.engine.lang.semantics.SemArrayClass;
import com.ibm.rules.engine.lang.semantics.SemAttribute;
import com.ibm.rules.engine.lang.semantics.SemAttribute.Implementation;
import com.ibm.rules.engine.lang.semantics.SemAttribute.NativeImplementation;
import com.ibm.rules.engine.lang.semantics.SemAttributeAssignment;
import com.ibm.rules.engine.lang.semantics.SemAttributeValue;
import com.ibm.rules.engine.lang.semantics.SemBagClass;
import com.ibm.rules.engine.lang.semantics.SemBlock;
import com.ibm.rules.engine.lang.semantics.SemCast;
import com.ibm.rules.engine.lang.semantics.SemClass;
import com.ibm.rules.engine.lang.semantics.SemCollectionDomain;
import com.ibm.rules.engine.lang.semantics.SemConditionalOperator;
import com.ibm.rules.engine.lang.semantics.SemConstant;
import com.ibm.rules.engine.lang.semantics.SemDomain;
import com.ibm.rules.engine.lang.semantics.SemDomainKind;
import com.ibm.rules.engine.lang.semantics.SemExtension;
import com.ibm.rules.engine.lang.semantics.SemFunctionalIf;
import com.ibm.rules.engine.lang.semantics.SemFunctionalSwitch;
import com.ibm.rules.engine.lang.semantics.SemGenericClass;
import com.ibm.rules.engine.lang.semantics.SemGenericInfo;
import com.ibm.rules.engine.lang.semantics.SemIndexerAssignment;
import com.ibm.rules.engine.lang.semantics.SemIndexerValue;
import com.ibm.rules.engine.lang.semantics.SemInterval;
import com.ibm.rules.engine.lang.semantics.SemLambdaBlock;
import com.ibm.rules.engine.lang.semantics.SemLambdaValue;
import com.ibm.rules.engine.lang.semantics.SemLocalVariableDeclaration;
import com.ibm.rules.engine.lang.semantics.SemMetadata;
import com.ibm.rules.engine.lang.semantics.SemMethod;
import com.ibm.rules.engine.lang.semantics.SemMethodInvocation;
import com.ibm.rules.engine.lang.semantics.SemMethodReference;
import com.ibm.rules.engine.lang.semantics.SemNamedVariableDeclaration;
import com.ibm.rules.engine.lang.semantics.SemNewObject;
import com.ibm.rules.engine.lang.semantics.SemStatement;
import com.ibm.rules.engine.lang.semantics.SemThis;
import com.ibm.rules.engine.lang.semantics.SemType;
import com.ibm.rules.engine.lang.semantics.SemTypeKind;
import com.ibm.rules.engine.lang.semantics.SemTypeRestriction;
import com.ibm.rules.engine.lang.semantics.SemValue;
import com.ibm.rules.engine.lang.semantics.SemValueSet;
import com.ibm.rules.engine.lang.semantics.SemValueVisitor;
import com.ibm.rules.engine.lang.semantics.SemVariableAssignment;
import com.ibm.rules.engine.lang.semantics.SemVariableDeclaration;
import com.ibm.rules.engine.lang.semantics.SemVariableValue;
import com.ibm.rules.engine.lang.semantics.metadata.SemTextLocationMetadata;
import com.ibm.rules.engine.ruledef.semantics.SemActionContent;
import com.ibm.rules.engine.ruledef.semantics.SemAggregateCondition;
import com.ibm.rules.engine.ruledef.semantics.SemClassCondition;
import com.ibm.rules.engine.ruledef.semantics.SemCondition;
import com.ibm.rules.engine.ruledef.semantics.SemConditionGenerator;
import com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor;
import com.ibm.rules.engine.ruledef.semantics.SemEvaluateCondition;
import com.ibm.rules.engine.ruledef.semantics.SemExistsCondition;
import com.ibm.rules.engine.ruledef.semantics.SemInstanciatedCondition;
import com.ibm.rules.engine.ruledef.semantics.SemModalCondition;
import com.ibm.rules.engine.ruledef.semantics.SemNotCondition;
import com.ibm.rules.engine.ruledef.semantics.SemOrCondition;
import com.ibm.rules.engine.ruledef.semantics.SemProductCondition;
import com.ibm.rules.engine.ruledef.semantics.SemProductionRule;
import com.ibm.rules.engine.ruledef.semantics.SemQuery;
import com.ibm.rules.engine.ruledef.semantics.SemRule;
import com.ibm.rules.engine.ruledef.semantics.SemRuleContent;
import com.ibm.rules.engine.ruledef.semantics.SemRuleLanguageFactory;
import com.ibm.rules.engine.ruledef.semantics.SemValueConditionGenerator;
import com.ibm.rules.engine.ruledef.semantics.SemValueConditionGenerator.Kind;
import com.ibm.rules.engine.ruledef.semantics.SemVariableCondition;

/**
 * A translator from SemRule nodes to CampAST nodes.
 */
public class SemRule2CAMP implements SemValueVisitor<CampPattern>, SemConditionVisitor<Void, CampRule> {
	/** Specific time type used in certain time constants */
	private static final String TIME_TYPE = "ilog.rules.brl.Time";

	/** Specific date type used in certain date constants */
	private static final String DATE_TYPE = "ilog.rules.brl.Date";

	/** Method name for the runtime utility methods that get the size of a collection */
	private static final String GET_SIZE = "getSize";

	/** Method name for the standard size() method on Collection */
	private static final String SIZE = "size";

	/** Class name for the runtime utility to manage collections */
	private static final String COLLECTION_UTIL = "ilog.rules.brl.IlrCollectionUtil";

	/** Class name for the apache utility to manage collections  */
	private static final String APACHE_COLLECTION_UTIL = "org.apache.commons.collections.CollectionUtils";

	/** The set of known temporal types */
	private static final Set<String> temporalTypes = new HashSet<>(Arrays.asList(
			DATE_TYPE,
			"ilog.rules.brl.SimpleDate",
			TIME_TYPE,
			LocalTime.class.getName(),
			ZonedDateTime.class.getName(),
			"com.ibm.ia.AbsoluteDuration",
			"com.ibm.ia.TimePeriod",
			"com.ibm.ia.CalendarDuration",
			Duration.class.getName()
			));

	/** A SemRuleLanguageFactory to use as needed in minor local rewrites */
	private final SemRuleLanguageFactory factory;

	/** Ensure a single passert in front of arbitrarily nested pbinop and punop */
	private boolean passertSeen;

	/** A place to store the known prefix of the access path when converting a SemAggregateCondition and/or 
	 * SemAttributeValue */
	private List<SemAttributeValue> linkChain;

	/** Place to cache a fetchRef link when iterating over collections of references */
	private CampPattern savedFetchRef;

	/** Count of pmap levels inserted during processing of processLinkChain */
	private int pmapCount;

	/**
	 * Make a new SemRule2CAMP
	 * @param factory the language factory to use
	 */
	public SemRule2CAMP(SemRuleLanguageFactory factory /* , UnaryOperator operator, SemClass engineData*/) {
		this.factory = factory;
	}

	/**
	 * Translate a Rule
	 * @param rule the Rule to translate
	 * @return the result as a CAMP AST
	 */
	public CampRule translate(SemRule rule) {
		SemCondition condition = null;
		CampPattern result = null;
		if (rule instanceof SemProductionRule) {
			SemRuleContent content = ((SemProductionRule) rule).getContent();
			if (content instanceof SemActionContent) {
				condition = content.getCondition();
				SemBlock statements = ((SemActionContent) content).getStatements();
				if (isQueryAsRule(statements) && getEffectiveCondition(condition) instanceof SemAggregateCondition) {
					condition = getEffectiveCondition(condition);
					result = condition.getBindings().get(0).asValue().accept(this);
				} else
					result = translateBlock(statements, condition);
			} 
		} else if (rule instanceof SemQuery) {
			condition = ((SemQuery) rule).getCondition();
			result = condition.getBindings().get(0).asValue().accept(this);
		}
		if (result == null)
			notImplemented("translation for rule of type " + rule.getClass().getName());
		ReturnRule ans = new ReturnRule(result);
		return condition == null ? ans : condition.accept(this, null).applyTo(ans);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemAggregate)
	 */
	@Override
	public CampPattern visit(SemAggregate aggregate) {
		return notImplemented(aggregate);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemAggregateCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemAggregateCondition ast, Void parameter) {
		/* Rule out things that keep us from succeeding */
		if (ast.hasGroupbyDefinition() || ast.hasGroupbyVariable())
			notImplemented("GroupBy");
		if (0 != ast.getTests().size())
			// TODO we should fix this.  Need some examples and then it should be obvious.
			notImplemented("SemAggregateCondition with tests");
		SemValue cls = ast.getAggregateApplication().getInstanceOfAggregateClass();
		if (!(cls instanceof SemNewObject))
			notImplemented("SemAggregateCondition whose application isn't an object creation");

		/* Get the condition and fork off the case of a per-entity aggregation */
		SemCondition cond = ast.getGeneratorCondition();
		if (cond instanceof SemClassCondition && ((SemClassCondition) cond).hasGenerator() 
				&& isPerEntityGenerator(((SemClassCondition) cond).getGenerator()))
			return translatePerEntityAggregate(ast);

		/* Consider product conditions and add to the link chain if appropriate; otherwise just process the condition  */
		List<SemAttributeValue> linkChain = new ArrayList<>();
		CampRule rule = null;
		if (cond instanceof SemProductCondition) {
			for (SemCondition c : ((SemProductCondition)cond).getConditions()) {
				if (getAttributeValueLink(c, linkChain)) continue;
				CampRule newRule = c.accept(this, null);
				rule = rule == null ? newRule : new CompoundRule(rule, newRule);
			}
		} else {
			rule = cond.accept(this, null);
		}

		/* Get the 'over' expression and the operator */
		Object[] overAndOp = getOverAndOp((SemNewObject) cls, ast, linkChain.isEmpty() ? null : linkChain);
		SemValue over = (SemValue) overAndOp[0];
		UnaryOperator op = (UnaryOperator) overAndOp[1];

		/* Process the 'over' expression along with the linkChain if any. */
		this.linkChain = linkChain.isEmpty() ? null : linkChain;
		CampPattern arg = null;
		if (over == null)  
			arg = processLinkChain(true);
		else if (!linkChain.isEmpty()) {
			if (over instanceof SemVariableValue && ((SemVariableValue) over).getVariableDeclaration() instanceof SemLocalVariableDeclaration)
				// TODO this is dubious since we do not specifically check that the variable reference is to the end of the linkChain
				arg = processLinkChain(true);
			else if (over instanceof SemAttributeValue) {
				this.linkChain.add((SemAttributeValue) over);
				arg = processLinkChain(true);
			} else
				notImplemented("Aggregate condition too complex to analyze");
		} else
			arg = over.accept(this);

		/* Build the answer */
		CampPattern ans = CampMacros.aggregate(rule, op, arg, pmapCount);
		pmapCount = 0;
		return makeAggregateAnswer(ast, ans);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueAndStatementVisitor#visit(com.ibm.rules.engine.lang.semantics.SemAttributeAssignment)
	 */
	@Override
	public CampPattern visit(SemAttributeAssignment value) {
		return notImplemented(value);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemAttributeValue)
	 */
	@Override
	public CampPattern visit(SemAttributeValue ast) {
		SemAttribute attr = ast.getAttribute();
		if (attr.isStatic()) {
			if (isEnumeration(attr.getAttributeType())) {
				return new ConstPattern(attr.getName());
			}
			Implementation impl = attr.getGetterImplementation();
			if (impl instanceof NativeImplementation) {
				Field field = ((NativeImplementation) impl).getField();
				try {
					return factory.getConstant(field.get(null), ast.getType()).accept(this);
				} catch (IllegalArgumentException | IllegalAccessException e) {
				}
			}
			notImplemented("Non-constant or non-native static attribute");
		}
		if (linkChain == null)
			linkChain = new ArrayList<>();
		linkChain.add(ast);
		return processLinkChain(false);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemCast)
	 */
	@Override
	public CampPattern visit(SemCast cast) {
		SemType toType = cast.getType();
		SemValue value = cast.getValue();
		SemType fromType = value.getType();
		/* Vacuous casts are always accepted (and elided) */
		if (toType.equals(fromType))
			return value.accept(this);
		/* If we are doing floating point and the cast is between numeric types, we translate the cast to the
		 * appropriate conversion operation in CAMP.  If we are not doing floating point, then all casts between
		 * numeric types are vacuous since we then have only one numeric type in CAMP.  Even when doing floating
		 * point, casts are vacuous unless they actively change between integer and floating point (in either direction).
		 */
		if (isNumeric(toType) && isNumeric(fromType)) {
			CampPattern convertedVal = value.accept(this);
			if (isFloatingPoint(toType))
				if (isFloatingPoint(fromType))
					return convertedVal;
				else
					return new UnaryPattern(UnaryOperator.OpFloatOfNat, convertedVal);
			else
				if (isFloatingPoint(fromType))
					return new UnaryPattern(UnaryOperator.OpFloatTruncate, convertedVal);
				else
					return convertedVal;
		}
		if (isTemporalType(toType) && isTemporalType(fromType))
			// Accept various casts that ARL normally applies for temporal operations on timestamps
			return value.accept(this);
		/* We aren't yet prepared to deal with the more complex cases */
		return notImplemented("A cast expression that actually changes the value");
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemClassCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemClassCondition ast, Void parameter) {
		String varName = getConditionVariableName(ast);
		String typeName = ast.getConditionType().getDisplayName();
		CampPattern tests = translateTests(ast.getTests());
		CampPattern initial = (varName != null) ? CampMacros.instanceOf(varName, typeName, tests) : 
			CampMacros.matches(typeName, tests);
		return new WhenRule(initial);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemConditionalOperator)
	 */
	@Override
	public CampPattern visit(SemConditionalOperator operator) {
		SemValue left = operator.getLeftValue();
		SemValue right = operator.getRightValue();
		switch (operator.getKind()) {
		case AND:
			return translateBinaryOp(BinaryOperator.OpAnd, left, right);
		case OR:
			return translateBinaryOp(BinaryOperator.OpOr, left, right);
		default:
			return notImplemented(operator);
		}
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemConstant)
	 */
	@Override
	public CampPattern visit(SemConstant constant) {
		return new ConstPattern(constant.getValue());
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemEvaluateCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemEvaluateCondition ast, Void parameter) {
		List<SemLocalVariableDeclaration> bindings = ast.getBindings();
		List<SemValue> tests = ast.getTests();
		CampPattern pattern = null;
		if (1 == bindings.size() && 0 == tests.size()) {
			/* Using SemEvaluateCondition to define a single binding */
			SemLocalVariableDeclaration binding = bindings.get(0);
			pattern = CampMacros.varWith(binding.getVariableName(), binding.getInitialValue().accept(this));
		} else if (bindings.size() != 0) {
			// TODO we can almost certainly be more general here
			notImplemented(bindings.size() + " bindings and " + tests.size() + " tests in an evaluate condition");
			return null;
		} else
			pattern = translateTests(tests);
		return new GlobalRule(pattern);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemExistsCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemExistsCondition cond, Void parameter) {
		notImplemented(cond);
		return null;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemExtension)
	 */
	@Override
	public CampPattern visit(SemExtension extension) {
		return notImplemented(extension);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemFunctionalIf)
	 */
	@Override
	public CampPattern visit(SemFunctionalIf functionalIf) {
		return notImplemented(functionalIf);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemFunctionalSwitch)
	 */
	@Override
	public CampPattern visit(SemFunctionalSwitch functionalSwitch) {
		return notImplemented(functionalSwitch);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueAndStatementVisitor#visit(com.ibm.rules.engine.lang.semantics.SemIndexerAssignment)
	 */
	@Override
	public CampPattern visit(SemIndexerAssignment value) {
		return notImplemented(value);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemIndexerValue)
	 */
	@Override
	public CampPattern visit(SemIndexerValue value) {
		return notImplemented(value);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemInstanciatedCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemInstanciatedCondition cond, Void parameter) {
		notImplemented(cond);
		return null;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemInterval)
	 */
	@Override
	public CampPattern visit(SemInterval interval) {
		return notImplemented(interval);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemLambdaBlock)
	 */
	@Override
	public CampPattern visit(SemLambdaBlock lambdaBlock) {
		return notImplemented(lambdaBlock);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemLambdaValue)
	 */
	@Override
	public CampPattern visit(SemLambdaValue lambdaValue) {
		return notImplemented(lambdaValue);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueAndStatementVisitor#visit(com.ibm.rules.engine.lang.semantics.SemMethodInvocation)
	 */
	@Override
	public CampPattern visit(SemMethodInvocation ast) {
		SemMethod method = ast.getMethod();
		List<SemValue> args = ast.getArguments();
		switch (method.getOperatorKind()) {
		case NOT_AN_OPERATOR: {
			if (isIntegerToString(ast) || isStringListToString(ast)) {
				return CampMacros.stringify(args.get(0).accept(this));
			} else if (isSystemOutPrintln(ast)) {
				// TODO this only works when the argument is a string concat already
				return args.get(0).accept(this);
			} else if (isToString(ast)) {
				return CampMacros.stringify(ast.getCurrentObject().accept(this));
			} else if (isTranslatableEquals(ast)) {
				return translateBinaryOp(BinaryOperator.OpEqual, ast.getCurrentObject(), args.get(0));
			} else if (isValueOf(ast)) {
				return args.get(0).accept(this);
			} else if (isXValue(ast)) {
				return ast.getCurrentObject().accept(this);
			} else if (isContains(ast)){
				SemValue receiver = ast.getCurrentObject();
				if (receiver instanceof SemInterval)
					return translateIntervalContains((SemInterval) receiver, args.get(0));
				return translateBinaryOp(BinaryOperator.OpContains, args.get(0), ast.getCurrentObject());
			} else if (isFormatEntities(ast)){
				return CampMacros.variables(getVariableNames(args));
			} else if (isTimeStringToEpochMillis(ast)) {
				return translateTimeStringToEpochMillis(ast);
			} else if (isContainsAny(ast)) {
				return translateContainsAny(args.get(0), args.get(1));
			} else if (isSizeMethod(ast)) {
				return translateSizeMethod(ast);
			} else {
				return notImplemented(ast);
			}
		}
		case ADD: {
			return translateAdd(ast);
		}
		case EQUALS: {
			return translateBinaryOp(BinaryOperator.OpEqual, args.get(0), args.get(1));
		}
		case NOT_EQUALS: {
			return translateNotEquals(ast);
		}
		case LESS_OR_EQUALS_THAN: {
			return translateBinaryOp(BinaryOperator.OpLe, args.get(0), args.get(1));
		}
		case LESS_THAN: {
			return translateBinaryOp(BinaryOperator.OpLt, args.get(0), args.get(1));
		}
		case GREATER_OR_EQUALS_THAN: {
			return translateBinaryOp(BinaryOperator.OpLe, args.get(1), args.get(0));
		}
		case GREATER_THAN: {
			return translateBinaryOp(BinaryOperator.OpLt, args.get(1), args.get(0));
		}
		case AND: {
			return translateBinaryOp(BinaryOperator.OpAnd, args.get(0), args.get(1));
		}
		case SUB: {
			return translateBinaryOp(BinaryOperator.NatMinus, args.get(0), args.get(1));
		}
		case DIV: {
			return translateBinaryOp(BinaryOperator.NatDiv, args.get(0), args.get(1));
		}
		case MUL: {
			return translateBinaryOp(BinaryOperator.NatMult, args.get(0), args.get(1));
		}
		// TODO appropriate subset of the following
		case BIT_NOT:
		case COUNT:
		case EXPLICIT_CAST:
		case IMPLICIT_CAST:
		case INSTANCEOF:
		case LSH:
		case MINUS:
		case NOT:
		case OR:
		case PLUS:
		case REM:
		case RSH:
		case URSH:
		case XOR:
		default:
			return notImplemented(method.getOperatorKind());
		}
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemMethodReference)
	 */
	@Override
	public CampPattern visit(SemMethodReference methodReference) {
		return notImplemented(methodReference);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemModalCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemModalCondition cond, Void parameter) {
		notImplemented(cond);
		return null;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueAndStatementVisitor#visit(com.ibm.rules.engine.lang.semantics.SemNewObject)
	 */
	@Override
	public CampPattern visit(SemNewObject newObject) {
		if (isTemporalValue(newObject))
			return translateTemporalAllocation(newObject);
		else
			return notImplemented(newObject);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemNotCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemNotCondition cond, Void parameter) {
		PatternRule inner = (PatternRule) cond.getCondition().accept(this, null);
		return new NotRule(inner.getPattern());
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemOrCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemOrCondition cond, Void parameter) {
		notImplemented(cond);
		return null;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.ruledef.semantics.SemConditionVisitor#visit(com.ibm.rules.engine.ruledef.semantics.SemProductCondition, java.lang.Object)
	 */
	@Override
	public CampRule visit(SemProductCondition ast, Void parameter) {
		while (ProductReducer.isReducible(ast)) {
			ProductReducer reducer = new ProductReducer(factory, ast);
			ast = (SemProductCondition) reducer.transformCondition(ast);
		}
		CampRule ans = null;
		for (SemCondition c : ast.getConditions()) {
			CampRule nextRule = c.accept(this, null);
			ans = ans == null ? nextRule : new CompoundRule(ans, nextRule);
		}
		return ans;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemThis)
	 */
	@Override
	public CampPattern visit(SemThis thisValue) {
		// TODO it isn't clear this is always the right thing to do
		return CampPattern.IT;
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemValueSet)
	 */
	@Override
	public CampPattern visit(SemValueSet valueSet) {
		return notImplemented(valueSet);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueAndStatementVisitor#visit(com.ibm.rules.engine.lang.semantics.SemVariableAssignment)
	 */
	@Override
	public CampPattern visit(SemVariableAssignment value) {
		return notImplemented(value);
	}

	/* (non-Javadoc)
	 * @see com.ibm.rules.engine.lang.semantics.SemValueVisitor#visit(com.ibm.rules.engine.lang.semantics.SemVariableValue)
	 */
	@Override
	public CampPattern visit(SemVariableValue value) {
		if (value.getVariableDeclaration() instanceof SemClassCondition)
			return CampPattern.IT;
		String var = getVariableName(value);
		if (var != null)
			return CampMacros.lookup(var);
		else
			return CampPattern.IT;
	}

	/**
	 * Translate the aggregate operator types from int to float as appropriate
	 * @param op the op
	 * @return the translation of the op (may be the same op)
	 */
	private UnaryOperator aggregateOpToFloat(UnaryOperator op) {
		switch (op) {
		case OpNatMax:
			return UnaryOperator.OpFloatBagMax;
		case OpNatMin:
			return UnaryOperator.OpFloatBagMin;
		case OpNatMean:
			return UnaryOperator.OpFloatMean;
		case OpNatSum:
			return UnaryOperator.OpFloatSum;
		default:
			return op;
		}
	}

	/**
	 * Indicates whether a SemTypeRestriction is one that we know how to translate
	 */
	private boolean canTranslateRestriction(SemTypeRestriction type) {
		SemDomain domain = type.getDomain();
		if (domain.getKind() == SemDomainKind.COLLECTION) {
			return canTranslateType(((SemCollectionDomain) domain).getElementType());
		}
		return false;
	}

	/**
	 * Indicates whether a SemType is one that we know how to translate
	 */
	private boolean canTranslateType(SemType type) {
		switch (type.getKind()) {
		case BOOLEAN:
		case INT:
		case BYTE:
		case LONG:
		case SHORT:
		case FLOAT:
		case DOUBLE:
		case CHAR:
		case STRING:
		case RESTRICTION:
			return canTranslateRestriction((SemTypeRestriction) type);
		case ARRAY:
			return canTranslateType(((SemArrayClass) type).getComponentType());
		default:
			break;
		}
		if (isEnumeration(type))
			return true;
		if (type instanceof SemClass)
			return ((SemClass) type).getNativeClass() != null;
		return false;
	}

	/** Issue the closing bracket of a passert iff the calling context was what started it */
	private CampPattern checkPassertEnd(CampPattern result, boolean passertStarted) {
		if (passertStarted) {
			passertSeen = false;
			return new AssertPattern(result);
		}
		return result;
	}

	/** Manipulate the initial passert on a series of patterns composed using pbinop and punop */
	private boolean checkPassertStart() {
		if (passertSeen) return false;
		return passertSeen = true;
	}

	/**
	 * Check whether a SemTypeKind has an "easy" (for our Coq code) toString semantics.  This is true of primitive
	 *   types (assuming we can handle them) but not of arbitrary Objects.  The Coq code will format anything,
	 *   but, in the case of Objects, it will unbrand then and format their contents, which does not match the
	 *   JRules semantics.
	 * @param kind the type kind
	 * @return whether it has an "easy" toString
	 */
	private boolean easyToString(SemTypeKind kind) {
		switch(kind) {
		case BOOLEAN:
		case BYTE:
		case CHAR:
		case DOUBLE:
		case FLOAT:
		case INT:
		case LONG:
		case SHORT:
		case STRING:
			return true;
		default:
			return false;
		}
	}

	/**
	 * Expand an attribute value into a canonical link chain before processing all the "dots"
	 * @param val the attribute value to expand
	 * @param canonical the canonical link chain
	 */
	private void expandAttributeValue(SemAttributeValue val, List<SemAttributeValue> canonical) {
		SemValue previous = val.getCurrentObject();
		if (previous instanceof SemAttributeValue) {
			expandAttributeValue((SemAttributeValue) previous, canonical);
		}
		canonical.add(val);
	}


	/** Fill in a chain of SemAttributeValue links from class conditions in a product condition */
	private boolean getAttributeValueLink(SemCondition ast, List<SemAttributeValue> results) {
		if (ast instanceof SemClassCondition) {
			SemClassCondition clsCond = (SemClassCondition) ast;
			if (clsCond.hasGenerator()) {
				SemValueConditionGenerator generator = clsCond.getGenerator().getValueConditionGenerator();
				SemValue value = generator.getValue();
				if (value instanceof SemAttributeValue) {
					results.add((SemAttributeValue) value);
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Given a type, return its component type iff it is an array or collection, otherwise null
	 * @param type the type to examine
	 * @return the component type or null
	 */
	private SemType getComponentType(SemType type) {
		switch (type.getKind()) {
		case RESTRICTION: {
			SemDomain domain = ((SemTypeRestriction) type).getDomain();
			if (domain.getKind() == SemDomainKind.COLLECTION)
				return ((SemCollectionDomain) domain).getElementType();
			break;
		}
		case ARRAY:
			return ((SemArrayClass) type).getComponentType();
		default:
			break;
		}
		if (type instanceof SemClass) {
			SemClass cls = (SemClass) type;
			Class<?> nativeCls = cls.getNativeClass();
			if (nativeCls != null) {
				if (Collection.class.isAssignableFrom(nativeCls)) {
					SemGenericInfo<SemGenericClass> genericInfo = cls.getGenericInfo();
					if (genericInfo != null) {
						return genericInfo.getGenericParameters().getTypeParameters().get(0);
					}
				}
			}
		}
		return null;
	}

	/** Gets the variable name from a SemVariableCondition or returns null if none is found */
	private String getConditionVariableName(SemVariableCondition ast) {
		for (SemLocalVariableDeclaration decl : ast.getBindings()) {
			SemValue initValue = decl.getInitialValue();
			if (null != initValue && initValue instanceof SemVariableValue) {
				SemVariableValue var = (SemVariableValue) initValue;
				if (var.getVariableDeclaration() == ast)
					return decl.getVariableName();
			}
		}
		return null;
	}

	/**
	 * Strip off one layer of product condition when vacuous
	 */
	private SemCondition getEffectiveCondition(SemCondition condition) {
		if (condition instanceof SemProductCondition) {
			List<SemCondition> conditions = ((SemProductCondition) condition).getConditions();
			if (conditions.size() == 1)
				return conditions.get(0);
		}
		return condition;
	}

	/**
	 * Return the id attribute of a type; if the type is not a class, there can be no id attribute.  Otherwise,
	 *  the attributes of the class are searched
	 * @param type the type to analyze
	 * @return the name of the id attribute or null if the type is not a class or there is no id attribute
	 */
	private String getIdAttribute(SemType type) {
		// This is meaningful only in the insights version of ODM but we have revised this code to be dependent only on the
		// classic version.   There is never any id attribute.  We may consider revisiting this.
		return null;
	}

	/**
	 * Get the native class from a type or null if it doesn't denote a native class
	 * @param theType
	 * @return the native class or null
	 */
	private Class<?> getNativeClass(SemType theType) {
		return theType instanceof SemClass ? ((SemClass) theType).getNativeClass() : null;
	}

	/**
	 * Common subroutine for processing both per-entity and global aggregates.  Gets the "over" expression and the
	 *   operator
	 * @param newObject the SemNewObject portion of the original aggregate
	 * @param ast the original aggregate condition
	 * @param linkChain the active link chain if there is one or null otherwise
	 * @return the "over" and the "op as a pair of objects in an array
	 */
	private Object[] getOverAndOp(SemNewObject newObject, SemAggregateCondition ast, List<SemAttributeValue> linkChain) {
		SemType type = newObject.getConstructor().getDeclaringType();
		SemAggregateFunctionMetadata meta = (SemAggregateFunctionMetadata) type
				.getMetadata(SemAggregateFunctionMetadata.class);
		String tName = (null == meta) ? type.getDisplayName() : meta.getName();
		List<SemValue> args = ast.getAggregateApplication().getArguments();
		SemValue over = null;
		if (1 == args.size())
			over = args.get(0);
		if (over instanceof SemConstant) // special convention for agg rules using PartialMoment
			over = null;
		else if (over != null) 
			over = simplify(over);
		UnaryOperator op = null;
		if (tName.startsWith("java.util.ArrayList"))
			op = UnaryOperator.OpIdentity;
		else if ("count".equals(tName))
			op = UnaryOperator.OpCount;
		else if ("min".equals(tName))
			op = UnaryOperator.OpNatMin;
		else if ("max".equals(tName))
			op = UnaryOperator.OpNatMax;
		else if ("sum".equals(tName))
			op = UnaryOperator.OpNatSum;
		else if ("mean".equals(tName))
			op = UnaryOperator.OpNatMean;
		else
			notImplemented("Aggregation operator " + tName);
		boolean isFloat;
		if (over != null)
			isFloat = isFloatingPoint(over.getType());
		else if (linkChain != null)
			isFloat = isFloatingPoint(getValueType(linkChain));
		else {
			notImplemented("Aggregates whose collection element type cannot be detemined");
			return null; // not reached
		}
		if (isFloat)
			op = aggregateOpToFloat(op);
		else if (op == UnaryOperator.OpNatMean) {
			op = UnaryOperator.OpFloatMean;
			over = factory.cast(SemCast.Kind.HARD, factory.getObjectModel().getType(SemTypeKind.DOUBLE), over);
		}
		return new Object[] {over, op};
	}

	/**
	 * Given a "link chain" (ordered list of SemAttributeValue representing an access path) return the type of the
	 *   overall expression (ie the last link in the chain)
	 * @param linkChain the link chain
	 * @return the type
	 */
	private SemType getValueType(List<SemAttributeValue> linkChain) {
		return linkChain.isEmpty() ? null : linkChain.get(linkChain.size() - 1).getType();
	}

	/** Gets the variable name from a SemVariableValue or null if the SemVariableValue does not have
	 *   a variable name (e.g. when its SemVariableDeclaration is a SemCondition without bindings). */
	private String getVariableName(SemVariableValue ast) {
		SemVariableDeclaration decl = ast.getVariableDeclaration();
		SemLocalVariableDeclaration realDecl = null;
		if (decl instanceof SemLocalVariableDeclaration)
			realDecl = (SemLocalVariableDeclaration) decl;
		else
			return null;
		return realDecl.getVariableName();
	}

	/** Gets an array of names from the argument list of a formatEntities call.  The list is in the middle argument */
	private List<String> getVariableNames(List<SemValue> vals) {
		if (vals.size() > 3) {
			SemValue listArg = vals.get(2);
			if (listArg instanceof SemExtension) {
				List<SemValue> args = ((SemExtension) listArg).getValues();
				List<String> ans = new ArrayList<>();
				boolean allStrings = true;
				for (SemValue arg : args) {
					if (arg instanceof SemConstant) {
						Object val = ((SemConstant) arg).getValue();
						if (val instanceof String) {
							ans.add((String) val);
							continue;
						}
					}
					allStrings = false;
					break;
				}
				if (allStrings) return ans;
			}
		}
		throw new IllegalStateException("formatEntities arguments did not have the expected form");
	}

	/**
	 * Get the variable names of objects used to match a SemCondition.
	 * @param condition the condition
	 * @return the list of variable names
	 */
	private List<String> getVariableNames(SemCondition condition) {
		if (condition instanceof SemProductCondition) {
			List<SemCondition> subconditions = ((SemProductCondition) condition).getConditions();
			List<String> ans = new ArrayList<>();
			for (SemCondition cond : subconditions) {
				ans.addAll(getVariableNames(cond));
			}
			return ans; // May be empty if no subcondition produced anything
		} else if (condition instanceof SemVariableCondition) {
			SemVariableDeclaration decl = ((SemVariableCondition) condition).asValue().getVariableDeclaration();
			if (decl instanceof SemNamedVariableDeclaration)
				return Collections.singletonList(((SemNamedVariableDeclaration) decl).getVariableName());
			if (condition instanceof SemAggregateCondition)
				condition = ((SemAggregateCondition) condition).getGeneratorCondition();
			if (condition instanceof SemClassCondition) {
				// either originally or after chasing through an aggregate condition
				SemValue generatorValue = ((SemClassCondition) condition).getValueConditionGenerator().getValue();
				if (generatorValue instanceof SemAttributeValue)
					return Collections.singletonList(((SemAttributeValue) generatorValue).getAttribute().getName());
			}
		}
		// If we arrive here we did not produce a compound answer from a product condition nor a simple answer from a variable condition
		// Look at the bindings.
		List<SemLocalVariableDeclaration> bindings = condition.getBindings();
		List<String> ans = new ArrayList<>();
		for (SemLocalVariableDeclaration binding : bindings)
			ans.add(binding.getVariableName());
		return ans; // May be empty if there are no bindings
	}

	/**
	 * When we don't have an original object model, this heuristically decides that a type is an enum.
	 * For the heuristic to fire, all members must be static and public and of the type's type.
	 * There must be no methods other than an equals method.
	 * @return true if type looks like an enumeration enough to take a chance on it.
	 */
	private boolean heuristicEnum(SemClass type) {
		Collection<SemMethod> methods = type.getMethods();
		if (methods.size() > 1)
			return false;
		if (methods.size() == 1 && !methods.iterator().next().getName().equals("instanceof"))
			return false;
		Collection<SemAttribute> attrs = type.getExtra().getAllAttributes();
		for (SemAttribute attr : attrs) {
			if (attr.getName().equals("class")) continue;
			if (!attr.isStatic())
				return false;
			if (!attr.getAttributeType().equals(type))
				return false;
		}
		return true;
	}

	/**
	 * Get an int from a SemValue assuming it is a constant (notImplemented exception if not)
	 * @param value the value to turn into an int
	 * @return the int
	 */
	private int intFrom(SemValue value) {
		if (value.isConstant()) {
			return ((Number) ((SemConstant) value).getValue()).intValue();
		}
		notImplemented("Non-constant value as argument to temporal construction: " + value);
		return -1; // not reached
	}

	/** Checks whether a method invocation is the contains method of a collection */
	private boolean isContains(SemMethodInvocation ast) {
		SemMethod method = ast.getMethod();
		if (!method.getName().equals("contains")) return false; // must have the expected name
		SemType declaringType = method.getDeclaringType();
		if (declaringType instanceof SemBagClass)
			return true;
		Class<?> nativeClass = getNativeClass(declaringType);
		return nativeClass != null && Collection.class.isAssignableFrom(nativeClass);
	}

	/**
	 * Test whether a method invocation ast is a call to CollectionUtils.containsAny
	 * @param ast the SemMethodInvocation ast
	 * @return true if it's a containsAny call
	 */
	private boolean isContainsAny(SemMethodInvocation ast) {
		SemMethod method = ast.getMethod();
		return method.getName().equals("containsAny") &&
				method.getDeclaringType().getDisplayName().equals(APACHE_COLLECTION_UTIL) &&
				ast.getCurrentObject() == null;
	}

	/**
	 * Test whether a type is an enumeration type; if so, its translation is integer (at least for now).
	 * @param type the type to test
	 * @return true if it is an an enumeration
	 */
	private boolean isEnumeration(SemType type) {
		if (type instanceof SemClass) {
			Class<?> nativeClass = ((SemClass) type).getNativeClass();
			if (nativeClass != null && nativeClass.isEnum()) return true;
			return heuristicEnum((SemClass) type);
		}
		return false;
	}

	/**
	 * Return true iff type denotes a primitive numeric type
	 * @param type the type to check
	 * @return true iff it is numeric
	 */
	private boolean isFloatingPoint(SemType type) {
		Class<?> nativeClass = type instanceof SemClass ? ((SemClass) type).getNativeClass() : null;
		if (nativeClass == null) return false;
		if (nativeClass.isPrimitive()) 
			switch (nativeClass.getName()) {
			case "double":
			case "float":
				return true;
			default:
				return false;
			}
		if (Collection.class.isAssignableFrom(nativeClass)) {
			new Object();
		}
		return Double.class.isAssignableFrom(nativeClass) || Float.class.isAssignableFrom(nativeClass);
	}

	/** Test whether a method invocation ast is a call to Runtime.formatEntities */
	private boolean isFormatEntities(SemMethodInvocation ast) {
		SemMethod method = ast.getMethod();
		return method.getName().equals("formatEntities") &&
				method.getDeclaringType().getDisplayName().equals(RuntimeUtils.class.getName()) &&
				ast.getCurrentObject() == null;
	}

	/** Tests whether a method invocation is for the toString method of Integer */
	private boolean isIntegerToString(SemMethodInvocation ast) {
		SemValue receiver = ast.getCurrentObject();
		SemMethod method = ast.getMethod();
		String type = method.getDeclaringType().getDisplayName();
		List<SemValue> args = ast.getArguments();
		return null == receiver && Integer.class.getName().equals(type)
				&& "toString".equals(method.getName()) && 1 == args.size();
	}

	/**
	 * Return true iff type denotes a primitive numeric type
	 * @param type the type to check
	 * @return true iff it is numeric
	 */
	private boolean isNumeric(SemType type) {
		Class<?> nativeClass = type instanceof SemClass ? ((SemClass) type).getNativeClass() : null;
		if (nativeClass == null) return false;
		if (nativeClass.isPrimitive()) 
			switch (nativeClass.getName()) {
			case "int":
			case "double":
			case "long":
			case "short":
			case "byte":
			case "float":
				return true;
			default: // char or boolean
				return false;
			}
		return Number.class.isAssignableFrom(nativeClass);
	}

	/** Test whether a type is something we intend to treat as an object type.  */
	private boolean isObjectType(SemType type) {
		if (isEnumeration(type)) return false;
		if (type instanceof SemClass) 
			switch (type.getKind()) {
			case BOOLEAN:
			case BYTE:
			case CHAR:
			case DOUBLE:
			case FLOAT:
			case INT:
			case LONG:
			case SHORT:
			case VOID:
			case STRING:
			case ARRAY:
				return false;
			default:
				Class<?> nativeCls = ((SemClass) type).getNativeClass();
				if (nativeCls != null) {
					if (Collection.class.isAssignableFrom(nativeCls)) {
						return false;
					} else if (Boolean.class.isAssignableFrom(nativeCls)) {
						return false;
					} else if (Number.class.isAssignableFrom(nativeCls)) {
						return false;
					}
				}
				return true;
			}
		else
			return false;
	}

	/**
	 * Determine if a generator found in an aggregate condition means that it's "per entity" 
	 */
	private boolean isPerEntityGenerator(SemConditionGenerator generator) {
		SemValue collectionValue = generator.getValueConditionGenerator().getValue();
		if (collectionValue instanceof SemAttributeValue 
				&& ((SemAttributeValue) collectionValue).getCurrentObject() instanceof SemThis)
			return false;
		return true;
	}

	/**
	 * Determine if a production rule is actually a SemQuery in spirit (in the solution archive, the ARL representation
	 *  of the local query for the Q1 engine takes the form of a production rule)
	 * @param block the statement block from the SemActionContent of the rule
	 * @return true if the form of the statements indicates a query
	 */
	private boolean isQueryAsRule(SemBlock block) {
		List<SemStatement> statements = block.getStatements();
		if (statements.size() != 1)
			return false;
		SemStatement toCheck = statements.get(0);
		return toCheck instanceof SemAttributeAssignment && 
				"localQueryResult".equals(((SemAttributeAssignment) toCheck).getAttribute().getName());
	}

	/**
	 * Determine if a method invocation ast is obtaining the size of a collection
	 * @param ast the node to examine
	 * @return true if it is a size method
	 */
	private boolean isSizeMethod(SemMethodInvocation method) {
		SemMethod callee = method.getMethod();
		List<SemValue> args = method.getArguments();
		if (args.size() == 1 && callee.getName().equals(GET_SIZE) && 
				callee.getDeclaringType().getDisplayName().equals(COLLECTION_UTIL)) {
			return true;
		}
		if (args.size() == 0 && callee.getName().equals(SIZE)) {
			SemType declaringType = callee.getDeclaringType();
			if (declaringType instanceof SemClass) {
				if (Collection.class.isAssignableFrom(((SemClass) declaringType).getNativeClass())) {
					return true;
				}
			}
		}
		return false;
	}

	/** Tests whether a method invocation is for the special stringListToString method defined in Runtime */
	private boolean isStringListToString(SemMethodInvocation ast) {
		SemValue receiver = ast.getCurrentObject();
		SemMethod method = ast.getMethod();
		String type = method.getDeclaringType().getDisplayName();
		List<SemValue> args = ast.getArguments();
		return null == receiver && RuntimeUtils.class.getName().equals(type)
				&& "stringListToString".equals(method.getName()) && 1 == args.size();
	}

	/** Test whether a method invocation is a println or the ODM equivalent thereof */
	private boolean isSystemOutPrintln(SemMethodInvocation ast) {
		SemValue receiver = ast.getCurrentObject();
		if (null != receiver && receiver instanceof SemAttributeValue) {
			SemAttributeValue attr = (SemAttributeValue) receiver;
			if (null == attr.getCurrentObject()) {
				String type = attr.getAttribute().getDeclaringType().getDisplayName();
				String field = attr.getAttribute().getName();
				String method = ast.getMethod().getName();
				if (System.class.getName().equals(type) && "out".equals(field)
						&& "println".equals(method) && 1 == ast.getArguments().size())
					return true;
			}
		}
		SemMethod method = ast.getMethod();
		return method.getDeclaringType().getDisplayName().equals("ilog.rules.brl.System")
				&& method.getName().equals("printMessage");
	}

	/**
	 * Determine if a SemType is one of several possible temporal types.  For various reasons, these have
	 *   both a semi-fictional representation and an actual one the latter drawn from java.time.*).
	 * TODO the current recognition doesn't distinction between dates, times, durations, etc. so it is 
	 * possible for weird cases to be missed, but I think it works for correct code at least.
	 * @param type the type to test
	 * @return true iff the type is a temporal type
	 */
	private boolean isTemporalType(SemType type) {
		return temporalTypes.contains(type.getDisplayName());
	}

	/**
	 * Test whether a SemValue has a temporal type
	 * @param toTest the SemValue to test
	 * @return true if it has a temporal type
	 */
	private boolean isTemporalValue(SemValue toTest) {
		if (toTest == null)
			return false;
		return isTemporalType(toTest.getType());
	}

	/**
	 * Check whether a method invocation represents a conversion from a string to epoch milliseconds on
	 *   the assumption that the string represents a dateTime.  This is a somewhat specialized use case
	 *   but one that can arise in the general case and has practical import for us right now.
	 * @param ast the SemMethodInvocation to analyze
	 * @return true if it is of the form ZonedDateTime.parse(string).toInstant().toEpochMilli();
	 */
	private boolean isTimeStringToEpochMillis(SemMethodInvocation ast) {
		if ("toEpochMilli".equals(ast.getMethod().getName())) {
			SemValue recvr = ast.getCurrentObject();
			if (recvr instanceof SemMethodInvocation) {
				ast = (SemMethodInvocation) recvr;
				if ("toInstant".equals(ast.getMethod().getName())) {
					recvr = ast.getCurrentObject();
					if (recvr instanceof SemMethodInvocation) {
						SemMethod toTest = ((SemMethodInvocation) recvr).getMethod();
						return "parse".equals(toTest.getName()) && ZonedDateTime.class.getName().equals(toTest.getReturnType().getDisplayName());
					}
				}
			}
		}
		return false;
	}

	/** Tests whether a method invocation is for the general toString() method of any object */
	private boolean isToString(SemMethodInvocation ast) {
		SemValue receiver = ast.getCurrentObject();
		String method = ast.getMethod().getName();
		List<SemValue> args = ast.getArguments();
		return null != receiver && "toString".equals(method) && 0 == args.size();
	}


	/** Tests whether a method invocation is for an equals between compatible types that we know how to translate */
	private boolean isTranslatableEquals(SemMethodInvocation ast) {
		SemMethod method = ast.getMethod();
		if ("equals".equals(method.getName())) {
			List<SemValue> args = ast.getArguments();
			if (args.size() == 1) {
				SemType left = method.getDeclaringType();
				SemType right = args.get(0).getType();
				if (canTranslateType(left) && canTranslateType(right))
					return left.getExtra().isApplicable(right) || right.getExtra().isApplicable(left);
			}
		}
		return false;
	}

	/** Tests whether a method invocation is the valueOf method of a primitive type */
	private boolean isValueOf(SemMethodInvocation ast) {
		if (ast.getCurrentObject() != null) return false; // must be static
		SemMethod method = ast.getMethod();
		if (!method.getName().equals("valueOf")) return false; // must have the expected name
		Class<?> cls = ((SemClass) method.getDeclaringType()).getNativeClass();
		return Number.class.isAssignableFrom(cls) || cls == Character.class || cls == Boolean.class;
	}

	/** Tests whether a method invocation is an xxxValue method of a primitive type */
	private boolean isXValue(SemMethodInvocation ast) {
		SemValue obj = ast.getCurrentObject();
		if (obj == null) return false; // must not be static
		SemMethod method = ast.getMethod();
		if (!method.getName().endsWith("Value")) return false; // must have the expected name form
		if (!ast.getArguments().isEmpty()) return false;  // must not have arguments
		Class<?> cls = ((SemClass) obj.getType()).getNativeClass();
		return Number.class.isAssignableFrom(cls) || cls == Character.class || cls == Boolean.class;
	}

	/**
	 * Get a long from a SemValue assuming it is a constant (notImplemented exception if not)
	 * @param value the value to turn into an long
	 * @return the long
	 */
	private long longFrom(SemValue value) {
		if (value.isConstant()) {
			return ((Number) ((SemConstant) value).getValue()).longValue();
		}
		notImplemented("Non-constant value as argument to temporal construction: " + value);
		return -1; // not reached
	}

	/**
	 * Common finishing for all aggregate cases (global and per-entity)
	 * @param ast the ast being processed
	 * @param pattern the pattern that constitutes the core of the answer
	 * @return the Rule form of the answer
	 */
	private CampRule makeAggregateAnswer(SemAggregateCondition ast, CampPattern pattern) {
		String varName = getConditionVariableName(ast);
		if (varName != null) pattern = CampMacros.is(varName, pattern);
		return new GlobalRule(pattern);
	}

	/** We arrive here when there's a hole in our implementation that arguably should be filled some day.
	 * This method does not actually return */
	private CampPattern notImplemented(Object ast) {
		String at = "";
		String what = ast.toString();
		if (ast instanceof SemAnnotatedElement) {
			SemMetadata loc = ((SemAbstractAnnotatedElement) ast).getMetadata(SemTextLocationMetadata.class);
			if (null != loc)
				at = "At" + loc.toString() + ": ";
		}
		String name = ast.getClass().getName();
		if (what.contains(name)) what = name;
		throw new UnsupportedOperationException(at + "not implemented: " + what);
	}


	/**
	 * Replace an integer op with its floating point counterpart if the types are floating point.
	 * This method is only called when the op is arithmetic and also floating point is enabled.
	 * We assume that SemRule always casts to a common type.  If we were completely sure of this
	 *   we'd only need one type argument but we use the opportunity to check that the assumption
	 *   holds.
	 * @param op the op
	 * @param type1 the first type
	 * @param type2 the second type
	 * @return the BinaryOperator to use
	 */
	private BinaryOperator opByType(BinaryOperator op, SemType type1, SemType type2) {
		if (isFloatingPoint(type1) && isFloatingPoint(type2)) {
			switch (op) {
			case NatDiv:
				return BinaryOperator.FloatDiv;
			case NatMax:
				return BinaryOperator.FloatMax;
			case NatMin:
				return BinaryOperator.FloatMin;
			case NatMinus:
				return BinaryOperator.FloatMinus;
			case NatMult:
				return BinaryOperator.FloatMult;
			case NatPlus:
				return BinaryOperator.FloatPlus;
			case OpLe:
				return BinaryOperator.FloatLe;
			case OpLt:
				return BinaryOperator.FloatLt;
			case NatRem:
				// Punting on this.  In theory we should translate it but Java's semantics are
				// different than IEEE and possibly / probably some other languages.
			default:
				notImplemented("Floating point equivalent to operation " + op);
				return null; // not reached
			}
		} else if (!isFloatingPoint(type1) && !isFloatingPoint(type2))
			return op;
		notImplemented(String.format("Operator %s between %s and %s", op, type1.getDisplayName(), type2.getDisplayName()));
		return null; // not reached
	}

	/**
	 * Process the accumulated chain of SemAttributeValue representing an access path
	 * @param terminalMap if true, a map operation is added when the type of the final link is a collection
	 * @return the CampPattern representing the evaluation of that access path in CAMP
	 */
	private CampPattern processLinkChain(boolean terminalMap) {
		/* First canonicalize the link chain to unfold attribute values that have attribute values as their
		 *   current object.
		 */
		List<SemAttributeValue> canonical = new ArrayList<>();
		for (SemAttributeValue val : linkChain) {
			expandAttributeValue(val, canonical);
		}
		linkChain = null; // reset for next time
		pmapCount = 0; // and this too

		/* Prime the iteration */
		Iterator<SemAttributeValue> attributes = canonical.iterator();
		SemAttributeValue ast = attributes.next();

		/* Consider whether to start with a saved fetchRef.  There will be one if the
		 *  link chain arises inside the translation of a nested aggregation and the
		 *  collection is a colllection of references. */
		CampPattern current = savedFetchRef;

		/* If no saved fetchRef, take the currentObject of the first attribute and visit it to get started.  If it
		 *  represents anything other than 'pit' issue a LetIt to start the chain. */
		if (current == null) {
			CampPattern start = ast.getCurrentObject().accept(this);
			current = start == CampPattern.IT ? null : new LetItPattern(start);
		}

		/* Loop through the attributes completing the expression */
		String idAttribute = null;
		SemType componentType = null;
		for (;;) {
			CampPattern access = CampMacros.unbrandDot(ast.getAttribute().getName());
			if (isObjectType(ast.getType())) {
				access = new CompoundPattern(access, new LetItPattern(CampPattern.LEFT));
			}
			if (idAttribute != null)
				access = new CompoundPattern(new CompoundPattern(new LetItPattern(CampPattern.LEFT), 
						CampMacros.fetchRef(idAttribute, componentType.getDisplayName())), access); 
			else
				access = tryRelationship(ast, access);
			current = current == null ? access : new CompoundPattern(current, access);
			if (attributes.hasNext()) {
				SemAttributeValue next = attributes.next();
				/* Check for iterated case */
				componentType = getComponentType(ast.getType());
				if (componentType != null) {
					SemType toType = next.getCurrentObject().getType();
					if (toType.getExtra().isAssignableFrom(componentType)) {
						/* Iterated case: record whether it is a reference and make it into
						 * a map
						 */
						idAttribute = getIdAttribute(componentType);
						current = new CompoundPattern(new LetItPattern(current.applyTo(CampPattern.IT)), new MapPattern()); 
						if (idAttribute == null && isObjectType(componentType))
							current = new CompoundPattern(current, new LetItPattern(CampPattern.LEFT));
						pmapCount++;
					} else
						/* Not iterated case, so don't record */
						componentType = null;
				}
				ast = next;
			}
			else
				break;
		}
		if (terminalMap && getComponentType(ast.getType()) != null) {
			current = new CompoundPattern(new LetItPattern(current.applyTo(CampPattern.IT)), new MapPattern());
			// TODO perhaps more logic needed here (see above)
			pmapCount++;
		}
		return current.applyTo(CampPattern.IT);
	}

	/**
	 * Simplify a SemValue based on the idea that we translate some things as identities; sometimes, even without translating,
	 *   we want to find the simplest possible SemValue that gives the same result
	 * @param value the SemValue to simplify
	 * @return the simplified value, which might be the same
	 */
	private SemValue simplify(SemValue value) {
		if (value instanceof SemMethodInvocation) {
			SemMethodInvocation smi = (SemMethodInvocation) value;
			if (isXValue(smi)) {
				return simplify(smi.getCurrentObject());
			} else if (isValueOf(smi)) {
				return simplify(smi.getArguments().get(0));
			} // else cannot simplify
		}
		if (value instanceof SemCast) {
			SemCast cast = (SemCast) value;
			SemType toType = cast.getType();
			SemValue subValue = cast.getValue();
			if (toType.equals(subValue.getType()) || isNumeric(toType) && isNumeric(subValue.getType()))
				// See similar logic in visit(SemCast)
				return simplify(subValue);
			// else cannot simplify
		}
		return value;
	}

	/**
	 * Translate a + operator, which might be arithmetic or string concatenation
	 * @param ast the ast to examine and translate
	 * @return the translation
	 */
	private CampPattern translateAdd(SemMethodInvocation ast) {
		SemValue arg1 = ast.getArguments().get(0);
		SemValue arg2 = ast.getArguments().get(1);
		if (arg1.getType().getKind() == SemTypeKind.STRING && easyToString(arg2.getType().getKind()) ||
				arg2.getType().getKind() == SemTypeKind.STRING && easyToString(arg1.getType().getKind())) {
			CampPattern stringArg1 = CampMacros.stringify(arg1.accept(this));
			CampPattern stringArg2 = CampMacros.stringify(arg2.accept(this));
			return new BinaryPattern(BinaryOperator.OpStringConcat, stringArg1, stringArg2);
		}
		else if (arg1.getType().getKind() == SemTypeKind.INT && arg2.getType().getKind() == SemTypeKind.INT)
			return translateBinaryOp(BinaryOperator.NatPlus, arg1, arg2);
		return notImplemented(ast);
	}

	/** 
	 * Provide a binary operator translation
	 * @param op the operator
	 * @param arg1 the first operand
	 * @param arg2 the second operand
	 * @return a CampPattern which is the translation
	 */
	private CampPattern translateBinaryOp(BinaryOperator op, SemValue arg1, SemValue arg2) {
		boolean started = op.isBoolean() ? checkPassertStart() : false;
		if (op.isArithmetic()) 
			op = opByType(op, arg1.getType(), arg2.getType());
		return checkPassertEnd(new BinaryPattern(op, arg1.accept(this), arg2.accept(this)), started);
	}

	/**
	 * Translate a block containing the statements of the action clause of a production rule.
	 * If the block contains a single statement which is a SemValue (e.g. a method call), it is simply
	 * translated according to the usual rules.  This allows for production rules that take charge of their
	 * own results display.  In all other cases (multiple statements in the block, statement that is not a SemValue)
	 * we gather up the variables that name objects in the condition and turn them into a VARIABLES macro.
	 * @param block the block to examine
	 * @param condition the condition from the original action rule, in case a search for variables that name objects is
	 *   required
	 * @return a translation (never returns null)
	 */
	private CampPattern translateBlock(SemBlock block, SemCondition condition) {
		List<SemStatement> statements = block.getStatements();
		if (1 == statements.size()) {
			SemStatement stmt = statements.get(0);
			if (stmt instanceof SemValue) {
				try {
					return ((SemValue) stmt).accept(this);
				} catch (UnsupportedOperationException e) {
				}
			}
		}
		List<String> variableNames = getVariableNames(condition);
		if (variableNames.isEmpty())
			return notImplemented("Action clause too difficult to analyze");
		return CampMacros.variables(variableNames);
	}

	/**
	 * Translate a "containsAny" method call to the bag intersection equivalent expression for CAMP
	 * @param x the SemValue for one collection 
	 * @param y the SemValue for the other collection
	 * @return the CAMP pattern required
	 */
	private CampPattern translateContainsAny(SemValue x, SemValue y) {
		boolean started = checkPassertStart();
		CampPattern countIntersect = new UnaryPattern(UnaryOperator.OpCount,
				new BinaryPattern(BinaryOperator.OpBagMin, x.accept(this), y.accept(this)));
		CampPattern eq0 = new BinaryPattern(BinaryOperator.OpEqual, new ConstPattern(0), countIntersect);
		CampPattern negation = new UnaryPattern(UnaryOperator.OpNeg, eq0);
		return checkPassertEnd(negation, started);
	}

	/**
	 * Translate a contains method call where the receiver is an interval (denoting a bag containing all the values
	 *  in the interval)
	 * @param interval the interval
	 * @param value the value being tested for containment in the interval
	 * @return the CampPattern that performs that test
	 */
	private CampPattern translateIntervalContains(SemInterval interval, SemValue value) {
		SemValue lower = interval.getLowerBound();
		SemValue higher = interval.getHigherBound();
		CampPattern geLower = translateBinaryOp(BinaryOperator.OpLe, lower, value);
		CampPattern leHigher = translateBinaryOp(BinaryOperator.OpLe, value, higher);
		return new BinaryPattern(BinaryOperator.OpAnd, geLower, leHigher);
	}

	/**
	 * Translate a not-equals expression
	 * @param ast the ast for the expression
	 * @return the translation
	 */
	private CampPattern translateNotEquals(SemMethodInvocation ast) {
		boolean started = checkPassertStart();
		List<SemValue> args = ast.getArguments();
		CampPattern ans = new UnaryPattern(UnaryOperator.OpNeg, translateBinaryOp(BinaryOperator.OpEqual, args.get(0), 
				args.get(1)));
		return checkPassertEnd(ans, started);
	}

	/**
	 * Translate an aggregate condition that does not aggregate on working memory but rather
	 *    on a per-entity collection
	 * @param ast the SemAggregateCondition found to meet the criteria for this method
	 * @return the translation
	 */
	private CampRule translatePerEntityAggregate(SemAggregateCondition ast) {
		/* Get the collection as a SemValue */
		SemClassCondition cond = (SemClassCondition) ast.getGeneratorCondition();
		SemValue collectionValue = cond.getGenerator().getValueConditionGenerator().getValue();
		SemType componentType = getComponentType(collectionValue.getType());

		/* Detect collection of references and do special processing */
		String idAttribute = getIdAttribute(componentType);
		if (idAttribute != null) {
			/* Collection of references */
			savedFetchRef = new CompoundPattern(new LetItPattern(CampPattern.LEFT), 
					CampMacros.fetchRef(idAttribute, componentType.getDisplayName())); 
		}

		/* Translate the tests, with savedFetchRef in force if appropriate; then clear the saved state */
		CampPattern filter = translateTests(cond.getTests());
		savedFetchRef = null;

		/* With 'it' set to the collection, map the filter to obtain the filtered collection */
		CampPattern filteredCollection = new LetItPattern(collectionValue.accept(this), new MapPattern(filter));

		/* Do the actual aggregation */
		SemNewObject newObject = (SemNewObject) ast.getAggregateApplication().getInstanceOfAggregateClass();
		UnaryOperator op = (UnaryOperator) getOverAndOp(newObject, ast, null)[1];
		return makeAggregateAnswer(ast, new UnaryPattern(op, filteredCollection));
	}

	/**
	 * Translate a method invocation known to be a size method invocation
	 * @param ast the method invocation node
	 * @return the translation
	 */
	private CampPattern translateSizeMethod(SemMethodInvocation ast) {
		/* First distinguish the static from the instance form and translate the collection */
		List<SemValue> args = ast.getArguments();
		CampPattern collection = (args.size() > 0 ? args.get(0) : ast.getCurrentObject()).accept(this);
		/* Produce a bag count operation on the collection */
		return new UnaryPattern(UnaryOperator.OpCount, collection);
	}

	/**
	 * Incomplete but evolving translation for object allocations involving temporal constructs
	 * @param ast the object allocation (SemNewObject)
	 * @return the translation
	 */
	private CampPattern translateTemporalAllocation(SemNewObject ast) {
		List<SemValue> args = ast.getArguments();
		if (DATE_TYPE.equals(ast.getType().getDisplayName())) {
			Iterator<SemValue> argIter = args.iterator();
			ZonedDateTime translation = ZonedDateTime.ofInstant(Instant.EPOCH, ZoneId.systemDefault())
					.withYear(intFrom(argIter.next())).withMonth(intFrom(argIter.next()))
					.withDayOfMonth(intFrom(argIter.next()));
			if (argIter.hasNext())
				translation = translation.withHour(intFrom(argIter.next()));
			if (argIter.hasNext())
				translation = translation.withMinute(intFrom(argIter.next()));
			if (argIter.hasNext())
				translation = translation.withSecond(intFrom(argIter.next()));
			ConstPattern constant = new ConstPattern(translation.toString());
			return new UnaryPattern(UnaryOperator.TimeFromString, constant);
		}
		if (TIME_TYPE.equals(ast.getType().getDisplayName()) && args.size() == 1) {
			long epochMilli = longFrom(args.get(0));
			LocalTime translation = ZonedDateTime.ofInstant(Instant.ofEpochMilli(epochMilli), 
					ZoneOffset.UTC).toLocalTime();
			// TODO this should really be a unique CAMP type corresponding to the TTRL type for LocalTimeComponentValue
			return new ConstPattern(translation.toString());
		}
		return notImplemented("Translation of temporal allocation: " + ast);
	}

	/**
	 * Translate a list of boolean tests, turning them into an asserted conjunction
	 * @param tests the tests to process
	 * @return a CampPattern for the translation
	 */
	private CampPattern translateTests(List<SemValue> tests) {
		if (0 == tests.size())
			return CampMacros.accept();
		CampPattern pattern = null;
		boolean started = checkPassertStart();
		for (SemValue test : tests) {
			CampPattern pat = test.accept(this);
			if (pattern == null)
				pattern = pat;
			else {
				pattern = new BinaryPattern(BinaryOperator.OpAnd, pattern, pat);
			}
		}
		return checkPassertEnd(pattern, started);
	}

	/**
	 * Generate the appropriate output for converting a String to a long.  At present, we only do this when the string is a constant
	 *   (in which case we can evaluate it at compile time and simply produce a long SemConstant).  Generalization to expressions
	 *   would be possible but would require timeDate manipulation functions to be present in coq.
	 * @param ast the SemMethodInvocation to convert, known to be of the proper form because it was examined by isTimeStringToEpochMillis
	 * @return
	 */
	private CampPattern translateTimeStringToEpochMillis(SemMethodInvocation ast) {
		ast = ((SemMethodInvocation) ast.getCurrentObject()); // the toInstant() call
		ast = ((SemMethodInvocation) ast.getCurrentObject()); // the parse() call
		SemValue val = ast.getArguments().get(0); // the string
		if (val instanceof SemConstant) {
			String string = (String) ((SemConstant) val).getValue();
			if (!string.contains("Z")) string += "Z";
			long millis = ZonedDateTime.parse(string).toInstant().toEpochMilli();
			return new ConstPattern(millis);
		}
		return notImplemented("String to date conversion for non-constants");
	}

	/**
	 * If an attribute value is a relationship reference, apply the appropriate macro form to the 
	 *   the access path (actually composes the functions to be applied later)
	 * @param value the attribute value in question
	 * @param access the access path so far, to be modified or not
	 * @return the appropriate CampPattern, either the original access or a modified
	 *   one for a relationship reference
	 */
	private CampPattern tryRelationship(SemAttributeValue value, CampPattern access) {
		SemValue source = value.getCurrentObject();
		SemClassCondition classSource = null;
		while (source instanceof SemVariableValue) {
			SemVariableDeclaration decl = ((SemVariableValue) source).getVariableDeclaration();
			if (decl instanceof SemClassCondition) {
				classSource = (SemClassCondition) decl;
				break;
			}
			else if (decl instanceof SemLocalVariableDeclaration) {
				source = ((SemLocalVariableDeclaration) decl).getInitialValue();
			}
		}
		SemType type = null;
		if (classSource != null && classSource.hasGenerator()) {
			SemConditionGenerator gen = classSource.getGenerator();
			if (gen.getValueConditionGenerator().getKind() == Kind.FROM)
				type = classSource.getVariableType();
		} else if (source instanceof SemAttributeValue)
			type = source.getType();
		String idAttribute = type == null ? null : getIdAttribute(type);
		if (idAttribute != null) {
			//        	System.out.println(value + " is an entity reference");
			return new CompoundPattern(CampMacros.fetchRef(idAttribute, type.getDisplayName()), access);
		}
		//    	System.out.println(value + " is not an entity reference");
		return access;
	}
}
