/**
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
package org.qcert.sqlpp;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumMap;
import java.util.Iterator;
import java.util.List;

import org.apache.asterix.common.exceptions.CompilationException;
import org.apache.asterix.common.functions.FunctionSignature;
import org.apache.asterix.lang.common.base.Expression;
import org.apache.asterix.lang.common.base.Expression.Kind;
import org.apache.asterix.lang.common.base.ILangExpression;
import org.apache.asterix.lang.common.base.Literal;
import org.apache.asterix.lang.common.clause.GroupbyClause;
import org.apache.asterix.lang.common.clause.LetClause;
import org.apache.asterix.lang.common.clause.LimitClause;
import org.apache.asterix.lang.common.clause.OrderbyClause;
import org.apache.asterix.lang.common.clause.OrderbyClause.OrderModifier;
import org.apache.asterix.lang.common.clause.UpdateClause;
import org.apache.asterix.lang.common.clause.WhereClause;
import org.apache.asterix.lang.common.expression.CallExpr;
import org.apache.asterix.lang.common.expression.FieldAccessor;
import org.apache.asterix.lang.common.expression.FieldBinding;
import org.apache.asterix.lang.common.expression.GbyVariableExpressionPair;
import org.apache.asterix.lang.common.expression.IfExpr;
import org.apache.asterix.lang.common.expression.IndexAccessor;
import org.apache.asterix.lang.common.expression.ListConstructor;
import org.apache.asterix.lang.common.expression.LiteralExpr;
import org.apache.asterix.lang.common.expression.OperatorExpr;
import org.apache.asterix.lang.common.expression.OrderedListTypeDefinition;
import org.apache.asterix.lang.common.expression.QuantifiedExpression;
import org.apache.asterix.lang.common.expression.RecordConstructor;
import org.apache.asterix.lang.common.expression.RecordTypeDefinition;
import org.apache.asterix.lang.common.expression.TypeReferenceExpression;
import org.apache.asterix.lang.common.expression.UnaryExpr;
import org.apache.asterix.lang.common.expression.UnorderedListTypeDefinition;
import org.apache.asterix.lang.common.expression.VariableExpr;
import org.apache.asterix.lang.common.literal.TrueLiteral;
import org.apache.asterix.lang.common.statement.CompactStatement;
import org.apache.asterix.lang.common.statement.ConnectFeedStatement;
import org.apache.asterix.lang.common.statement.CreateDataverseStatement;
import org.apache.asterix.lang.common.statement.CreateFeedPolicyStatement;
import org.apache.asterix.lang.common.statement.CreateFeedStatement;
import org.apache.asterix.lang.common.statement.CreateFunctionStatement;
import org.apache.asterix.lang.common.statement.CreateIndexStatement;
import org.apache.asterix.lang.common.statement.DatasetDecl;
import org.apache.asterix.lang.common.statement.DataverseDecl;
import org.apache.asterix.lang.common.statement.DataverseDropStatement;
import org.apache.asterix.lang.common.statement.DeleteStatement;
import org.apache.asterix.lang.common.statement.DisconnectFeedStatement;
import org.apache.asterix.lang.common.statement.DropDatasetStatement;
import org.apache.asterix.lang.common.statement.FeedDropStatement;
import org.apache.asterix.lang.common.statement.FeedPolicyDropStatement;
import org.apache.asterix.lang.common.statement.FunctionDecl;
import org.apache.asterix.lang.common.statement.FunctionDropStatement;
import org.apache.asterix.lang.common.statement.IndexDropStatement;
import org.apache.asterix.lang.common.statement.InsertStatement;
import org.apache.asterix.lang.common.statement.LoadStatement;
import org.apache.asterix.lang.common.statement.NodeGroupDropStatement;
import org.apache.asterix.lang.common.statement.NodegroupDecl;
import org.apache.asterix.lang.common.statement.Query;
import org.apache.asterix.lang.common.statement.SetStatement;
import org.apache.asterix.lang.common.statement.StartFeedStatement;
import org.apache.asterix.lang.common.statement.StopFeedStatement;
import org.apache.asterix.lang.common.statement.TypeDecl;
import org.apache.asterix.lang.common.statement.TypeDropStatement;
import org.apache.asterix.lang.common.statement.UpdateStatement;
import org.apache.asterix.lang.common.statement.WriteStatement;
import org.apache.asterix.lang.common.struct.OperatorType;
import org.apache.asterix.lang.common.struct.QuantifiedPair;
import org.apache.asterix.lang.common.struct.UnaryExprType;
import org.apache.asterix.lang.common.struct.VarIdentifier;
import org.apache.asterix.lang.sqlpp.clause.AbstractBinaryCorrelateClause;
import org.apache.asterix.lang.sqlpp.clause.FromClause;
import org.apache.asterix.lang.sqlpp.clause.FromTerm;
import org.apache.asterix.lang.sqlpp.clause.HavingClause;
import org.apache.asterix.lang.sqlpp.clause.JoinClause;
import org.apache.asterix.lang.sqlpp.clause.NestClause;
import org.apache.asterix.lang.sqlpp.clause.Projection;
import org.apache.asterix.lang.sqlpp.clause.SelectBlock;
import org.apache.asterix.lang.sqlpp.clause.SelectClause;
import org.apache.asterix.lang.sqlpp.clause.SelectElement;
import org.apache.asterix.lang.sqlpp.clause.SelectRegular;
import org.apache.asterix.lang.sqlpp.clause.SelectSetOperation;
import org.apache.asterix.lang.sqlpp.clause.UnnestClause;
import org.apache.asterix.lang.sqlpp.expression.CaseExpression;
import org.apache.asterix.lang.sqlpp.expression.IndependentSubquery;
import org.apache.asterix.lang.sqlpp.expression.SelectExpression;
import org.apache.asterix.lang.sqlpp.optype.SetOpType;
import org.apache.asterix.lang.sqlpp.struct.SetOperationInput;
import org.apache.asterix.lang.sqlpp.struct.SetOperationRight;
import org.apache.asterix.lang.sqlpp.visitor.base.ISqlppVisitor;

/**
 * A visitor for a parsed SQL++ expression, turning it into S-expression form.
 * At present, the S-expression form is designed to be consumed by qcert's SQL (as opposed to SQL++) support, since the latter is not yet in place.
 */
public class SqlppEncodingVisitor implements ISqlppVisitor<StringBuilder, StringBuilder> {
	private static final EnumMap<OperatorType, String> opNameMap = new EnumMap<>(OperatorType.class);
	private static final EnumMap<OperatorType, OperatorType> negations = new EnumMap<>(OperatorType.class);
	private static final EnumMap<UnaryExprType, String> unaryExprMap = new EnumMap<>(UnaryExprType.class);
	static {
		// All non-negated binary operators are here except 'concat', which is handled specially.  Note that 'between' is actually ternary 
		// and is also handled specially.
		opNameMap.put(OperatorType.GT, "greater_than");
		opNameMap.put(OperatorType.GE, "greater_than_or_equal");
		opNameMap.put(OperatorType.LT, "less_than");
		opNameMap.put(OperatorType.LE, "less_than_or_equal");
		opNameMap.put(OperatorType.EQ, "equal");
		opNameMap.put(OperatorType.FUZZY_EQ, "equal"); // No distinction at this level
		opNameMap.put(OperatorType.NEQ, "not_equal");
		opNameMap.put(OperatorType.AND, "and");
		opNameMap.put(OperatorType.OR, "or");
		opNameMap.put(OperatorType.LIKE, "like");
		opNameMap.put(OperatorType.DIV, "divide");
		opNameMap.put(OperatorType.IDIV, "divide");    // No distinction at this level
		opNameMap.put(OperatorType.MOD, "modulus");    // No support yet in sexp_to_sql_expr 
		opNameMap.put(OperatorType.CARET, "exponent"); // No support yet in sexp_to_sql_expr
		opNameMap.put(OperatorType.MUL, "multiply");
		opNameMap.put(OperatorType.IN, "isIn");
		opNameMap.put(OperatorType.MINUS, "subtract");
		opNameMap.put(OperatorType.PLUS, "add");
		
		// Only negations of binary operators and 'between' are here; 'not exists' (unary) is handled specially as are the special forms
		// starting with IS like IS NOT NULL (parser turns these into function calls).
		negations.put(OperatorType.NOT_BETWEEN, OperatorType.BETWEEN);
		negations.put(OperatorType.NOT_IN, OperatorType.IN);
		negations.put(OperatorType.NOT_LIKE, OperatorType.LIKE);

		// NOT_EXISTS is not in the following table because it is a negation and handled specially
		unaryExprMap.put(UnaryExprType.EXISTS, "exists");
		unaryExprMap.put(UnaryExprType.NEGATIVE, "minus");
		unaryExprMap.put(UnaryExprType.POSITIVE, "plus");  // No support yet in sexp_to_sql_expr.  Perhaps we should simply elide.
	}
	
	private boolean useDateNameHeuristic;
	
	public SqlppEncodingVisitor(boolean useDateNameHeuristic) {
		this.useDateNameHeuristic = useDateNameHeuristic;
	}

	@Override
	public StringBuilder visit(CallExpr node, StringBuilder builder) throws CompilationException {
		FunctionSignature signature = node.getFunctionSignature();
		String namespace = signature.getNamespace();
		String name = namespace != null && namespace.length() > 0 ? namespace + "." + signature.getName() : signature.getName();
		List<Expression> args = node.getExprList();
		// The following kluge is pretty arbitrary but seems needed since AsterixDB parses count(*) as count(1)
		if (name.equals("count") && args.size() == 1 && args.get(0).getKind() == Kind.LITERAL_EXPRESSION) {
			LiteralExpr lit = (LiteralExpr) args.get(0);
			if (lit.getValue().toString().equals("1"))
				args = Collections.emptyList();
		}
		// The following special cases are needed because AsterixDB treats "not" as a function and because we turn
		// various things into functions to match SQL++ conventions.
		if (args.size() == 1)
			switch (name) {
			case "not": 
				return handleNot(args.get(0), builder);
			case "date":
				return handleDate(args.get(0), builder);
			case "duration":
				return handleDuration(args.get(0), builder);
			case "get_year":
			case "get_month":
			case "get_day":
				return handleExtract(name.substring(4), args.get(0), builder);
			default:
				break;
			}
		builder = builder.append("(function ");
		builder = appendString(name, builder);
		for (Expression arg : args)
			arg.accept(this, builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(CaseExpression node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(cases ");
		Expression operand = node.getConditionExpr();
		if (operand != null && !isTrueLiteral(operand)) {
			builder = builder.append("(operand ");
			builder = operand.accept(this, builder);
			builder = builder.append(") ");
		}
		List<Expression> whens = node.getWhenExprs();
		List<Expression> thens = node.getThenExprs();
		Expression defaultValue = node.getElseExpr();
		assert whens.size() == thens.size();
		Iterator<Expression> thenIter = thens.iterator();
		for (Expression when : node.getWhenExprs()) {
			Expression then = thenIter.next();
			builder = builder.append("(case (when ");
			builder = when.accept(this,  builder);
			builder = builder.append(") (then ");
			builder = then.accept(this, builder);
			builder = builder.append(")) ");
		}
		if (defaultValue != null) {
			builder = builder.append("(default ");
			builder = defaultValue.accept(this, builder);
			builder = builder.append(")");
		}
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(CompactStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(ConnectFeedStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}
	
	@Override
	public StringBuilder visit(CreateDataverseStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(CreateFeedPolicyStatement cfps, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(CreateFeedStatement cfs, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(CreateFunctionStatement cfs, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(CreateIndexStatement cis, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(DatasetDecl dd, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(DataverseDecl node, StringBuilder builder) throws CompilationException {
		// Do nothing.  This statement is often present but is outside the query semantics
		return builder;
	}

	@Override
	public StringBuilder visit(DataverseDropStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(DeleteStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(DisconnectFeedStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(DropDatasetStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(FeedDropStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(FeedPolicyDropStatement dfs, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(FieldAccessor node, StringBuilder builder) throws CompilationException {
		builder = nodeWithString("deref", node.getIdent().toString(), builder);
		return node.getExpr().accept(this, builder).append(") ");
	}

	@Override
	public StringBuilder visit(FromClause node, StringBuilder builder) throws CompilationException {
		builder.append("(from ");
		// In keeping with how the Presto parser works, we process more than on 'from' term as an implicit Join.
		builder = makeImplicitJoin(node.getFromTerms(), builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(FromTerm node, StringBuilder builder) throws CompilationException {
		if (node.hasCorrelateClauses())
			for (AbstractBinaryCorrelateClause clause : node.getCorrelateClauses()) {
				builder = clause.accept(this, builder);
			}
		if (node.hasPositionalVariable())
			throw new UnsupportedOperationException("Cannot handle positional variables in FromTerm");
		VariableExpr var = node.getLeftVariable();
		Expression expr = node.getLeftExpression();
		boolean aliased = isDistinctName(var, expr);
		if (aliased)
			// Use 'aliasAs' for tables or subquery-like things, instead of 'as', which is used for columns.
			// This maintains the convention we had for Presto
			// TODO the distinction may or may not be useful ... check what happens on qcert side
			nodeWithString("aliasAs", decodeVariableRef(var.toString()), builder);
		if (expr.getKind() == Kind.VARIABLE_EXPRESSION)
			// Normal visit would use 'ref' but we want 'table' here to conform to our Presto encoding convention
			builder = appendStringNode("table", decodeVariableRef(expr.toString()), builder);
		else 
			builder = expr.accept(this, builder);
		return aliased ? builder.append(") ") : builder;
	}

	@Override
	public StringBuilder visit(FunctionDecl node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(functionDecl ");
		builder = appendString(node.getSignature().getName(), builder).append("(params ");
		for (VarIdentifier id : node.getParamList())
			builder = appendString(decodeVariableRef(id.getValue()), builder);
		builder.append(") ");
		builder = node.getFuncBody().accept(this, builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(FunctionDropStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(GroupbyClause node, StringBuilder builder) throws CompilationException {
		if (node.hasDecorList())
			throw new UnsupportedOperationException("Not supporting DecorList in group by");
		if (node.hasGroupVar())
			throw new UnsupportedOperationException("Not supporting GroupVar in group by");
		if (node.hasHashGroupByHint())
			throw new UnsupportedOperationException("Not supporting HashGroupByHint in group by");
		if (node.hasWithMap())
			throw new UnsupportedOperationException("Not supporting WithMap in group by");
		builder = builder.append("(groupBy ");
    	for (GbyVariableExpressionPair pair : node.getGbyPairList()) {
    		Expression expr = pair.getExpr();
    		VariableExpr var = pair.getVar();
    		if (isDistinctName(var, expr)) {
    			builder = appendStringNode("as", decodeVariableRef(var), builder);
    		}
    		builder = expr.accept(this, builder);
    	}
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(HavingClause node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(having ");
		builder = node.getFilterExpression().accept(this, builder);
		return builder.append(") ");
	}
	
	@Override
	public StringBuilder visit(IfExpr ifexpr, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(IndependentSubquery independentSubquery, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(IndexAccessor node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(index ");
		if (node.isAny())
			builder.append("(any) ");
		else
			builder = node.getIndexExpr().accept(this, builder);
		builder = node.getExpr().accept(this, builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(IndexDropStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(InsertStatement insert, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(JoinClause node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(join (").append(node.getJoinType().toString().toLowerCase()).append(") ");
		builder = node.getRightExpression().accept(this,  builder);
		VariableExpr asVar = node.getRightVariable();
		if (asVar != null)
			builder = appendStringNode("as", decodeVariableRef(asVar), builder);
		builder.append("(on ");
		builder = node.getConditionExpression().accept(this, builder);
		return builder.append(")) ");
	}

	@Override
	public StringBuilder visit(LetClause lc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(LimitClause node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(limit ");
		builder = node.getLimitExpr().accept(this, builder);
		builder = acceptIfPresent(node.getOffset(), builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(ListConstructor node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(list ");
		for (Expression e : node.getExprList()) {
			builder = e.accept(this,  builder);
		}
		return builder.append(") ");

	}

	@Override
	public StringBuilder visit(LiteralExpr node, StringBuilder builder) throws CompilationException {
		Literal lit = node.getValue();
		switch (lit.getLiteralType()) {
		case INTEGER:
		case LONG:
		case FALSE:
		case TRUE:
			return builder.append(lit.getStringValue()).append(" ");
		case STRING:
			return appendString(lit.getStringValue(), builder);
		case DOUBLE:
			return builder.append(String.format("%f", lit.getValue())).append(" ");
		default:
			break;
		}
		throw new UnsupportedOperationException("Not supporting literals of type " + lit.getLiteralType());
	}

	@Override
	public StringBuilder visit(LoadStatement stmtLoad, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(NestClause nestClause, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(NodegroupDecl ngd, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(NodeGroupDropStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(OperatorExpr node, StringBuilder builder) throws CompilationException {
		List<Expression> exprs = node.getExprList();
		List<OperatorType> ops = node.getOpList();
		if (ops.size() == 1 && (exprs.size() == 2 || exprs.size() == 3)) {
			// Consider substitutions based on inferring that the operation involves dates
			Expression alternative = maybeTransform(ops.get(0), exprs);
			if (alternative != null)
				return alternative.accept(this, builder);
			// Otherwise, proceed with the normal case, which involves either 2 or 3 operands.  3 operand cases are limited to
			// 'between' which is handled individually below.  First we look at whether the operator is a negation form.
			boolean negated = false;
			OperatorType op = ops.get(0);
			OperatorType positive = negations.get(op);
			if (positive != null) {
				op = positive;
				negated = true;
				builder = builder.append("(not ");
			}
			if (exprs.size() == 3 && op == OperatorType.BETWEEN) {
				builder = handleBetween(exprs.get(0), exprs.get(1), exprs.get(2), builder);
				return negated ? builder.append(") ") : builder;
			} else if (exprs.size() == 2) {
				builder = processBinaryOperator(op, exprs.get(0), exprs.get(1), builder);
				return negated ? builder.append(") ") : builder;
			} // else 3 exprs but not handled by the case logic; fall through to unsupported
		}
		else if (exprs.size() - ops.size() == 1) {
			// This case is for chains of binary operators under associativity
			assert ops.size() > 0;
			return visit(makeBinary(exprs, ops), builder);
		}
		/* Here we arrive when we have no handling for binary or n-ary (n > 1) cases.  
		 * Note that "unary" operators don't come to this method at all */
		throw new UnsupportedOperationException("Not yet handling operator expressions that aren't binary or 'between'");
	}

	@Override
	public StringBuilder visit(OrderbyClause node, StringBuilder builder) throws CompilationException {
		if (node.getNumFrames() > -1 || node.getNumTuples() > -1 || node.getRangeMap() != null)
			throw new UnsupportedOperationException("Not yet supporting more complex OrderBy clauses");
		List<Expression> orderExprs = node.getOrderbyList();
		List<OrderModifier> orderMods = node.getModifierList();
		assert orderExprs.size() == orderMods.size();
		builder.append("(orderBy ");
		Iterator<OrderModifier> kinds = orderMods.iterator();
		for(Expression expr : orderExprs) {
			String ordering;
			switch (kinds.next()) {
			case ASC:
				ordering = "ascending";
				break;
			case DESC:
				ordering = "descending";
				break;
			default:
				throw new IllegalStateException("Unexpected ordering");
			}
			builder.append("(").append(ordering).append(" ");
			expr.accept(this, builder);
			builder.append(") ");
		}
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(OrderedListTypeDefinition olte, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(Projection node, StringBuilder builder) throws CompilationException {
		Expression expr = node.getExpression();
		String name = node.getName();
		if (name != null && !isDistinctName(name, expr)) {
			name = null;
		}
		if (name != null) 
			appendStringNode("as", name, builder);
		if (expr != null)
			return expr.accept(this, builder);
		if (node.star())
			return builder.append("(all ) ");
		throw new UnsupportedOperationException("Cannot deal with a projection without an expression or a star");
	}

	@Override
	public StringBuilder visit(QuantifiedExpression node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(").append(node.getQuantifier().name().toLowerCase()).append(" ");
		for (QuantifiedPair pair : node.getQuantifiedList()) {
			builder = builder.append("(varIn ");
			builder = appendString(decodeVariableRef(pair.getVarExpr()), builder);
			builder = pair.getExpr().accept(this, builder);
			builder = builder.append(") ");
		}
		builder = builder.append("(satisfies ");
		builder = node.getSatisfiesExpr().accept(this, builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(Query node, StringBuilder builder) throws CompilationException {
		return node.getBody().accept(this, builder);
	}

	@Override
	public StringBuilder visit(RecordConstructor node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(record ");
		for (FieldBinding field : node.getFbList()) {
			builder = builder.append("(field ");
			builder = field.getLeftExpr().accept(this, builder);
			builder = field.getRightExpr().accept(this, builder);
			builder = builder.append(") ");
		}
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(RecordTypeDefinition tre, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(SelectBlock node, StringBuilder builder) throws CompilationException {
		builder.append("(query (select ");
		builder = node.getSelectClause().accept(this, builder);
		builder = builder.append(") "); // for parity with what Presto encoder does.
		builder = acceptIfPresent(node.getFromClause(), builder);
		builder = acceptIfPresent(node.getWhereClause(), builder);
		builder = acceptIfPresent(node.getGroupbyClause(), builder);
		builder = acceptIfPresent(node.getHavingClause(), builder);
		return builder.append(") "); // only one since one was inserted above
	}

	@Override
	public StringBuilder visit(SelectClause node, StringBuilder builder) throws CompilationException {
		if (node.distinct())
			builder.append("(distinct) ");
		if (node.selectElement())
			builder = node.getSelectElement().accept(this, builder);
		if (node.selectRegular())
			builder = node.getSelectRegular().accept(this, builder);
		return builder;
	}

	@Override
	public StringBuilder visit(SelectElement node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(select_expr ");
		builder = node.getExpression().accept(this, builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(SelectExpression node, StringBuilder builder) throws CompilationException {
		builder = node.getSelectSetOperation().accept(this, builder);
		// Because this is a top-level query, but visit(SelectBlock) assumes it might be nested, we have to strip the last paren
		// before processing order by and limit.  We assume without checking that only whitespace follows the last paren.
		int lastParen = builder.lastIndexOf(")");
		builder.delete(lastParen, builder.length());
		builder = acceptIfPresent(node.getOrderbyClause(), builder);
		builder = acceptIfPresent(node.getLimitClause(), builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(SelectRegular node, StringBuilder builder) throws CompilationException {
		for (Projection proj : node.getProjections()) {
			builder = proj.accept(this, builder);
		}
		return builder;
	}

	@Override
	public StringBuilder visit(SelectSetOperation node, StringBuilder builder) throws CompilationException {
		if (!node.hasRightInputs())
			return node.getLeftInput().accept(this, builder);
		SetOperationInput current = node.getLeftInput();
		List<SetOpType> ops = new ArrayList<>();
		List<Boolean> distincts = new ArrayList<>();
		List<SetOperationInput> rights = new ArrayList<>();
		for (SetOperationRight right : node.getRightInputs()) {
			ops.add(right.getSetOpType());
			distincts.add(right.isSetSemantics());
			rights.add(right.getSetOperationRightInput());
		}
		int closeCount = 0;
		while (!ops.isEmpty()) {
			SetOpType op = ops.remove(0);
			boolean distinct = distincts.remove(0);
			SetOperationInput right = rights.remove(0);
			builder = builder.append("(query (").append(op.name().toLowerCase()).append(" ");
			closeCount += 2;
			if (distinct)
				builder.append("(distinct) ");
			builder = current.accept(this, builder);
			current = right;
		}
		builder = current.accept(this, builder);
		for (int i = 0; i < closeCount; i++)
			builder = builder.append(") ");
		return builder;
	}

	@Override
	public StringBuilder visit(SetStatement ss, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(StartFeedStatement sfs, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(StopFeedStatement sfs, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(TypeDecl td, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(TypeDropStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(TypeReferenceExpression tre, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(UnaryExpr node, StringBuilder builder) throws CompilationException {
		String verb = unaryExprMap.get(node.getExprType());
		builder = builder.append("(").append(verb).append(" ");
		builder = node.getExpr().accept(this, builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(UnnestClause node, StringBuilder builder) throws CompilationException {
		builder = builder.append("(unnest (").append(node.getJoinType().name().toLowerCase()).append(") ");
		builder = node.getRightExpression().accept(this, builder);
		builder = appendStringNode("as", decodeVariableRef(node.getRightVariable()), builder);
		VariableExpr posVar = node.getPositionalVariable();
		if (posVar != null) {
			builder = appendStringNode("at", decodeVariableRef(posVar), builder);
		}
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(UnorderedListTypeDefinition ulte, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(UpdateClause del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(UpdateStatement update, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(VariableExpr node, StringBuilder builder) throws CompilationException {
		return appendStringNode("ref", decodeVariableRef(node), builder);
	}

	@Override
	public StringBuilder visit(WhereClause node, StringBuilder builder) throws CompilationException {
    	builder.append("(where ");
    	builder = node.getWhereExpr().accept(this, builder);
    	return builder.append(") ");
	}

	@Override
	public StringBuilder visit(WriteStatement ws, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	private StringBuilder acceptIfPresent(ILangExpression node, StringBuilder builder) throws CompilationException {
		if (node != null)
			builder = node.accept(this, builder);
		return builder;
	}

	/** Append a string with a trailing blank */
	private StringBuilder appendString(String s, StringBuilder builder) {
		return builder.append("\"").append(s).append("\" ");
	}

	/**
	 * Given a node name and a string argument, append a String-style S-expression node
	 * @param node the node name
	 * @param arg the String argument
	 * @param builder the StringBuilder to receive the append
	 */
	private StringBuilder appendStringNode(String node, String arg, StringBuilder builder) {
		return builder.append(String.format("(%s \"%s\" ) ", node, arg));
	}

	/**
	 * Reverse the asterixDB practice of prefixing variable references with '$'
	 * @param name the name to decode
	 * @return the decoded name
	 */
	private String decodeVariableRef(String name) {
		return (name.charAt(0) == '$') ? name.substring(1) : name;
	}

	/**
	 * Wrap the other decodeVariableRef for convenience in the common case
	 * @param expr a VariableExpr whose identifier is to be decoded
	 * @return the decoded name
	 */
	private String decodeVariableRef(VariableExpr expr) {
		return decodeVariableRef(expr.toString());
	}
	
	/**
	 * Handling for the 'between' expression
	 * @param expr the expression being tested
	 * @param limit1 the first limit
	 * @param limit2 the second limit
	 * @param builder the builder
	 * @return the builder
	 * @throws CompilationException
	 */
	private StringBuilder handleBetween(Expression expr, Expression limit1, Expression limit2, StringBuilder builder) throws CompilationException {
		builder = builder.append("(isBetween ");
		builder = expr.accept(this, builder);
		builder = limit1.accept(this, builder);
		builder = limit2.accept(this, builder);
		return builder.append(") ");
	}

	/**
	 * Special handling for date literals appearing as calls to the function "date"
	 * TODO in SQL++ the date function really is a function operating on strings in general, not just literals.  We should
	 *   be processing this as a general conversion from String to date.
	 * @param arg the argument to the apparent "date" function
	 * @param builder the builder
	 * @return the builder
	 * @throws CompilationException
	 */
	private StringBuilder handleDate(Expression arg, StringBuilder builder) throws CompilationException {
		if (arg.getKind() != Kind.LITERAL_EXPRESSION)
			throw new UnsupportedOperationException("Not handling date constructors on non-literals");
		builder = builder.append("(literal \"date\" ");
		builder = arg.accept(this, builder);
		return builder.append(")");
	}

	/**
	 * Special handling for duration literals (confusingly called 'interval literals' by SQL but appearing as calls to the
	 *  function "duration"
	 * TODO in SQL++ the duration function really is a function operating on strings in general, not just literals.  We should
	 *   be processing this as a general conversion from String to duration
	 * @param arg the argument to the apparent "duration" function
	 * @param builder the builder
	 * @return the builder
	 * @throws CompilationException
	 */
	private StringBuilder handleDuration(Expression arg, StringBuilder builder) throws CompilationException {
		if (arg.getKind() != Kind.LITERAL_EXPRESSION)
			throw new UnsupportedOperationException("Not handling duration constructors on non-literals");
		String lit = ((LiteralExpr) arg).getValue().getStringValue();
		char first = lit.charAt(0);
		char last = lit.charAt(lit.length() - 1);
		if (first != 'P' || last != 'D' && last != 'M' && last != 'Y')
			throw new UnsupportedOperationException("Ill-formed duration literal: " + lit);
		String tag = last == 'D' ? "(day)" : last == 'M' ? "(month)" : "(year)";  
		builder = builder.append("(interval ");
		builder = appendString(lit.substring(1, lit.length() - 1), builder);
		return builder.append(tag).append(")");
	}

	/**
	 * Special handling for functions get_year, get_month, and get_day which are extract expressions
	 * @param unit the unit being extracted (year, month, or day)
	 * @param expression the expression from which it is being extracted
	 * @param builder the builder
	 * @return the builder
	 * @throws CompilationException 
	 */
	private StringBuilder handleExtract(String unit, Expression expression, StringBuilder builder) throws CompilationException {
		builder = builder.append("(extract (").append(unit).append(") ");
		builder = expression.accept(this, builder);
		return builder.append(") ");
	}

	/**
	 * Handle the case of a "not" appearing as a function call
	 * @param expression the expression that is the argument to the apparent function call
	 * @param builder the builder
	 * @return the builder
	 * @throws CompilationException 
	 */
	private StringBuilder handleNot(Expression expression, StringBuilder builder) throws CompilationException {
		builder = builder.append("(not ");
		builder = expression.accept(this, builder);
		return builder.append(") ");
	}

	/** Heuristic type inference: determine if an Expression has type 'date'.
	 * This should not produce false positives.  It uses heuristics to find obvious cases only.
	 */
	private boolean isDate(Expression maybeDate) {
		/* Look for functions with method name date_plus or date_minus since these produce dates (and resulted from
		 *  heuristic type inference on children).  Also, look for functions with method name "date" since that is how
		 *  a date literal is expressed after lexical fixups and parsing by AsterixDB SQL++.
		 */
		if (maybeDate.getKind() == Kind.CALL_EXPRESSION)
			switch(((CallExpr) maybeDate).getFunctionSignature().getName()) {
			case "date_plus":
			case "date_minus":
			case "date":
				return true;
			}
		/* if the date name heuristic is enabled and the expression is a ref or deref of a name, apply that heuristic */
		if (useDateNameHeuristic) {
			String name = null;
			switch (maybeDate.getKind()) {
			case FIELD_ACCESSOR_EXPRESSION:
				name = ((FieldAccessor) maybeDate).getIdent().getValue();
				break;
			case VARIABLE_EXPRESSION:
				name = decodeVariableRef(((VariableExpr) maybeDate));
				break;
			default:
				break;
			}
			if (name != null)
				return name.endsWith("date");
		}
		return false;
	}

	/** Heuristic type inference: determine if an Expression has type 'date interval' (or "duration")
	 * This should not produce false positives.  It uses heuristics to find obvious cases only.
	 */
	private boolean isDateInterval(Expression maybeInterval) {
		/* Look for function call with the name "duration" since this is how durations are expressed after lexical
		 * fixup and parsing by AsterixDB SQL++
		 */
		return maybeInterval.getKind() == Kind.CALL_EXPRESSION && ((CallExpr) maybeInterval).getFunctionSignature().getName().equals("duration");
	}

	/**
	 * Work around the asterixDB convention of including an explicit name for every selected column, even when that is the
	 *   same as the name of column. 
	 * @param name the name assigned to the column
	 * @param expr the Expression for the column, which might be a variable reference and possible to the same name, though
	 *   prefixed with a $ as per their convention
	 * @return true iff the name is distinct (that is, requires explicit handling in an "as" clause, otherwise such handling can be
	 *   omitted to match presto conventions)
	 */
	private boolean isDistinctName(String name, Expression expr) {
		if (expr.getKind() == Kind.VARIABLE_EXPRESSION) {
			VariableExpr var = (VariableExpr) expr;
			if (var.getIsNewVar())
				return true;
			VarIdentifier id = var.getVar();
			if (id.namedValueAccess())
				return true;
			String exprName = id.getValue();
			if (exprName.length() == name.length() + 1 && decodeVariableRef(exprName).equals(name))
				return false;
		}
		return true;
	}

	/**
	 * Work around the asterixDB convention of including an explicit name for every selected-from table, even when that is the
	 *   same as the name of table (dual of similar method for columns) 
	 * @param var the name for the table as a VariableExpr
	 * @param expr the Expression for the table, which might be a variable reference and possible to the same name, though
	 *   prefixed with a $ as per their convention
	 * @return true iff the name is distinct (that is, requires explicit handling in an "as" clause, otherwise such handling can be
	 *   omitted to match presto conventions)
	 */
	private boolean isDistinctName(VariableExpr name, Expression expr) {
		VarIdentifier id = name.getVar();
		if (id.namedValueAccess())
			return true;
		String varName = decodeVariableRef(id.getValue());
		return isDistinctName(varName, expr);
	}

	/**
	 * Check whether an expression (assumed non-null) is the true literal
	 * @param expr the expression
	 * @return true iff the expression is the true literal
	 */
	private boolean isTrueLiteral(Expression expr) {
		if (expr.getKind() == Kind.LITERAL_EXPRESSION) {
			Literal lit = ((LiteralExpr) expr).getValue();
			return lit == TrueLiteral.INSTANCE;
		}
		return false;
	}

	/**
	 * Subroutine of the visitor for OperatorExpr to handle chains longer than one operator and two operands.
	 * In keeping with how things work in Presto, the result is left associative
	 * @param exprs the expressions
	 * @param ops the ops
	 * @return
	 */
	private OperatorExpr makeBinary(List<Expression> exprs, List<OperatorType> ops) {
		assert exprs.size() > 2;
		exprs = new ArrayList<>(exprs);
		ops = new ArrayList<>(ops);
		Expression lastExpr = exprs.remove(exprs.size() - 1);
		OperatorType lastOp = ops.remove(ops.size() - 1);
		OperatorExpr remainder = new OperatorExpr(exprs, Collections.emptyList(), ops, false);
		exprs = Arrays.asList(remainder, lastExpr);
		return new OperatorExpr(exprs, Collections.emptyList(), Collections.singletonList(lastOp), false);
	}

	/**
	 * Subroutine of the FromClause visitor to build a left-associative recursive nest of implicit joins from the
	 *   list of FromTerms
	 * @param terms the FromTerms
	 * @param builder the StringBuilder
	 * @return a StringBuilder appropriately augmented
	 */
	private StringBuilder makeImplicitJoin(List<FromTerm> terms, StringBuilder builder) throws CompilationException {
		if (terms.size() == 1)
			return terms.get(0).accept(this, builder);
		terms = new ArrayList<>(terms);
		FromTerm last = terms.remove(terms.size() - 1);
		builder = builder.append("(join ");
		builder = makeImplicitJoin(terms, builder);
		builder = last.accept(this, builder);
		return builder.append(") ");
	}
	
	/** Test whether a node is an operator node and call the main date transformation analysis if it is */
	private Expression maybeTransform(Expression expr) {
		if (expr.getKind() == Kind.OP_EXPRESSION) {
			OperatorExpr opExpr = (OperatorExpr) expr;
			List<Expression> exprs = opExpr.getExprList();
			List<OperatorType> ops = opExpr.getOpList();
			if (ops.size() == 1) {
				// TODO we might need to reorganize the code a bit to make sure we catch other cases
				Expression maybe = maybeTransform(ops.get(0), exprs);
				if (maybe != null)
					return maybe;
			}
		}
		return expr;
	}

	/** Selectively turn an operator node into a function call if it operates on dates.  Returns a new node or null if
	 *  no safe transformation is available. */
	private Expression maybeTransform(OperatorType operator, List<Expression> operands) {
		String name;
		boolean arithmetic = false;
		switch (operator) {
		case BETWEEN:
			name = "date_between";
			break;
		case NOT_BETWEEN:
			throw new UnsupportedOperationException("A 'not between' predicate may need date transformation but it is not yet implemented");
		case GE:
			name = "date_ge";
			break;
		case GT:
			name = "date_gt";
			break;
		case LE:
			name = "date_le";
			break;
		case LT:
			name = "date_lt";
			break;
		case MINUS:
			name = "date_minus";
			arithmetic = true;
			break;
		case NEQ:
			name = "date_ne";
			break;
		case PLUS:
			name = "date_plus";
			arithmetic = true;
			break;
		default:
			return null;
		}
		if (arithmetic) {
			assert operands.size() == 2;
			Expression left = maybeTransform(operands.get(0));
			Expression right = maybeTransform(operands.get(1));
			if (isDate(left) && isDateInterval(right))
				return new CallExpr(new FunctionSignature(null, name, 2), Arrays.asList(left, right));
		} else {
			List<Expression> transformed = new ArrayList<>();
			boolean date = false;
			for (Expression operand : operands) {
				Expression trans = maybeTransform(operand);
				date |= isDate(trans);
				transformed.add(trans);
			}
			if (date)
				return new CallExpr(new FunctionSignature(null, name, transformed.size()), transformed);
		}
		return null;
	}

	/** Like appendStringNode but leaves the node open for more things to be added (see appendStringNode) */
	private StringBuilder nodeWithString(String node, String arg, StringBuilder builder) {
		return builder.append(String.format("(%s \"%s\" ", node, arg));
	}

	/**
	 * Convenient error thrower for identifying unimplemented things
	 * @param o an object anonymously subclassed by the throwing method, allowing the method to be identified
	 * @return a StringBuilder nominally, for composition, but never actually returns
	 */
	private StringBuilder notImplemented(Object o) {
		Method method = o.getClass().getEnclosingMethod();
		Class<?> type = method.getParameterTypes()[0];
		throw new UnsupportedOperationException("Visitor not implemented for " + type.getSimpleName());
	}

	/**
	 * Process a binary operation whose verb has been identified and that can be handled in a standard way.
	 * @param operator the operator
	 * @param operand1 the first operand		
	 * @param operand2 the second operand	
	 * @param builder the StringBuilder
	 * @return the StringBuilder (or a behaviorally equivalent one) augmented with this expression
	 * @throws CompilationException
	 */
	private StringBuilder processBinaryOperator(OperatorType operator, Expression operand1, Expression operand2, StringBuilder builder) 
			throws CompilationException {
		if (operator == OperatorType.CONCAT) {
			// Special case: turns into function
			builder = builder.append("(function ");
			builder = appendString("concat", builder);
		} else {
			String verb = opNameMap.get(operator);
			if (verb == null)
				throw new UnsupportedOperationException("No support for binary operator " + operator);
			builder.append("(").append(verb).append(" ");
		}
		builder = operand1.accept(this, builder);
		builder = operand2.accept(this, builder);
		return builder.append(") ");
	}
}
