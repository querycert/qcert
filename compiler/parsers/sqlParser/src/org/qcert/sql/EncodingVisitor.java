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
package org.qcert.sql;

import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import com.facebook.presto.sql.tree.*;
import com.facebook.presto.sql.tree.IntervalLiteral.Sign;
import com.facebook.presto.sql.tree.SortItem.NullOrdering;

/**
 * A presto AST visitor that encodes the tree as an S-expression
 */
public class EncodingVisitor extends DefaultTraversalVisitor<StringBuilder, StringBuilder> {
	/** Set this to suppress the limit clause
	 */
	private static final boolean SUPPRESS_LIMIT = true;

	/** Set this to suppress window designations on function calls
	 */
	private static final boolean SUPPRESS_WINDOWS = Boolean.getBoolean("SUPPRESS_WINDOWS");
	
	/** Set this to suppress all 'with ... as' clauses
	 */
	private static final boolean SUPPRESS_WITH = Boolean.getBoolean("SUPPRESS_WITH");
	
	/** Set this to suppress all 'orderBy' directives
	 */
	private static final boolean SUPPRESS_ORDERBY = Boolean.getBoolean("SUPPRESS_ORDERBY");

	/** Indicates whether field names ending in "date" are assumed to be dates in the schema */
	private boolean useDateNameHeuristic;
	
	public EncodingVisitor(boolean useDateNameHeuristic) {
		this.useDateNameHeuristic = useDateNameHeuristic;
	}
	
	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitFrameBound(com.facebook.presto.sql.tree.FrameBound, java.lang.Object)
	 */
	@Override
	public StringBuilder visitFrameBound(FrameBound node, StringBuilder builder) {
		builder.append("(frameBound (").append(node.getType().name().toLowerCase()).append(") ");
		if (node.getValue().isPresent())
			process(node.getValue().get(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitResetSession(com.facebook.presto.sql.tree.ResetSession, java.lang.Object)
	 */
	@Override
	public StringBuilder visitResetSession(ResetSession node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitWindow(com.facebook.presto.sql.tree.Window, java.lang.Object)
	 */
	@Override
	public StringBuilder visitWindow(Window node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitWindowFrame(com.facebook.presto.sql.tree.WindowFrame, java.lang.Object)
	 */
	@Override
	public StringBuilder visitWindowFrame(WindowFrame node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitAddColumn(com.facebook.presto.sql.tree.AddColumn, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitAddColumn(AddColumn node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitAliasedRelation(com.facebook.presto.sql.tree.AliasedRelation, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitAliasedRelation(AliasedRelation node, StringBuilder builder) {
		nodeWithString("aliasAs", node.getAlias(), builder);
		process(node.getRelation(), builder);
		if (node.getColumnNames() != null && !node.getColumnNames().isEmpty()) {
			builder.append("(columns ");
			appendStrings(node.getColumnNames(), builder);
			builder.append(")");
		}
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitAllColumns(com.facebook.presto.sql.tree.AllColumns, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitAllColumns(AllColumns node, StringBuilder builder) {
		if (node.getPrefix().isPresent())
			return appendStringNode("all", node.getPrefix().get().toString(), builder);
		else
			return builder.append("(all ) ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitArithmeticBinary(com.facebook.presto.sql.tree.ArithmeticBinaryExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitArithmeticBinary(ArithmeticBinaryExpression node, StringBuilder builder) {
		Expression transformed = maybeTransform(node);
		if (transformed != node)
			return process(transformed, builder);
		builder.append("(").append(node.getType().toString().toLowerCase()).append(" ");
		process(node.getLeft(), builder);
		process(node.getRight(), builder);
		return builder.append(") ");
	}
	
	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitArithmeticUnary(com.facebook.presto.sql.tree.ArithmeticUnaryExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitArithmeticUnary(ArithmeticUnaryExpression node, StringBuilder builder) {
		builder.append("(").append(node.getSign().toString().toLowerCase()).append(" ");
		process(node.getValue(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitArrayConstructor(com.facebook.presto.sql.tree.ArrayConstructor, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitArrayConstructor(ArrayConstructor node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitAtTimeZone(com.facebook.presto.sql.tree.AtTimeZone, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitAtTimeZone(AtTimeZone node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitBetweenPredicate(com.facebook.presto.sql.tree.BetweenPredicate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitBetweenPredicate(BetweenPredicate node, StringBuilder builder) {
		Expression transformed = maybeTransform(node);
		if (transformed != node)
			return process(transformed, builder);
		builder.append("(isBetween ");
		process(node.getValue(), builder);
		process(node.getMin(), builder);
		process(node.getMax(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitBinaryLiteral(com.facebook.presto.sql.tree.BinaryLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitBinaryLiteral(BinaryLiteral node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitBooleanLiteral(com.facebook.presto.sql.tree.BooleanLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitBooleanLiteral(BooleanLiteral node,	StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCall(com.facebook.presto.sql.tree.Call, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCall(Call node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCallArgument(com.facebook.presto.sql.tree.CallArgument, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCallArgument(CallArgument node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitCast(com.facebook.presto.sql.tree.Cast, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCast(Cast node, StringBuilder builder) {
		builder.append("(cast ");
		appendStringNode("as", node.getType(), builder);
		process(node.getExpression(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCharLiteral(com.facebook.presto.sql.tree.CharLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCharLiteral(CharLiteral node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitCoalesceExpression(com.facebook.presto.sql.tree.CoalesceExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCoalesceExpression(CoalesceExpression node,	StringBuilder builder) {
		builder.append("(coalesce ");
		for (Expression e : node.getOperands())
			process(e, builder);
		return builder.append(") ");
	}

	@Override
	protected StringBuilder visitColumnDefinition(ColumnDefinition node, StringBuilder builder) {
		nodeWithString("column", node.getName(), builder);
		return appendString(node.getType(), builder).append(")");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCommit(com.facebook.presto.sql.tree.Commit, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCommit(Commit node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitComparisonExpression(com.facebook.presto.sql.tree.ComparisonExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitComparisonExpression(ComparisonExpression node, StringBuilder builder) {
		Expression transformed = maybeTransform(node);
		if (transformed != node)
			return process(transformed, builder);
		builder.append("(").append(node.getType().toString().toLowerCase()).append(" ");
		process(node.getLeft(), builder);
		process(node.getRight(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCreateTable(com.facebook.presto.sql.tree.CreateTable, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCreateTable(CreateTable node, StringBuilder builder) {
		nodeWithString("createTable", node.getName().toString(), builder);
		if (node.isNotExists())
			builder.append("(notExists) ");
		if (!node.getElements().isEmpty())
			for (TableElement element : node.getElements()) {
				process(element, builder);
			}
		addProperties(node.getProperties(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitCreateTableAsSelect(com.facebook.presto.sql.tree.CreateTableAsSelect, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCreateTableAsSelect(CreateTableAsSelect node, StringBuilder builder) {
		nodeWithString("createTableAsSelect", node.getName().toString(), builder);
		if (node.isNotExists())
			builder.append("(notExists) ");
		if (node.isWithData())
			builder.append("(withData) ");
		process(node.getQuery(), builder);
		addProperties(node.getProperties(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCreateView(com.facebook.presto.sql.tree.CreateView, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCreateView(CreateView node, StringBuilder builder) {
		nodeWithString("createView", node.getName().toString(), builder);
		return process(node.getQuery(), builder).append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCube(com.facebook.presto.sql.tree.Cube, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCube(Cube node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitCurrentTime(com.facebook.presto.sql.tree.CurrentTime, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitCurrentTime(CurrentTime node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitDeallocate(com.facebook.presto.sql.tree.Deallocate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitDeallocate(Deallocate node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitDecimalLiteral(com.facebook.presto.sql.tree.DecimalLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitDecimalLiteral(DecimalLiteral node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitDelete(com.facebook.presto.sql.tree.Delete, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitDelete(Delete node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitDereferenceExpression(com.facebook.presto.sql.tree.DereferenceExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitDereferenceExpression(DereferenceExpression node, StringBuilder builder) {
		nodeWithString("deref", node.getFieldName(), builder);
		return process(node.getBase(), builder).append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitDoubleLiteral(com.facebook.presto.sql.tree.DoubleLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitDoubleLiteral(DoubleLiteral node, StringBuilder builder) {
		return builder.append(String.format("%f", node.getValue())).append(" ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitDropTable(com.facebook.presto.sql.tree.DropTable, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitDropTable(DropTable node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitDropView(com.facebook.presto.sql.tree.DropView, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitDropView(DropView node, StringBuilder builder) {
		return appendStringNode("dropView", node.getName().toString(), builder);
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitExcept(com.facebook.presto.sql.tree.Except, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitExcept(Except node, StringBuilder builder) {
		return processSetOperation(node, builder, Except.class, "except");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitExecute(com.facebook.presto.sql.tree.Execute, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitExecute(Execute node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitExists(com.facebook.presto.sql.tree.ExistsPredicate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitExists(ExistsPredicate node, StringBuilder builder) {
		builder.append("(exists ");
		process(node.getSubquery(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitExplain(com.facebook.presto.sql.tree.Explain, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitExplain(Explain node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitExplainOption(com.facebook.presto.sql.tree.ExplainOption, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitExplainOption(ExplainOption node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitExpression(com.facebook.presto.sql.tree.Expression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitExpression(Expression node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitExtract(com.facebook.presto.sql.tree.Extract, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitExtract(Extract node, StringBuilder builder) {
		builder.append("(extract (").append(node.getField().name().toLowerCase()).append(") ");
		process(node.getExpression(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitFieldReference(com.facebook.presto.sql.tree.FieldReference, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitFieldReference(FieldReference node,	StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitFunctionCall(com.facebook.presto.sql.tree.FunctionCall, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitFunctionCall(FunctionCall node, StringBuilder builder) {
		builder.append("(function ");
		if (node.getWindow().isPresent())
			processWindow(node.getWindow().get(), builder);
		appendString(node.getName().toString(), builder);
		for (Expression arg : node.getArguments())
			process(arg, builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitGenericLiteral(com.facebook.presto.sql.tree.GenericLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitGenericLiteral(GenericLiteral node, StringBuilder builder) {
		builder.append("(literal ");
		appendStrings(builder, node.getType(), node.getValue());
		return builder.append(")");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitGrant(com.facebook.presto.sql.tree.Grant, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitGrant(Grant node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitGroupBy(com.facebook.presto.sql.tree.GroupBy, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitGroupBy(GroupBy node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitGroupingElement(com.facebook.presto.sql.tree.GroupingElement, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitGroupingElement(GroupingElement node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitGroupingSets(com.facebook.presto.sql.tree.GroupingSets, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitGroupingSets(GroupingSets node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitIfExpression(com.facebook.presto.sql.tree.IfExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitIfExpression(IfExpression node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitInListExpression(com.facebook.presto.sql.tree.InListExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitInListExpression(InListExpression node, StringBuilder builder) {
		builder.append("(list ");
		for (Expression e : node.getValues()) {
			process(e, builder);
		}
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitInPredicate(com.facebook.presto.sql.tree.InPredicate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitInPredicate(InPredicate node, StringBuilder builder) {
		builder.append("(isIn ");
		process(node.getValue(), builder);
		process(node.getValueList(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitInsert(com.facebook.presto.sql.tree.Insert, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitInsert(Insert node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitIntersect(com.facebook.presto.sql.tree.Intersect, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitIntersect(Intersect node, StringBuilder builder) {
		return processSetOperation(node, builder, Union.class, "intersect");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitIntervalLiteral(com.facebook.presto.sql.tree.IntervalLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitIntervalLiteral(IntervalLiteral node, StringBuilder builder) {
		nodeWithString("interval", node.getValue(), builder);
		if (node.getSign() == Sign.NEGATIVE) {
			builder.append("(negative) ");
		}
		builder.append("(").append(node.getStartField().name().toLowerCase()).append(")");
		if (node.getEndField().isPresent())
			builder.append(" (").append(node.getEndField().get().name().toLowerCase()).append(")");
		return builder.append(")");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitIsNotNullPredicate(com.facebook.presto.sql.tree.IsNotNullPredicate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitIsNotNullPredicate(IsNotNullPredicate node,
			StringBuilder builder) {
		builder.append("(notNull ");
		process(node.getValue(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitIsNullPredicate(com.facebook.presto.sql.tree.IsNullPredicate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitIsNullPredicate(IsNullPredicate node, StringBuilder builder) {
		builder.append("(isNull ");
		process(node.getValue(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitIsolationLevel(com.facebook.presto.sql.tree.Isolation, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitIsolationLevel(Isolation node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitJoin(com.facebook.presto.sql.tree.Join, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitJoin(Join node, StringBuilder builder) {
		builder.append("(join ");
		Join.Type type = node.getType();
		if (type != Join.Type.IMPLICIT)
			builder.append("(").append(type.name().toLowerCase()).append(")");
		if (node.getCriteria().isPresent()) {
			JoinCriteria criteria = node.getCriteria().get();
			if (criteria instanceof NaturalJoin) {
				builder.append("(natural) ");
			} else if (criteria instanceof JoinOn) {
				builder.append("(on ");
				process(((JoinOn) criteria).getExpression(), builder);
				builder.append(") ");
			} else if (node.getCriteria().get() instanceof JoinUsing) {
				builder.append("(using ");
				appendStrings(((JoinUsing) criteria).getColumns(), builder);
				builder.append(") ");
			} else
				throw new IllegalStateException("Unexpected Join criteria subclass " +
						node.getCriteria().get().getClass().getName());
		}
		process(node.getLeft(), builder);
		process(node.getRight(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitLambdaExpression(com.facebook.presto.sql.tree.LambdaExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitLambdaExpression(LambdaExpression node,
			StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitLikePredicate(com.facebook.presto.sql.tree.LikePredicate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitLikePredicate(LikePredicate node, StringBuilder builder) {
		builder.append("(like ");
		process(node.getValue(), builder);
		process(node.getPattern(), builder);
		Expression escape = node.getEscape();
		if (escape != null) {
			builder.append("(escape ");
			process(escape, builder);
			builder.append(")");
		}
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitLiteral(com.facebook.presto.sql.tree.Literal, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitLiteral(Literal node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitLogicalBinaryExpression(com.facebook.presto.sql.tree.LogicalBinaryExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitLogicalBinaryExpression(LogicalBinaryExpression node, StringBuilder builder) {
		builder.append("(").append(node.getType().toString().toLowerCase()).append(" ");
		process(node.getLeft(), builder);
		process(node.getRight(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitLongLiteral(com.facebook.presto.sql.tree.LongLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitLongLiteral(LongLiteral node, StringBuilder builder) {
		return builder.append(String.valueOf(node.getValue())).append(" ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitNode(com.facebook.presto.sql.tree.Node, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitNode(Node node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitNotExpression(com.facebook.presto.sql.tree.NotExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitNotExpression(NotExpression node, StringBuilder builder) {
		builder.append("(not ");
		process(node.getValue(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitNullIfExpression(com.facebook.presto.sql.tree.NullIfExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitNullIfExpression(NullIfExpression node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitNullLiteral(com.facebook.presto.sql.tree.NullLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitNullLiteral(NullLiteral node, StringBuilder builder) {
		return builder.append("(dunit)");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitPrepare(com.facebook.presto.sql.tree.Prepare, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitPrepare(Prepare node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitQualifiedNameReference(com.facebook.presto.sql.tree.QualifiedNameReference, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitQualifiedNameReference(QualifiedNameReference node, StringBuilder builder) {
		return appendStringNode("ref", node.getName().toString(), builder);
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitQuery(com.facebook.presto.sql.tree.Query, java.lang.Object)
	 */
	@SuppressWarnings("unused")
	protected StringBuilder visitQuery(Query node, StringBuilder builder) {
		builder.append("(query ");

		if (node.getWith().isPresent())
			process(node.getWith().get(), builder);

		process(node.getQueryBody(), builder);

		if (node.getLimit().isPresent() && !SUPPRESS_LIMIT)
			appendStringNode("limit", node.getLimit().get(), builder);

		processOrderBy(node.getOrderBy(), builder);
		
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitQueryBody(com.facebook.presto.sql.tree.QueryBody, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitQueryBody(QueryBody node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitQuerySpecification(com.facebook.presto.sql.tree.QuerySpecification, java.lang.Object)
	 */
	@SuppressWarnings("unused")
	@Override
	protected StringBuilder visitQuerySpecification(QuerySpecification node, StringBuilder builder) {
		process(node.getSelect(), builder);
		
        if (node.getFrom().isPresent()) {
        	builder.append("(from ");
            process(node.getFrom().get(), builder);
            builder.append(") ");
        }

        if (node.getWhere().isPresent()) {
        	builder.append("(where ");
            process(node.getWhere().get(), builder );
            builder.append(") ");
        }

        if (node.getGroupBy().isPresent()) {
        	builder.append("(groupBy ");
            if (node.getGroupBy().get().isDistinct()) {
                builder.append("(distinct) ");
            }
            for (GroupingElement groupingElement : node.getGroupBy().get().getGroupingElements()) {
                if (groupingElement instanceof SimpleGroupBy) {
                    for (Expression column : ((SimpleGroupBy) groupingElement).getColumnExpressions()) {
                        process(column, builder );
                    }
                }
                else if (groupingElement instanceof Rollup) {
                	builder.append("(rollup ");
                	for (QualifiedName colName : ((Rollup) groupingElement).getColumns()) {
                		appendString(colName.toString(), builder);
                	}
                	builder.append(")");
                } else
                    throw new UnsupportedOperationException("Only simple groupBy and rollup are supported");
            }
            builder.append(") ");
        }

        if (node.getHaving().isPresent()) {
        	builder.append("(having ");
            process(node.getHaving().get(), builder );
            builder.append(") ");
        }

        processOrderBy(node.getOrderBy(), builder);

        if (node.getLimit().isPresent() && !SUPPRESS_LIMIT) {
            appendStringNode("limit", node.getLimit().get(), builder);
        }

        return null;
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitRelation(com.facebook.presto.sql.tree.Relation, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitRelation(Relation node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitRenameColumn(com.facebook.presto.sql.tree.RenameColumn, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitRenameColumn(RenameColumn node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitRenameTable(com.facebook.presto.sql.tree.RenameTable, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitRenameTable(RenameTable node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitRevoke(com.facebook.presto.sql.tree.Revoke, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitRevoke(Revoke node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitRollback(com.facebook.presto.sql.tree.Rollback, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitRollback(Rollback node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitRollup(com.facebook.presto.sql.tree.Rollup, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitRollup(Rollup node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitRow(com.facebook.presto.sql.tree.Row, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitRow(Row node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSampledRelation(com.facebook.presto.sql.tree.SampledRelation, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSampledRelation(SampledRelation node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSearchedCaseExpression(com.facebook.presto.sql.tree.SearchedCaseExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSearchedCaseExpression(SearchedCaseExpression node, StringBuilder builder) {
		builder.append("(cases ");
		return addCaseBody(node.getWhenClauses(), node.getDefaultValue(), builder);
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSelect(com.facebook.presto.sql.tree.Select, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSelect(Select node, StringBuilder builder) {
		builder.append("(select ");
		super.visitSelect(node, builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitSelectItem(com.facebook.presto.sql.tree.SelectItem, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSelectItem(SelectItem node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSetOperation(com.facebook.presto.sql.tree.SetOperation, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSetOperation(SetOperation node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitSetSession(com.facebook.presto.sql.tree.SetSession, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSetSession(SetSession node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowCatalogs(com.facebook.presto.sql.tree.ShowCatalogs, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowCatalogs(ShowCatalogs node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowColumns(com.facebook.presto.sql.tree.ShowColumns, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowColumns(ShowColumns node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowCreate(com.facebook.presto.sql.tree.ShowCreate, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowCreate(ShowCreate node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowFunctions(com.facebook.presto.sql.tree.ShowFunctions, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowFunctions(ShowFunctions node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowPartitions(com.facebook.presto.sql.tree.ShowPartitions, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowPartitions(ShowPartitions node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowSchemas(com.facebook.presto.sql.tree.ShowSchemas, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowSchemas(ShowSchemas node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowSession(com.facebook.presto.sql.tree.ShowSession, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowSession(ShowSession node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitShowTables(com.facebook.presto.sql.tree.ShowTables, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitShowTables(ShowTables node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSimpleCaseExpression(com.facebook.presto.sql.tree.SimpleCaseExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSimpleCaseExpression(SimpleCaseExpression node, StringBuilder builder) {
		builder.append("(cases (operand ");
		process(node.getOperand(), builder).append(") ");
		return addCaseBody(node.getWhenClauses(), node.getDefaultValue(), builder);
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSimpleGroupBy(com.facebook.presto.sql.tree.SimpleGroupBy, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSimpleGroupBy(SimpleGroupBy arg0, StringBuilder arg1) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSingleColumn(com.facebook.presto.sql.tree.SingleColumn, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSingleColumn(SingleColumn node, StringBuilder builder) {
		if (node.getAlias().isPresent())
			appendStringNode("as", node.getAlias().get(), builder);
		return process(node.getExpression(), builder);
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSortItem(com.facebook.presto.sql.tree.SortItem, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSortItem(SortItem node, StringBuilder builder) {
		builder.append("(").append(node.getOrdering().name().toLowerCase()).append(" ");
		NullOrdering nullOrdering = node.getNullOrdering();
		if (nullOrdering != NullOrdering.UNDEFINED)
			builder.append("(").append(nullOrdering.name().toLowerCase()).append(") ");
		process(node.getSortKey(), builder);
		return builder.append(") ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitStartTransaction(com.facebook.presto.sql.tree.StartTransaction, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitStartTransaction(StartTransaction node,	StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitStatement(com.facebook.presto.sql.tree.Statement, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitStatement(Statement node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitStringLiteral(com.facebook.presto.sql.tree.StringLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitStringLiteral(StringLiteral node, StringBuilder builder) {
		return appendString(node.getValue(), builder);
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitSubscriptExpression(com.facebook.presto.sql.tree.SubscriptExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSubscriptExpression(SubscriptExpression node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitSymbolReference(com.facebook.presto.sql.tree.SymbolReference, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitSymbolReference(SymbolReference node,
			StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitTable(com.facebook.presto.sql.tree.Table, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitTable(Table node, StringBuilder builder) {
		return appendStringNode("table", node.getName().toString(), builder);
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitTableElement(com.facebook.presto.sql.tree.TableElement, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitTableElement(TableElement node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitTimeLiteral(com.facebook.presto.sql.tree.TimeLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitTimeLiteral(TimeLiteral node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitTimestampLiteral(com.facebook.presto.sql.tree.TimestampLiteral, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitTimestampLiteral(TimestampLiteral node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitTransactionAccessMode(com.facebook.presto.sql.tree.TransactionAccessMode, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitTransactionAccessMode(TransactionAccessMode node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitTransactionMode(com.facebook.presto.sql.tree.TransactionMode, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitTransactionMode(TransactionMode node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitTryExpression(com.facebook.presto.sql.tree.TryExpression, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitTryExpression(TryExpression node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitUnion(com.facebook.presto.sql.tree.Union, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitUnion(Union node, StringBuilder builder) {
		return processSetOperation(node, builder, Union.class, "union");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitUnnest(com.facebook.presto.sql.tree.Unnest, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitUnnest(Unnest node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.AstVisitor#visitUse(com.facebook.presto.sql.tree.Use, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitUse(Use node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitValues(com.facebook.presto.sql.tree.Values, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitValues(Values node, StringBuilder builder) {
		return notImplemented(new Object(){});
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitWhenClause(com.facebook.presto.sql.tree.WhenClause, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitWhenClause(WhenClause node, StringBuilder builder) {
		builder.append("(case (when ");
		process(node.getOperand(), builder);
		builder.append(") (then ");
		process(node.getResult(), builder);
		return builder.append(")) ");
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitWith(com.facebook.presto.sql.tree.With, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitWith(With node, StringBuilder builder) {
		if (SUPPRESS_WITH)
			return builder;
		if (node.isRecursive())
			return notImplemented(new Object(){});
		super.visitWith(node,  builder);
		return builder;
	}

	/* (non-Javadoc)
	 * @see com.facebook.presto.sql.tree.DefaultTraversalVisitor#visitWithQuery(com.facebook.presto.sql.tree.WithQuery, java.lang.Object)
	 */
	@Override
	protected StringBuilder visitWithQuery(WithQuery node, StringBuilder builder) {
		if (node.getColumnNames().isPresent())
			return notImplemented(new Object(){});
		builder.append("(with ");
		appendStringNode("as", node.getName(), builder);
		process(node.getQuery(), builder);
		return builder.append(") ");
	}

	/**
	 * Complete a case expression, whether "simple" or "searched"
	 * @param whenClauses the list of when clauses
	 * @param defaultValue the default value
	 * @param builder the StringBuilder to use
	 * @return the StringBuilder for convenience
	 */
	private StringBuilder addCaseBody(List<WhenClause> whenClauses, Optional<Expression> defaultValue, StringBuilder builder) {
		for (WhenClause clause : whenClauses) {
			process(clause, builder);
		}
		if (defaultValue.isPresent()) {
			builder.append("(default ");
			process(defaultValue.get(), builder);
			builder.append(")");
		}
		return builder.append(") ");
	}

	/** Add a properties subnode (createTable and createTableAsSelect use this) */
	private void addProperties(Map<String, Expression> properties, StringBuilder builder) {
		if (!properties.isEmpty()) {
			builder.append("(properties ");
			for (Entry<String, Expression> property : properties.entrySet()) {
				nodeWithString("property", property.getKey(), builder);
				process(property.getValue(), builder).append(") ");
			}
			builder.append(")");
		}
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
	 * Append a list of strings (inside an already-existing s-expression node)
	 * @param list the list of Strings
	 * @param builder the builder to append to
	 */
	private void appendStrings(List<String> list, StringBuilder builder) {
		for (String s : list) {
			appendString(s, builder);
		}
	}

	/**
	 * Variant on appendStrings using a varargs array instead of a list
	 * @param builder the bild to append to
	 * @param strings the strings
	 */
	private void appendStrings(StringBuilder builder, String... strings) {
		appendStrings(Arrays.asList(strings), builder);
	}

	/** Heuristic type inference: determine if an Expression has type 'date'.
	 * This should not produce false positives.  It uses heuristics to find obvious cases only.
	 */
	private boolean isDate(Expression maybeDate) {
		/* Look for date literals, since they are obviously dates */
		if (maybeDate instanceof GenericLiteral)
			return ((GenericLiteral) maybeDate).getType().equalsIgnoreCase("date");
		/* Look for functions with method name date_plus or date_minus since these produce dates (and resulted from
		 *  heuristic type inference on children).
		 */
		if (maybeDate instanceof FunctionCall)
			switch(((FunctionCall) maybeDate).getName().toString()) {
			case "date_plus":
			case "date_minus":
				return true;
			}
		/* if the date name heuristic is enabled and the expression is a ref or deref of a name, apply that heuristic */
		if (useDateNameHeuristic) {
			String name = maybeDate instanceof QualifiedNameReference ? ((QualifiedNameReference) maybeDate).getName().toString()
					: maybeDate instanceof DereferenceExpression ? ((DereferenceExpression) maybeDate).getFieldName()
							: null;
			if (name != null)
				return name.endsWith("date");
		}
		return false;
	}

	/** Heuristic type inference: determine if an Expression has type 'date interval'.
	 * This should not produce false positives.  It uses heuristics to find obvious cases only.
	 */
	private boolean isDateInterval(Expression maybeInterval) {
		/* Look for interval literals, since they are obviously intervals */
		return maybeInterval instanceof IntervalLiteral;
		/* That's all for now */
	}

	/** From a list of at least two relations and a SetOperation subclass, make a list of exactly two relations whose
	 *   members may themselves be set operations with relation lists of exactly two members.
	 *   Longer lists are canonicalized by inserting nodes of the specified type.
	 * @param relations the input list
	 * @param type the type to insert if the list needs to be reformed
	 * @param distinct value to use for the 'distinct' value in any created node 
	 * @return the canonical list
	 */
	private List<Relation> makeBinary(List<Relation> relations, Class<? extends SetOperation> type, boolean distinct) {
		assert relations.size() >= 2;
		if (relations.size() == 2) 
			return relations;
		relations = new ArrayList<>(relations);
		Relation first = relations.remove(0);
		try {
			Constructor<? extends SetOperation> cons = type.getConstructor(List.class, boolean.class);
			Relation second = cons.newInstance(relations, distinct);
			return Arrays.asList(first, second);
		} catch (Exception e) {
			throw new IllegalStateException(e);
		}
	}

	/**
	 * Convenience utility to construct a function call node
	 */
	private FunctionCall makeFunction(String name, Expression... args) {
		return new FunctionCall(QualifiedName.of(name), Arrays.asList(args));
	}

	/** Selectively turn an ArithmeticBinaryExpression node into a function call if it operates on dates */
	private Expression maybeTransform(ArithmeticBinaryExpression node) {
		/* Bail if the operator isn't add or subtract; if it is, note the name to use. */
		String name;
		switch (node.getType()) {
		case ADD:
			name = "date_plus";
			break;
		case SUBTRACT:
			name = "date_minus";
			break;
		default:
			return node;
		}
		/* Transform children, then test heuristically for date type */
		Expression left = maybeTransform(node.getLeft());
		Expression right = maybeTransform(node.getRight());
		if (isDate(left) || isDateInterval(right))
			return makeFunction(name, left, right);
		return node;
	}

	/** Selectively turn a BetweenPredicate node into a function call if it operates on dates */
	private Expression maybeTransform(BetweenPredicate node) {
		Expression value = maybeTransform(node.getValue());
		Expression min = maybeTransform(node.getMin());
		Expression max = maybeTransform(node.getMax());
		if (isDate(value) || isDate(min) || isDate(max))
			return makeFunction("date_between", value, min, max);
		return node;
	}

	/** Selectively turn a ComparisonExpression node into a function call if it operates on dates */
	private Expression maybeTransform(ComparisonExpression node) {
		/* Bail if not a possible operator, else remember the name to use */
		String name;
		switch (node.getType()) {
		case GREATER_THAN:
			name = "date_gt";
			break;
		case GREATER_THAN_OR_EQUAL:
			name = "date_ge";
			break;
		case LESS_THAN:
			name = "date_lt";
			break;
		case LESS_THAN_OR_EQUAL:
			name = "date_le";
			break;
		case NOT_EQUAL:
			name = "date_ne";
			break;
		default:
			return node;
		}
		Expression left = maybeTransform(node.getLeft());
		Expression right = maybeTransform(node.getRight());
		if (isDate(left) || isDate(right))
			return makeFunction(name, left, right);
		return node;
	}

	/* Selectively turn an expression to a Function call if it meets any of the date or date interval criteria for doing so */
	private Expression maybeTransform(Expression node) {
		if (node instanceof ArithmeticBinaryExpression)
			return maybeTransform((ArithmeticBinaryExpression) node);
		else if (node instanceof BetweenPredicate)
			return maybeTransform((BetweenPredicate) node);
		else if (node instanceof ComparisonExpression)
			return maybeTransform((ComparisonExpression) node);
		else
			return node;
	}

	/** Like appendStringNode but leaves the node open for more things to be added (see appendStringNode) */
	private StringBuilder nodeWithString(String node, String arg, StringBuilder builder) {
		return builder.append(String.format("(%s \"%s\" ", node, arg));
	}

	/**
	 * Exception when something isn't implemented
	 */
	private StringBuilder notImplemented(Object o) {
		throw new UnsupportedOperationException("Not implemented: " + o.getClass().getEnclosingMethod().getName());
	}

	/**
	 * Process an orderby list
	 * @param list the list
	 * @param builder the StringBuilder to use
	 */
	private void processOrderBy(List<SortItem> list, StringBuilder builder) {
		if (!list.isEmpty() && !SUPPRESS_ORDERBY) {
			builder.append("(orderBy ");
			for(SortItem sort : list) {
				process(sort, builder);
			}
			builder.append(") ");
		}
	}

	/** Common subroutine for set operation visitor methods */
	private StringBuilder processSetOperation(SetOperation node, StringBuilder builder, Class<? extends SetOperation> type,
			String tag) {
		boolean distinct = node.isDistinct();
		List<Relation> canonical = makeBinary(node.getRelations(), type, distinct);
		builder.append("(").append(tag).append(distinct ? " (distinct) " : " ");
		for (Relation r : canonical)
			processSetOpOperand(r, builder);
		return builder.append(") ");
	}

	/**
	 * Wrap the processing of operands to union and intersection so that they become proper
	 *   queries. 
	 */
	private void processSetOpOperand(Relation r, StringBuilder builder) {
		if (r instanceof SetOperation)
			process(r, builder);
		else if (r instanceof QuerySpecification) {
			builder.append("(query ");
			process(r, builder);
			builder.append(") ");
		} else
			throw new UnsupportedOperationException("Can't deal with set op operand type " + r.getClass().getSimpleName());
	}

	/**
	 * Process a window associated with a function call
	 * @param window the window
	 * @param builder the builder to use
	 */
	private void processWindow(Window window, StringBuilder builder) {
		if (SUPPRESS_WINDOWS)
			return;
		processOrderBy(window.getOrderBy(), builder);
		List<Expression> partitions = window.getPartitionBy();
		if (!partitions.isEmpty()) {
			builder.append("(partitionBy ");
			for(Expression expr : partitions) {
				process(expr, builder);
			}
			builder.append(") ");
		}
		if (window.getFrame().isPresent()) {
			WindowFrame frame = window.getFrame().get();
			builder.append("(frame (").append(frame.getType().name().toLowerCase()).append(") ");
			process(frame.getStart(), builder);
			if (frame.getEnd().isPresent())
				process(frame.getEnd().get(), builder);
			builder.append(") ");
		}
	}
}
