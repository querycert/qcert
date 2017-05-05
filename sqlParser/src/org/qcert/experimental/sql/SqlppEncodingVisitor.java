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
package org.qcert.experimental.sql;

import java.lang.reflect.Method;

import org.apache.asterix.common.exceptions.CompilationException;
import org.apache.asterix.lang.common.base.ILangExpression;
import org.apache.asterix.lang.common.clause.GroupbyClause;
import org.apache.asterix.lang.common.clause.LetClause;
import org.apache.asterix.lang.common.clause.LimitClause;
import org.apache.asterix.lang.common.clause.OrderbyClause;
import org.apache.asterix.lang.common.clause.UpdateClause;
import org.apache.asterix.lang.common.clause.WhereClause;
import org.apache.asterix.lang.common.expression.CallExpr;
import org.apache.asterix.lang.common.expression.FieldAccessor;
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
import org.apache.asterix.lang.sqlpp.visitor.base.ISqlppVisitor;

public class SqlppEncodingVisitor implements ISqlppVisitor<StringBuilder, StringBuilder> {
	private boolean useDateNameHeuristic;
	
	
	public SqlppEncodingVisitor(boolean useDateNameHeuristic) {
		this.useDateNameHeuristic = useDateNameHeuristic;
	}

	@Override
	public StringBuilder visit(CallExpr pf, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(CaseExpression caseExpression, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
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
	public StringBuilder visit(DataverseDecl dv, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
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
	public StringBuilder visit(FieldAccessor fa, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(FromClause fromClause, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(FromTerm fromTerm, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(FunctionDecl fd, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(FunctionDropStatement del, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(GroupbyClause gc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(HavingClause havingClause, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
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
	public StringBuilder visit(IndexAccessor ia, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
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
	public StringBuilder visit(JoinClause joinClause, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(LetClause lc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(LimitClause lc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(ListConstructor lc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(LiteralExpr l, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
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
	public StringBuilder visit(OperatorExpr ifbo, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(OrderbyClause oc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(OrderedListTypeDefinition olte, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(Projection projection, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(QuantifiedExpression qe, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(Query node, StringBuilder builder) throws CompilationException {
		builder.append("(query ");
		builder = node.getBody().accept(this, builder);
		return builder.append(") ");
	}

	@Override
	public StringBuilder visit(RecordConstructor rc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(RecordTypeDefinition tre, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(SelectBlock node, StringBuilder builder) throws CompilationException {
		builder = node.getSelectClause().accept(this, builder);
		builder = node.getFromClause().accept(this, builder);
		builder = node.getWhereClause().accept(this, builder);
		builder = acceptIfPresent(node.getGroupbyClause(), builder);
		return acceptIfPresent(node.getHavingClause(), builder);
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
	public StringBuilder visit(SelectElement selectElement, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(SelectExpression node, StringBuilder builder) throws CompilationException {
		builder.append("(select ");
		builder = acceptIfPresent(node.getLimitClause(), builder);
		builder = acceptIfPresent(node.getOrderbyClause(), builder);
		builder = node.getSelectSetOperation().accept(this, builder);
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
		if (node.hasRightInputs())
			// TODO ? Is this a SQL++ superset feature?
			throw new UnsupportedOperationException("No support yet for SelectSetOperation with RightInputs");
		return node.getLeftInput().accept(this, builder);
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
	public StringBuilder visit(UnaryExpr u, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(UnnestClause unnestClause, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
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
	public StringBuilder visit(VariableExpr v, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
	}

	@Override
	public StringBuilder visit(WhereClause wc, StringBuilder arg) throws CompilationException {
		return notImplemented(new Object(){});
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

	private StringBuilder notImplemented(Object o) {
		Method method = o.getClass().getEnclosingMethod();
		Class<?> type = method.getParameterTypes()[0];
		throw new UnsupportedOperationException("Visitor not implemented for " + type.getSimpleName());
	}
}
