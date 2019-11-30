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
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.apache.asterix.common.exceptions.CompilationException;
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
import org.apache.asterix.lang.common.expression.ListConstructor.Type;
import org.apache.asterix.lang.common.expression.LiteralExpr;
import org.apache.asterix.lang.common.expression.OperatorExpr;
import org.apache.asterix.lang.common.expression.OrderedListTypeDefinition;
import org.apache.asterix.lang.common.expression.QuantifiedExpression;
import org.apache.asterix.lang.common.expression.QuantifiedExpression.Quantifier;
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
import org.apache.asterix.lang.common.struct.Identifier;
import org.apache.asterix.lang.common.struct.OperatorType;
import org.apache.asterix.lang.common.struct.QuantifiedPair;
import org.apache.asterix.lang.common.struct.VarIdentifier;
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
import org.apache.asterix.lang.sqlpp.optype.JoinType;
import org.apache.asterix.lang.sqlpp.optype.SetOpType;
import org.apache.asterix.lang.sqlpp.struct.SetOperationRight;
import org.apache.asterix.lang.sqlpp.visitor.base.ISqlppVisitor;
import org.apache.hyracks.algebricks.common.utils.Pair;

public class SPPEncodingVisitor implements ISqlppVisitor<StringBuilder, StringBuilder> {
	/** Pre-screening map for legal function calls.  Note that there are a few others that are turned into
	 *  operations; they are special cases not listed here.
	 *  The "enumeration" implied by the following static block must correspond to the enumeration sqlpp_function_name in the Coq AST, except that the members
	 *  of that enumeration are prefixed with 'SPF', e.g. 'SPFget_year'. */
	private static final Map<String, FunctionTemplate> functionTemplates = new HashMap<>();
	static {
		functionTemplates.put("get_year", new FunctionTemplate(1, 1));
		functionTemplates.put("get_month", new FunctionTemplate(1, 1));
		functionTemplates.put("get_day", new FunctionTemplate(1, 1));
		functionTemplates.put("get_hour", new FunctionTemplate(1, 1));
		functionTemplates.put("get_minute", new FunctionTemplate(1, 1));
		functionTemplates.put("get_second", new FunctionTemplate(1, 1));
		functionTemplates.put("get_millisecond", new FunctionTemplate(1, 1));
		functionTemplates.put("avg", new FunctionTemplate(1, 1));
		functionTemplates.put("min", new FunctionTemplate(1, 1));
		functionTemplates.put("max", new FunctionTemplate(1, 1));
		functionTemplates.put("count", new FunctionTemplate(1, 1));
		functionTemplates.put("sum", new FunctionTemplate(1, 1));
		functionTemplates.put("coll_avg", new FunctionTemplate(1, 1));
		functionTemplates.put("coll_min", new FunctionTemplate(1, 1));
		functionTemplates.put("coll_max", new FunctionTemplate(1, 1));
		functionTemplates.put("coll_count", new FunctionTemplate(1, 1));
		functionTemplates.put("coll_sum", new FunctionTemplate(1, 1));
		functionTemplates.put("array_avg", new FunctionTemplate(1, 1));
		functionTemplates.put("array_min", new FunctionTemplate(1, 1));
		functionTemplates.put("array_max", new FunctionTemplate(1, 1));
		functionTemplates.put("array_count", new FunctionTemplate(1, 1));
		functionTemplates.put("array_sum", new FunctionTemplate(1, 1));
		functionTemplates.put("sqrt", new FunctionTemplate(1, 1));
		functionTemplates.put("substring", new FunctionTemplate(2, 3));
		functionTemplates.put("regexp_contains", new FunctionTemplate(2, 3));
		functionTemplates.put("contains", new FunctionTemplate(2, 2));
	}

	// Grammar:
	//	 FunctionCallExpression ::= FunctionName "(" ( Expression ( "," Expression )* )? ")"
	// Coq:
	//			  | SPFunctionCall : string -> list sqlpp_expr -> sqlpp_expr
	// Encoding:
	//   (FunctionCall "functionName" (sqlpp_expr) ...)
	// But, also, some unary expressions in the grammar are encoded as function calls and this needs to
	// be undone here.
	@Override
	public StringBuilder visit(CallExpr node, StringBuilder builder) throws CompilationException {
		String name = node.getFunctionSignature().getName().toLowerCase();
		List<Expression> args = node.getExprList();
		// Handle special cases that are really unary operators
		if (name.equals("not"))
			return makeNode("Not", builder, args.get(0));
		else if (name.equals("is-null"))
			return makeNode("IsNull", builder, args.get(0));
		else if (name.equals("is-missing"))
			return makeNode("IsMissing", builder, args.get(0));
		else if (name.equals("is-unknown"))
			return makeNode("IsUnknown", builder, args.get(0));
		else {
			// Typical case: actually a function call.  We let it through if it is on the "approved list" but boot it if not,
			// since we can't handle arbitrary user-defined or system-extension functions (and actually can't handle many built-in
			// AsterixDB functions at this point, either).
			builder = startNode("FunctionCall", builder);
			// UnsupportedOperationException here if name is not approved
			builder = startNode(preApprove(name, args.size()), builder);
			builder = endNode(builder);
			builder = appendNodeList(args, builder);
			return endNode(builder);
		}
	}

	// Grammar:
 	//	CaseExpression ::= SimpleCaseExpression | SearchedCaseExpression
	//			SimpleCaseExpression ::= <CASE> Expression ( <WHEN> Expression <THEN> Expression )+ ( <ELSE> Expression )? <END>
	//			SearchedCaseExpression ::= <CASE> ( <WHEN> Expression <THEN> Expression )+ ( <ELSE> Expression )? <END>
	// Coq:
	//	   | SPSimpleCase : sqlpp_expr -> list sqlpp_when_then -> option sqlpp_expr -> sqlpp_expr
	//	   | SPSearchedCase : list sqlpp_when_then -> option sqlpp_expr -> sqlpp_expr
	//	 with sqlpp_when_then : Set:=
	//	   | SPWhenThen : sqlpp_expr -> sqlpp_expr -> sqlpp_when_then
	// Encoding:
	//   (SimpleCase (sqlpp_expr)  (Default (sqlpp_expr)? (WhenThen (sqlpp_expr) (sqlpp_expr)) ...) 
	//   (SearchedCase (Default (sqlpp_expr)? (WhenThen (sqlpp_expr) (sqlpp_expr)) ...)
	//      The optional Default term is placed before the one or more WhenThen terms to facilitate pattern matching.
	@Override
	public StringBuilder visit(CaseExpression node, StringBuilder builder) throws CompilationException {
		Expression operand = node.getConditionExpr();
		if (operand != null && !isTrueLiteral(operand)) {
			builder = startNode("SimpleCase", builder);
			builder = operand.accept(this, builder);
		} else
			builder = startNode("SearchedCase", builder);
		Expression defaultValue = node.getElseExpr();
		if (defaultValue != null)
			builder = makeNode("Default", builder, defaultValue);
		List<Expression> whens = node.getWhenExprs();
		List<Expression> thens = node.getThenExprs();
		assert whens.size() == thens.size();
		Iterator<Expression> thenIter = thens.iterator();
		for (Expression when : node.getWhenExprs()) {
			Expression then = thenIter.next();
			builder = makeNode("WhenThen", builder, when, then);
		}
		return endNode(builder);
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(CompactStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("compact");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(ConnectFeedStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("connect feed");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(CreateDataverseStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("create dataverse");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(CreateFeedPolicyStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("create feed policy");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(CreateFeedStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("create feed");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(CreateFunctionStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("create function");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(CreateIndexStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("create index");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(DatasetDecl node, StringBuilder builder) throws CompilationException {
		return notSupported("create dataset");
	}

	// Not in grammar or Coq.  Present in many examples.  Rendered harmless by ignoring.
	@Override
	public StringBuilder visit(DataverseDecl node, StringBuilder builder) throws CompilationException {
		// Silently elided
		return builder;
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(DataverseDropStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop dataverse");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(DeleteStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("delete");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(DisconnectFeedStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("disconnect feed");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(DropDatasetStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop dataset");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(FeedDropStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop feed");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(FeedPolicyDropStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop feed policy");
	}

	// Grammar:
	//   PathExpression  ::= PrimaryExpression ( Field | Index )*
	//   Field           ::= "." Identifier
	// Coq:
	//   | SPDot : sqlpp_expr -> string -> sqlpp_expr
	// Encoding:
	//  (Dot "Identifier" (primaryExpression))
	@Override
	public StringBuilder visit(FieldAccessor node, StringBuilder builder) throws CompilationException {
		return makeNode("Dot", builder, getVar(node.getIdent()), node.getExpr());
	}

	// Grammar:
	//   FromClause         ::= <FROM> FromTerm ( "," FromTerm )*
	// Coq:
	//   list sqlpp_from   (* The 'from' clause as a list of from terms.  Empty list if missing *) 
	// Encoding:
	//   (Froms (FromTerm) (FromTerm) ...)
	@Override
	public StringBuilder visit(FromClause node, StringBuilder builder) throws CompilationException {
		return makeNode("Froms", builder, node.getFromTerms());
	}

	// Grammar:
	//	FromTerm           ::= Expression (( <AS> )? Variable)?
	//            ( ( JoinType )? ( JoinClause | UnnestClause ) )*
	//  In the AsterixDB AST, JoinClause and UnnestClause are subtypes of AbstractBinaryCorrelateClause, which
	//    includes the JoinType.  
	// Coq:
	//	with sqlpp_from : Set :=
	//			  | SPFrom : sqlpp_expr -> option string -> list sqlpp_join_clause -> sqlpp_from
	//  In Coq, the sqlpp_join_clause has two forms, one for JoinClause and one for UnnestClause
	// Encoding:
	//  (From (sqlpp_expr) (as "Variable")? (sqlpp_join_clause) (sqlpp_join_clause) ...)
	@Override
	public StringBuilder visit(FromTerm node, StringBuilder builder) throws CompilationException {
		builder = startNode("From", builder);
		Expression expr = node.getLeftExpression();
		builder = expr.accept(this, builder);
		builder = appendOptionalAlias(node.getLeftVariable(), expr, builder);
		builder = appendNodeList(node.getCorrelateClauses(), builder);
		return endNode(builder);
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(FunctionDecl node, StringBuilder builder) throws CompilationException {
		return notSupported("function declaration");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(FunctionDropStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop function");
	}
	
	// Grammar:
	//	GroupbyClause      ::= <GROUP> <BY> ( Expression ( (<AS>)? Variable )? ( "," Expression ( (<AS>)? Variable )? )*
	//            ( <GROUP> <AS> Variable
	//              ("(" Variable <AS> VariableReference ("," Variable <AS> VariableReference )* ")")?
	//            )?
	//  The "group by" section is stored in the AST node as the GbyPairList member.
	//  The "group as" section is stored in the AST node as the GroupVar and GroupFieldList members.
	// Coq:
	//	with sqlpp_group_by : Set :=
	//			| SPGroupBy : list (sqlpp_expr * option string)   (* group by section *)
	//				-> option (string * list (string * string))  (* group as section *)
	//				-> sqlpp_group_by
	//		    | SPNoGroupBy
	// Encoding:
	//  (GroupBy
	//    (Keys (Key (Expression) (as "Variable")?) ...)
	//    (GroupAs "Variable" (Rename "Variable" "VariableReference") ...)? )
	@Override
	public StringBuilder visit(GroupbyClause node, StringBuilder builder) throws CompilationException {
		List<GbyVariableExpressionPair> groupBySection = node.getGbyPairList();
		List<Pair<Expression, Identifier>> groupAsSection = node.getGroupFieldList();
		builder = startNode("GroupBy", builder);
		builder = startNode("Keys", builder);
		for (GbyVariableExpressionPair pair : groupBySection) {
			builder = startNode("Key", builder);
			Expression expr = pair.getExpr();
			builder = expr.accept(this, builder);
			builder = appendOptionalAlias(pair.getVar(), expr, builder);
			builder = endNode(builder); // Key
		}
		builder = endNode(builder); // Keys
		if (node.hasGroupVar()) {
			builder = startNode("GroupAs", builder);
			builder = appendString(getVar(node.getGroupVar()), builder);
			for (Pair<Expression, Identifier> pair : groupAsSection) {
				builder = startNode("Rename", builder);
				String first = getVar((VariableExpr) pair.first);  // No CCE; if one happens consider it an assertion failure
				String second = getVar(pair.second);
				builder = appendString(first, builder);
				builder = appendString(second, builder);
				builder = endNode(builder); // Rename
			}
			builder = endNode(builder); // GroupAs 
		}
		return endNode(builder); // Grouping
	}

	// Grammar:
	//    HavingClause       ::= <HAVING> Expression
	// Coq:
	//	with sqlpp_select_block : Set :=
	//			SPSelectBlock : ...
	//		        -> option sqlpp_expr  (* the optional having clause *) 
	//		        ...
	// Encoding: (part of SelectBlock)
	//   (Having (sqlpp_expr))
	@Override
	public StringBuilder visit(HavingClause node, StringBuilder builder) throws CompilationException {
		return makeNode("Having", builder, node.getFilterExpression());
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(IfExpr node, StringBuilder builder) throws CompilationException {
		// Not used by SQL++ grammar (present in AQL)?
		return notSupported("if");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(IndependentSubquery node, StringBuilder builder) throws CompilationException {
		// Not used by SQL++ grammar (present in AQL)?
		return notSupported("independent subquery");
	}
	
	// Grammar:
	//   PathExpression  ::= PrimaryExpression ( Field | Index )*
	//    Index           ::= "[" ( Expression | "?" ) "]"
	// Coq:
	//	  | SPIndex : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPIndexAny : sqlpp_expr -> sqlpp_expr
	// Encoding:
	// (Index (index_expr) (primary_expr))
	// (IndexAny (primary_expr))
	@Override
	public StringBuilder visit(IndexAccessor node, StringBuilder builder) throws CompilationException {
		if (node.isAny())
			return makeNode("IndexAny", builder, node.getExpr());
		else
			return makeNode("Index", builder, node.getIndexExpr(), node.getExpr());
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(IndexDropStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop index");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(InsertStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("insert");
	}

	// Grammar:
	//  JoinClause         ::= <JOIN> Expression (( <AS> )? Variable)? <ON> Expression
	//  JoinType           ::= ( <INNER> | <LEFT> ( <OUTER> )? )
	//  In the AsterixDB AST, JoinClause and UnnestClause are subtypes of AbstractBinaryCorrelateClause, which
	//    includes the JoinType.
	//  Note: we currently follow the documentation, which supports an "AT" clause only on UNNEST.  The parser seems to accept
	//    it on JOIN also, which seems logical.  TODO investigate this; possibly a documentation error.
	// Coq:
	//    Inductive sqlpp_join_type : Set := SPInner | SPLeftOuter.
	//     ...
	//      | SPJoin : sqlpp_join_type -> sqlpp_expr -> option string -> sqlpp_expr -> sqlpp_join_clause
	// Encoding:
	//  (Join (Inner | LeftOuter) (as "Variable")? (Expr1) (Expr2)) 
	@Override
	public StringBuilder visit(JoinClause node, StringBuilder builder) throws CompilationException {
		builder = startNode("Join", builder);
		builder = makeNode(node.getJoinType() == JoinType.INNER ? "Inner" : "LeftOuter", builder);
		VariableExpr var = node.getRightVariable();
		Expression expr = node.getRightExpression();
		builder = appendOptionalAlias(var, expr, builder);
		builder = expr.accept(this, builder);
		builder = node.getConditionExpression().accept(this, builder);
		return endNode(builder);
	}

	// Grammar:
	//	 WithClause         ::= <WITH> WithElement ( "," WithElement )*
	//   LetClause          ::= (<LET> | <LETTING>) LetElement ( "," LetElement )*
	//	 LetClause          ::= (<LET> | <LETTING>) LetElement ( "," LetElement )*
	//	 LetElement         ::= Variable "=" Expression
	//	 WithElement        ::= Variable <AS> Expression
	// Note: SQL++ supports 'with' and 'let' in different positions in the grammar but they come to the same thing
	//   semantically and are represented by a LetClause node in all cases.  The Coq and encoding are the same.
	//   The AsterixDB represents a "LetClause" or "WithClause" from the grammar as a list of (confusingly named)
	//   LetClause nodes, each defining one variable.  In the parsing of SelectBlock, we compensate by giving the
	//   list itself the tag "Lets".
	// Coq:
	//   list (string * sqlpp_expr)
	// Encoding:
	//   (Lets (Let "string" (sqlpp_expr)) ...)
	@Override
	public StringBuilder visit(LetClause node, StringBuilder builder) throws CompilationException {
		return makeNode("Let", builder, getVar(node.getVarExpr()), node.getBindingExpr());
	}

	// The limit clause is in the grammar but not in Coq and is current elided.
	@Override
	public StringBuilder visit(LimitClause node, StringBuilder builder) throws CompilationException {
		return builder; // elided
	}

	// Grammar:
	//	ArrayConstructor         ::= "[" ( Expression ( "," Expression )* )? "]"
	//	MultisetConstructor      ::= "{{" ( Expression ( "," Expression )* )? "}}"
	// Coq:
	//	  | SPArray : list sqlpp_expr -> sqlpp_expr                                                   
	//    | SPBag : list sqlpp_expr -> sqlpp_expr
	// Encoding:
	// (Array (sqlpp_expr) ...)
	// (Bag (sqlpp_expr) ...)
	@Override
	public StringBuilder visit(ListConstructor node, StringBuilder builder) throws CompilationException {
		if (node.getType() == Type.ORDERED_LIST_CONSTRUCTOR)
			return makeNode("Array", builder, node.getExprList());
		else
			return makeNode("Bag", builder, node.getExprList());
	}
	
	// Grammar:
	//   Literal ::= StringLiteral
	//          | IntegerLiteral
	//          | FloatLiteral
	//          | DoubleLiteral
	//          | <NULL>
	//          | <MISSING>
	//          | <TRUE>
	//          | <FALSE>
	//  (lexical fine-points omitted)
	// Coq:
	//	  | SPLiteral : data -> sqlpp_expr (* For string, number, boolean *)
	//	  | SPNull | SPMissing
	// Encoding:
	//   Conventional literal syntax for strings, numbers, booleans, or
	//   (Null)
	//   (Missing)
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
		case FLOAT:
		case DOUBLE:
			return builder.append(String.format("%f", lit.getValue())).append(" ");
		case MISSING:
			return makeNode("Missing", builder);
		case NULL:
			return makeNode("Null", builder);
		default:
			throw new UnsupportedOperationException("Not supporting literals of type " + lit.getLiteralType());
		}
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(LoadStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("load");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(NestClause node, StringBuilder builder) throws CompilationException {
		// Not used by SQL++ grammar (present in AQL)?
		return notSupported("nest");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(NodegroupDecl node, StringBuilder builder) throws CompilationException {
		return notSupported("create nodegroup");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(NodeGroupDropStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop nodegroup");
	}

	// Grammar:
	//	Expression ::= OperatorExpression | CaseExpression | QuantifiedExpression
	//	OperatorExpression ::= PathExpression
	//	                       | Operator OperatorExpression
	//	                       | OperatorExpression Operator (OperatorExpression)?
	//	                       | OperatorExpression <BETWEEN> OperatorExpression <AND> OperatorExpression
	// However, the AST node called OperatorExpr only covers the binary operators and the BETWEEN operator.
	// Path expressions are handled as FieldAccessor or IndexAccessor and unary operators as UnaryExpr.
	// A complication of OperatorExpr is that a single node can hold an associative chain of N operators
	// operating on N+1 operands.  This case is handled by transforming the single OperatorExpr into a nest of
	// simpler OperatorExprs with one operator per node.
	// Coq:
	//    | SPPlus : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPMinus : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPMult : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPDiv : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPMod : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPExp : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPConcat : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPIn : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPEq : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//    | SPFuzzyEq : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPNeq : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPLt : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPGt : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPLe : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPGe : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPLike : sqlpp_expr -> string -> sqlpp_expr (* Special restriction, not in the SQL++ spec *)
	//	  | SPAnd : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPOr : sqlpp_expr -> sqlpp_expr -> sqlpp_expr
	//	  | SPBetween : sqlpp_expr -> sqlpp_expr -> sqlpp_expr -> sqlpp_expr                                         
	// Encoding:
	//   (Plus|Minus|Mult|Div|Mod|Exp|Concat|In|Eq|Neq|Lt|Gt|Le|Ge|Like|And|Or (sqlpp_expr) (sqlpp_expr))
	//   (Between (sqlpp_expr) (sqlpp_expr) (sqlpp_expr))
	//
	@Override
	public StringBuilder visit(OperatorExpr node, StringBuilder builder) throws CompilationException {
		List<Expression> exprs = node.getExprList();
		List<OperatorType> ops = node.getOpList();
		if (ops.size() > 1) {
			// Associative chain of binary operators
			assert exprs.size() == ops.size() + 1;
			return visit (makeBinary(exprs, ops), builder);
		}
		// Single operator case
		OperatorType op = ops.get(0);
		String tag;
		boolean negated = false;
		switch (op) {
		case AND:
			tag = "And";
			break;
		case NOT_BETWEEN:
			negated = true;
			//$FALL-THROUGH$
		case BETWEEN:
			tag = "Between";
			break;
		case CARET:
			tag = "Exp";
			break;
		case CONCAT:
			tag = "Concat";
			break;
		case IDIV:
		case DIV:
			tag = "Div";
			break;
		case EQ:
			tag = "Eq";
			break;
		case FUZZY_EQ:
			tag = "FuzzyEq";
			break;
		case GE:
			tag = "Ge";
			break;
		case GT:
			tag = "Gt";
			break;
		case NOT_IN:
			negated = true;
			//$FALL-THROUGH$
		case IN:
			tag = "In";
			break;
		case LE:
			tag = "Le";
			break;
		case NOT_LIKE:
			negated = true;
			//$FALL-THROUGH$
		case LIKE:
			tag = "Like";
			break;
		case LT:
			tag = "Lt";
			break;
		case MINUS:
			tag = "Minus";
			break;
		case MOD:
			tag = "Mod";
			break;
		case MUL:
			tag = "Mult";
			break;
		case NEQ:
			tag = "Neq";
			break;
		case OR:
			tag = "Or";
			break;
		case PLUS:
			tag = "Plus";
			break;
		default:
			throw new IllegalStateException("Null OperatorType should never happen"); 
		}
		if (negated)
			builder = startNode("Not", builder);
		if (op == OperatorType.LIKE)
			/* Impleent special restriction on RHS */
			builder = makeNode(tag, builder, exprs.get(0), getStringLiteral(exprs.get(1), "LIKE expressions"));
		else
			builder = makeNode(tag, builder, exprs);
		return negated ? endNode(builder) : builder;
	}

	// Grammar:
	//   OrderbyClause      ::= <ORDER> <BY> Expression ( <ASC> | <DESC> )? ( "," Expression ( <ASC> | <DESC> )? )*
	// Coq:
	//	with sqlpp_order_by : Set :=
	//			| SPOrderBy : list (sqlpp_expr * sqlpp_order_spec) -> sqlpp_order_by
	//			| SPNoOrderBy
	//  Definition sqlpp_order_spec : Set := SortDesc (* Ascending or Descending *)
	// Encoding:
	//  (Ordering (OrderBy (sqlpp_expr) "ASC" | "DESC")...)
	@Override
	public StringBuilder visit(OrderbyClause node, StringBuilder builder) throws CompilationException {
		builder = startNode("Ordering", builder);
		Iterator<OrderModifier> mods =  node.getModifierList().iterator();
		for (Expression expr : node.getOrderbyList()) {
			OrderModifier mod = mods.next();
			makeNode("OrderBy", builder, expr, mod.name());
		}
		return endNode(builder);
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(OrderedListTypeDefinition node, StringBuilder builder) throws CompilationException {
		return notSupported("create type"); // probably only reachable from a type definition
	}

	// Grammar:
	//    Projection         ::= ( Expression ( <AS> )? Identifier | "*" )
	// Coq:
	//	with sqlpp_project : Set :=
	//			  | SPProject : (sqlpp_expr * option string) -> sqlpp_project
	//			  | SPProjectStar
	// Encoding:
	//   (Project (sqlpp_expr) "Identifier"?)
	//   (ProjectStar)
	@Override
	public StringBuilder visit(Projection node, StringBuilder builder) throws CompilationException {
		if (node.star())
			return makeNode("ProjectStar", builder);
		else if (node.hasName())
			return makeNode("Project", builder, node.getExpression(), node.getName());
		else
			return makeNode("Project", builder, node.getExpression());
	}

	// Grammar:
	//	QuantifiedExpression ::= ( (<ANY>|<SOME>) | <EVERY> ) Variable <IN> Expression ( "," Variable "in" Expression )*
	//            <SATISFIES> Expression (<END>)?
	// Coq:
	//	  | SPSome : list (string * sqlpp_expr) -> sqlpp_expr -> sqlpp_expr
	//	  | SPEvery : list (string * sqlpp_expr) -> sqlpp_expr -> sqlpp_expr
	// Encoding:
	//  (Some | Every (Bindings (VarIn "Variable" (Expression)) ...) (SatExpression))
	@Override
	public StringBuilder visit(QuantifiedExpression node, StringBuilder builder) throws CompilationException {
		String tag = node.getQuantifier() == Quantifier.EVERY ? "Every" : "Some";
		builder = startNode(tag, builder);
		builder = startNode("Bindings", builder);
		for (QuantifiedPair pair : node.getQuantifiedList())
			builder = makeNode("VarIn", builder, getVar(pair.getVarExpr()), pair.getExpr());
		builder = endNode(builder); // Bindings
		builder = node.getSatisfiesExpr().accept(this, builder);
		return endNode(builder); // Every or Some
	}

	// This node in the AsterixDB AST is essentially vacuous for our purposes and merely serves to make an expression
	// (which is typically a Select but doesn't have to be) into a top-level statement on a par with others.
	public StringBuilder visit(Query node, StringBuilder builder) throws CompilationException {
		return node.getBody().accept(this,  builder);
	}

	// Grammar:
	//	  ObjectConstructor        ::= "{" ( FieldBinding ( "," FieldBinding )* )? "}"
	// 	  FieldBinding             ::= Expression ":" Expression
	//  Apparently SQL++ is serious about the fact that the the field name is just an expression.  It must have type String,
	//  but its value need not be statically known.  In our own implementation we restrict the name to being a string literal
	//  and reject violating cases here.
	// Coq:
	//    | SPObject : list (string * sqlpp_expr) -> sqlpp_expr
	// Encoding:
	//   (Object  (Field name (sqlpp_expr)) ...)
	@Override
	public StringBuilder visit(RecordConstructor node, StringBuilder builder) throws CompilationException {
		builder = startNode("Object", builder);
		for (FieldBinding field : node.getFbList()) {
			String name = getStringLiteral(field.getLeftExpr(), "object field names");
			builder = makeNode("Field", builder, name, field.getRightExpr());
		}
		return endNode(builder);
	}
	
	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(RecordTypeDefinition node, StringBuilder builder) throws CompilationException {
		return notSupported("create type"); // probably only reachable from a type definition
	}

	// Grammar:
	//	SelectBlock        ::= SelectClause
	//            ( FromClause ( LetClause )?)?
	//            ( WhereClause )?
	//            ( GroupbyClause ( LetClause )? ( HavingClause )? )?
	//            |
	//            FromClause ( LetClause )?
	//            ( WhereClause )?
	//            ( GroupbyClause ( LetClause )? ( HavingClause )? )?
	//            SelectClause
	// Note that what the grammar calls LetClause is a _list_ of what the AST calls LetClause.
	// Coq:
	//	with sqlpp_select_block : Set :=
	//			SPSelectBlock : sqlpp_select -> list sqlpp_from   (* The 'from' clause as a list of from terms.  Empty list if missing *)
	//			    -> list (string * sqlpp_expr)  (* the first let clause, empty list if missing *)
	//		        -> sqlpp_where -> sqlpp_group_by
	//		        -> list (string * sqlpp_expr)  (* the second let clause, empty list if missing *)
	//		        -> option sqlpp_expr  (* the optional having clause *) 
	//		        -> sqlpp_select_block
	// Encoding:
	//  (SelectBlock (SelectValue | SelectSQL ...) (Froms ...) (Lets ...) (Where ...) (Grouping ...) (Lets ...) (Having ...)) 
	@Override
	public StringBuilder visit(SelectBlock node, StringBuilder builder) throws CompilationException {
		builder = startNode("SelectBlock", builder);
		builder = node.getSelectClause().accept(this, builder);
		if (node.hasFromClause())
			builder = node.getFromClause().accept(this, builder);
		else
			builder = makeNode("Froms", builder); // indicate absence for easier pattern match
		if (node.hasLetClauses())
			builder = makeNode("Lets", builder, node.getLetList());
		else
			builder = makeNode("Lets", builder); // etc.
		if (node.hasWhereClause())
			builder = node.getWhereClause().accept(this, builder);
		else
			builder = makeNode("Where", builder);
		if (node.hasGroupbyClause())
			builder = node.getGroupbyClause().accept(this, builder);
		else
			builder = makeNode("GroupBy", builder);
		if (node.hasLetClausesAfterGroupby())
			builder = makeNode("Lets", builder, node.getLetListAfterGroupby());
		else
			builder = makeNode("Lets", builder);
		if (node.hasHavingClause())
			builder = node.getHavingClause().accept(this, builder);
		else
			builder = makeNode("Having", builder);
		return endNode(builder);
	}

	// Grammar:
	//	SelectClause       ::= <SELECT> ( <ALL> | <DISTINCT> )? ( SelectRegular | SelectValue )
	//	SelectRegular      ::= Projection ( "," Projection )*
	//	SelectValue      ::= ( <VALUE> | <ELEMENT> | <RAW> ) Expression
	// Coq:
	//	with sqlpp_select : Set :=
	//		  | SPSelectSQL : sqlpp_distinct -> list sqlpp_project -> sqlpp_select
	//		  | SPSelectValue: sqlpp_distinct -> sqlpp_expr -> sqlpp_select
	//  Inductive sqlpp_distinct : Set := SPDistinct | SPAll.
	//  See visit(Projection) for sqlpp_project
	// Encoding:
	//   (SelectSQL (Distinct | All) (Projection)...)
	//   (SelectValue (Distinct | All) (sqlpp_expr))
	@Override
	public StringBuilder visit(SelectClause node, StringBuilder builder) throws CompilationException {
		String tag = node.selectElement() ? "SelectValue" : "SelectSQL";
		builder = startNode(tag, builder);
		builder = makeNode(node.distinct() ? "Distinct" : "All", builder);
		builder = (node.selectElement() ? node.getSelectElement() : node.getSelectRegular()).accept(this, builder);
		return endNode(builder);
	}

	// Grammar, Coq, and Encoding are covered under SelectClause.  This method merely sub-dispatches
	//   in the case where the SelectClause has selectElement() true.
	@Override
	public StringBuilder visit(SelectElement node, StringBuilder builder) throws CompilationException {
		return node.getExpression().accept(this, builder);
	}

	// Grammar:
	//	SelectStatement    ::= ( WithClause )?
	//                   SelectSetOperation (OrderbyClause )? ( LimitClause )?
	//  The documented grammar has "SelectStatement" but no "SelectExpression" (it uses SubQuery for the case where a
	//  select statement is embedded in an expression).  AsterixDB regularizes this a bit by using the SelectExpression
	//  node but the syntactic distinction (whether the statement is surrounded by parentheses) is already meaningless
	//  by the time we reach this method.
	// Coq:
	//	with sqlpp_select_statement : Set :=
	//			SPSelectStmt :
	//				list (string * sqlpp_expr)     (* The 'with' clause  Empty list if missing *)
	//				-> ... see visit(SelectSetOperation) for details ...
	//				-> sqlpp_order_by
	//				-> sqlpp_select_statement
	// Encoding:
	//   (Select (Lets (Let ...)...)? (... see SelectSetOperation for details ...) (Ordering ...)?)
	@Override
	public StringBuilder visit(SelectExpression node, StringBuilder builder) throws CompilationException {
		builder = startNode("Select", builder);
		if (node.hasLetClauses())
			builder = makeNode("Lets", builder, node.getLetList());
		else
			builder = makeNode("Lets", builder);
		builder = node.getSelectSetOperation().accept(this, builder);
		if (node.hasOrderby())
			builder = node.getOrderbyClause().accept(this, builder);
		else
			builder = makeNode("Ordering", builder);
		return endNode(builder);
		
	}

	// Grammar, Coq, and Encoding are covered under SelectClause.  This method merely sub-dispatches
	//   in the case where the SelectClause has selectRegular() true.
	@Override
	public StringBuilder visit(SelectRegular node, StringBuilder builder) throws CompilationException {
		for (Projection p : node.getProjections())
			builder = p.accept(this, builder);
		return builder;
	}

	// Grammar:
	//	  SelectSetOperation ::= SelectBlock (<UNION> <ALL> ( SelectBlock | Subquery ) )*
	//	  Subquery           ::= "(" SelectStatement ")"
	//  In other words, the node denotes a union of N query parts, the first of which must be
	//  a SelectBlock while others can be either a SelectBlock or a complete SelectStatement.
	// Coq:
	//   In the Coq AST< the SelectSetOperation is inlined into the select statement and constitutes two constructor
	//   arguments:
	//       ...
	//	     -> sqlpp_select_block (* The first or only select block *) 
	//	     -> list sqlpp_union_element (* additional select blocks or subqueries, unioned with the first *)
	//       ...
	//	     with sqlpp_union_element : Set :=
	//			  | SPBlock : sqlpp_select_block -> sqlpp_union_element
	//			  | SPSubquery : sqlpp_select_statement -> sqlpp_union_element        
	// Encoding:
	//   (SelectBlock ...) (Unions (SelectBlock | SelectStatement)* ) )
	@Override
	public StringBuilder visit(SelectSetOperation node, StringBuilder builder) throws CompilationException {
		builder = node.getLeftInput().accept(this, builder);
		builder = startNode("Unions", builder); // Empty if no unions.  Helps pattern matching
		if (node.hasRightInputs())
			for (SetOperationRight right : node.getRightInputs()) {
				assert right.getSetOpType() == SetOpType.UNION;  // Other connectives shouldn't happen in SQL++
				builder = right.getSetOperationRightInput().accept(this, builder);
			}
		return endNode(builder);
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(SetStatement node, StringBuilder builder) throws CompilationException {
		// Not used by SQL++ grammar (present in AQL)?
		return notSupported("set statement");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(StartFeedStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("start feed");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(StopFeedStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("stop feed");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(TypeDecl node, StringBuilder builder) throws CompilationException {
		return notSupported("create type");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(TypeDropStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("drop type");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(TypeReferenceExpression node, StringBuilder builder) throws CompilationException {
		return notSupported("create type"); // probably only reachable from a type definition
	}

	// Grammar:
	//	OperatorExpression ::= ...
	//            | Operator OperatorExpression
	//            | ...
	// Coq:
	//	  | SPPositive : sqlpp_expr -> sqlpp_expr
	//	  | SPNegative : sqlpp_expr -> sqlpp_expr
	//	  | SPExists : sqlpp_expr -> sqlpp_expr
	//	  | SPNot : sqlpp_expr -> sqlpp_expr
	//	  | SPIsNull : sqlpp_expr -> sqlpp_expr
	//	  | SPIsMissing : sqlpp_expr -> sqlpp_expr
	//	  | SPIsUnknown : sqlpp_expr -> sqlpp_expr                                  
	// Encoding:
	//  (Positive|Negative|Exists|Not|IsNull|IsMissing|IsUnknown (sqlpp_expr))
	// But, note that Not, IsNull, IsMissing, and IsUnknown are not parsed as unary expressions but turned into functions
	// by the parser, so these cases are constructed in visit(CallExpr) rather than here.  
	// Also, the AST allows for a NOT_EXISTS, which we negate here.
	@Override
	public StringBuilder visit(UnaryExpr node, StringBuilder builder) throws CompilationException {
		String tag;
		boolean negated = false;
		switch (node.getExprType()) {
		case NOT_EXISTS:
			negated = true;
			//$FALL-THROUGH$
		case EXISTS:
			tag = "Exists";
			break;
		case NEGATIVE:
			tag = "Negative";
			break;
		case POSITIVE:
			tag = "Positive";
			break;
		default:
			throw new IllegalStateException("Null unary operator type should never happen");
		}
		if (negated)
			builder = startNode("Not", builder);
		builder = makeNode(tag, builder, node.getExpr());
		return negated ? endNode(builder) : builder;
	}

	// Grammar:
	//	UnnestClause       ::= ( <UNNEST> | <CORRELATE> | <FLATTEN> ) Expression
	//            ( <AS> )? Variable ( <AT> Variable )?
	// Coq:
	//    Inductive sqlpp_join_type : Set := SPInner | SPLeftOuter.
	//     ...
	//	  | SPUnnest : sqlpp_join_type -> sqlpp_expr -> option string -> option string -> sqlpp_join_clause  
	// Encoding:
	//  (Unnest (Inner | LeftOuter) (as "Variable")? (at "Variable")? (Expr)) 
	@Override
	public StringBuilder visit(UnnestClause node, StringBuilder builder) throws CompilationException {
		builder = startNode("Unnest", builder);
		builder = makeNode(node.getJoinType() == JoinType.INNER ? "Inner" : "LeftOuter", builder);
		VariableExpr var = node.getRightVariable();
		Expression expr = node.getRightExpression();
		builder = appendOptionalAlias(var, expr, builder);
		if (node.hasPositionalVariable())
			builder = makeNode("at", builder, getVar(node.getPositionalVariable()));
		builder = expr.accept(this, builder);
		return endNode(builder);
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(UnorderedListTypeDefinition node, StringBuilder builder) throws CompilationException {
		return notSupported("create type"); // probably only reachable from a type definition
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(UpdateClause node, StringBuilder builder) throws CompilationException {
		return notSupported("update");
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(UpdateStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("update");
	}

	// Grammar:
	//    VariableReference     ::= <IDENTIFIER>|<DelimitedIdentifier>
	//  The AsterixDB parser distinguishes reference contexts for variables from definition contexts.  References
	//  are prefixed with '$'.  Our decodeVariableRef utility method undoes this.   The parser also handles
	//  delimited identifiers, so nothing special needs to be done for them (since they will be encoded as
	//  strings and seen as such in the Coq)
	// Coq:
	//    | SPVarRef : string -> sqlpp_expr                                   
	// Encoding:
	//   (VarRef "var")
	@Override
	public StringBuilder visit(VariableExpr node, StringBuilder builder) throws CompilationException {
		return makeNode("VarRef", builder, 	decodeVariableRef(getVar(node)));
	}

	// Grammar:
	//	WhereClause        ::= <WHERE> Expression
	// Coq:
	//	with sqlpp_where : Set :=
	//			  | SPWhere : sqlpp_expr -> sqlpp_where
	//			  | SPNoWhere
	// Encoding:
	//  (Where (expr))
	@Override
	public StringBuilder visit(WhereClause node, StringBuilder builder) throws CompilationException {
		return makeNode("Where", builder, node.getWhereExpr());
	}

	// Not in grammar or Coq.
	@Override
	public StringBuilder visit(WriteStatement node, StringBuilder builder) throws CompilationException {
		return notSupported("write");
	}

	/**
	 * Append the encoding of a list of nodes by visiting them
	 * @param nodeList the list of nodes
	 * @param builder the builder
	 * @return the builder
	 * @throws CompilationException 
	 */
	private StringBuilder appendNodeList(List<? extends ILangExpression> nodeList, StringBuilder builder) throws CompilationException {
		for (ILangExpression e : nodeList)
			builder = e.accept(this, builder);
		return builder;
	}

	/**
	 * Append an optional 'as' node based on the convention that (1) this is to be done when a VariableExpr is provided and
	 *   (2) it is to be skipped in cases where the alias is vacuous (it isn't really an alias) because the AsterixDB parser
	 *   does that some times
	 * @param variable the provided VariableRef or null
	 * @param expr the expression for which the alias is provided (possibly null or possibly a vacuous variable reference)
	 * @param builder the builder
	 * @return the builder
	 */
	private StringBuilder appendOptionalAlias(VariableExpr variable, Expression expr, StringBuilder builder) {
		if (variable == null || expr == null)
			return builder;
		if (isDistinctName(variable, expr)) {
			builder = startNode("as", builder);
			builder = appendString(decodeVariableRef(getVar(variable)), builder);
			builder = endNode(builder);
		}
		return builder;
	}

	/**
	 * Append a string
	 * @param contents the contents of the string
	 * @param builder the builder
	 * @return the builder
	 */
	private StringBuilder appendString(String contents, StringBuilder builder) {
		return builder.append("\"").append(contents).append("\" ");
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
	 * End a node
	 * @param builder the builder
	 * @return the builder
	 */
	private StringBuilder endNode(StringBuilder builder) {
		return builder.append(") ");
	}

	/**
	 * In object constructions and 'like' expressions (at least) we restrict the language of certain arguments to be string literals
	 *   instead of arbitrary expressions.  This is checked here and the String form extracted.
	 * @param expr the Expression from which a String is extracted or else the Expression is rejected as not literal
	 * @param context a phrase to use in the error message
	 * @return a string if the expression is a String literal
	 * @throws UnsupportedOperationException with an informative message if expr is not a String literal
	 */
	private String getStringLiteral(Expression expr, String context) {
		if (expr.getKind() == Kind.LITERAL_EXPRESSION) {
			Literal name = ((LiteralExpr) expr).getValue();
			if (name.getLiteralType() == Literal.Type.STRING) {
				return name.getStringValue();
			}
		}
		throw new UnsupportedOperationException("We don't support anything except string literals in " + context);
	}

	/** Retrieve String from Identifier, ensuring no '$' prefix */
	private String getVar(Identifier ident) {
		return decodeVariableRef(ident.toString());
	}

	/** Retrieve String from VariableExpr, ensuring no '$' prefix */
	private String getVar(VariableExpr var) {
		return getVar(var.getVar());
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
	 * Convert a list of N ops (at least 2) and N+1 exprs into a new OperatorExpr such that the left operand is an OperatorExpr
	 *   with one less op and one less expr, the op is the last op, and the right operand is the last expr.  If the left operand
	 *   still has more than one op, it will get further reduced by a subsequent call to this method.
	 * @param exprs the list of exprs
	 * @param ops the list of ops
	 * @return the resulting operator expression
	 */
	private OperatorExpr makeBinary(List<Expression> exprs, List<OperatorType> ops) {
		exprs = new ArrayList<>(exprs);
		ops = new ArrayList<>(ops);
		Expression lastExpr = exprs.remove(exprs.size() - 1);
		OperatorType lastOp = ops.remove(ops.size() - 1);
		OperatorExpr remainder = new OperatorExpr(exprs, Collections.emptyList(), ops, false);
		exprs = Arrays.asList(remainder, lastExpr);
		return new OperatorExpr(exprs, Collections.emptyList(), Collections.singletonList(lastOp), false);
	}

	/**
	 * Append a complete node with a tag and optional arguments, which are either Strings or Expressions or Lists of expressions
	 * @param tag the tag
	 * @param builder the builder
	 * @param args the optional arguments
	 * @return the builder
	 * @throws CompilationException 
	 */
	@SuppressWarnings("unchecked")
	private StringBuilder makeNode(String tag, StringBuilder builder, Object... args) throws CompilationException {
		builder = startNode(tag, builder);
		for (Object arg : args) {
			if (arg instanceof String)
				builder = appendString((String) arg, builder);
			else if (arg instanceof ILangExpression)
				builder = ((ILangExpression) arg).accept(this, builder);
			else if (arg instanceof List<?>) // imperfect test; don't pass in lists whose elements aren't ILangExpression
				builder = appendNodeList((List<? extends ILangExpression>) arg, builder);
		}
		return endNode(builder);
	}

	/**
	 * Convenient error thrower for identifying unimplemented things that probably should be implemented eventually
	 * @param o an object anonymously subclassed by the throwing method, allowing the method to be identified
	 * @return a StringBuilder nominally, for composition, but never actually returns
	 */
	@SuppressWarnings("unused") // Not used now, but could be re-instated if more constructs are added later.
	private StringBuilder notImplemented(Object o) {
		Method method = o.getClass().getEnclosingMethod();
		Class<?> type = method.getParameterTypes()[0];
		throw new UnsupportedOperationException("Visitor not implemented for " + type.getSimpleName());
	}

	/**
	 * Convenient error thrower for identifying things we don't support and probably won't ever support
	 * @param verb the name (human readable) of the verb that we don't support
	 * @return a StringBuilder nominally, for composition, but never actually returns
	 */
	private StringBuilder notSupported(String verb) {
		throw new UnsupportedOperationException("'" + verb + "' is not the query subset of SQL++ and is not supported");
	}

	/**
	 * Check a function call to see if it is on the "approved list"
	 * @param name the name of the function
	 * @param argCount the number of arguments
	 * @return the name if approved
	 * @throws UnsupportedOperationException with informative message if not approved
	 */
	private String preApprove(String name, int argCount) {
		// There is some evidence from test cases that AsterixDB (at least) accepts a hyphen in place of an underscore for some
		//	functions, although the documentation for built-in functions uses only the underscore.  It is unclear whether this 
		// is to be taken as a SQL++ feature (I suspect not).  But, we're mimicking that behavior for now.
		name = name.replace('-', '_'); // TODO consider eliminating this and just fixing up test cases that expect it.
		FunctionTemplate t = functionTemplates.get(name);
		if (t == null)
			throw new UnsupportedOperationException(name + " is not a supported function");
		if (argCount < t.minArgs || argCount > t.maxArgs)
			throw new UnsupportedOperationException(name + " requires from " + t.minArgs + " to " + t.maxArgs + " arguments");
		return name;
	}

	/**
	 * Start a node
	 * @param nodeTag the tag
	 * @param builder the builder
	 * @return the builder
	 */
	private StringBuilder startNode(String nodeTag, StringBuilder builder) {
		return builder.append("(").append(nodeTag).append(" ");
	}
	
	private static class FunctionTemplate {
		int minArgs;
		int maxArgs;
		FunctionTemplate(int minArgs, int maxArgs) {
			this.minArgs = minArgs;
			this.maxArgs = maxArgs;
		}
	}
}
