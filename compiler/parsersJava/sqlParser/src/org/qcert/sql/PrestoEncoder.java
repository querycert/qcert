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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;

import com.facebook.presto.sql.parser.CaseInsensitiveStream;
import com.facebook.presto.sql.parser.ParsingException;
import com.facebook.presto.sql.parser.SqlBaseLexer;
import com.facebook.presto.sql.parser.SqlParser;
import com.facebook.presto.sql.parser.StatementSplitter;
import com.facebook.presto.sql.tree.CreateView;
import com.facebook.presto.sql.tree.Node;
import com.facebook.presto.sql.tree.Query;
import com.facebook.presto.sql.tree.QuerySpecification;
import com.facebook.presto.sql.tree.Select;
import com.facebook.presto.sql.tree.SelectItem;
import com.facebook.presto.sql.tree.SingleColumn;
import com.facebook.presto.sql.tree.Statement;

/**
 * Utilities that work with presto-parser to produce other useful forms 
 */
public class PrestoEncoder {
	/** Causes printing of SQL before and after lexical fixup */
	private static final boolean VERBOSE_LEXICAL = Boolean.getBoolean("VERBOSE_LEXICAL");
	
	/**
	 * Encode a list of presto tree nodes as an S-expression for importing into Coq code
	 * @param toEncode the list of presto tree nodes to encode
	 * @param useDateNameHeuristic flag indicating that field names ending in "date" denote dates 
	 * @return the S-expression string
	 */
	public static String encode(List<? extends Node> toEncode, boolean useDateNameHeuristic) {
		StringBuilder buffer = new StringBuilder();
		buffer.append("(statements ");
		for(Node node : toEncode) {
			encode(buffer, node, useDateNameHeuristic);
		}
		buffer.append(")");
		return buffer.toString();
	}

	/**
	 * Encode an individual presto tree node as an S-expression using an existing buffer
	 * @param buffer the existing buffer
	 * @param toEncode the presto tree node
	 * @return the buffer, for convenience
	 */
	public static StringBuilder encode(StringBuilder buffer, Node toEncode, boolean useDateNameHeuristic) {
		return new EncodingVisitor(useDateNameHeuristic).process(toEncode, buffer);
	}

	/**
	 * Parse a SQL source string.  First separates it into statements, then parses the Statements.
	 * @param sourceString the SQL source string
	 * @return the parsed statement(s) as an List<Statement>
	 */
	public static List<Statement> parse(String query) {
		StatementSplitter splitter = new StatementSplitter(query);
		SqlParser parser = new SqlParser();
		ArrayList<Statement> results = new ArrayList<Statement>(1);

		for(com.facebook.presto.sql.parser.StatementSplitter.Statement statement : splitter.getCompleteStatements()) {
			String body = statement.statement();
			Statement result = parseStatement(parser, body);
			results.add(result);
		}

		if(results.isEmpty()) {
			throw new ParsingException("input query does not contain any statements");
		}

		return results;
	}
	
	/**
	 * Parse a SQL source in string form into one or more presto nodes and then encode the result as
	 *   an S-expression string
	 * @param sourceString the SQL source string to parse and then encode
	 * @param interleaved if true, each statement is parsed then encoded with the outer loop iterating through statements;
	 *   otherwise, all parsing is done, and then all encoding
	 * @param useDateNameHeuristic if true, all field names ending in "date" are assumed to contain dates 
	 * @return the S-expression string
	 */
	public static String parseAndEncode(String sourceString, boolean interleaved, boolean useDateNameHeuristic) {
		if (interleaved)
			return interleavedParseAndEncode(sourceString, useDateNameHeuristic);
		return encode(parse(sourceString), useDateNameHeuristic);
	}

	/**
	 * Apply necessary fixups at the lexical level (needed to get the query to even be parsed by presto-parser).
	 * 1.  Convert occurances of 'NN [days|months|years]' to 'interval NN [day|month|year]' (needed by many TPC-DS queries).
	 * 2.  Remove parenthesized numeric field after an interval unit field (needed to run TPC-H query 1).
	 * 3.  Remove parenthesized name list in 'create view NAME (...) as' and relocate the names into the body of the statement (needed to run TPC-H query 15).
	 * 4.  On a 'create table' (schema), remove occurances of NOT NULL, which presto does not handle.
	 * Fixup 3 is only partially lexical; the lexical phase remembers the names and a visitor updates the body after parsing.  
	 * @param query the original query
	 * @param foundNames an initially empty list to which names found in fixup 3 may be added for later processing
	 * @return the altered query
	 */
	private static String applyLexicalFixups(String query, List<String> foundNames) {
		if (VERBOSE_LEXICAL) {
			System.out.println("Before:");
			System.out.println(query);
		}
	    CharStream stream = new CaseInsensitiveStream(new ANTLRInputStream(query));
		SqlBaseLexer lexer = new SqlBaseLexer(stream);
		StringBuilder buffer = new StringBuilder();
		Token savedInteger = null;
		List<Token> savedWS = new ArrayList<>();
		FixupState state = FixupState.OPEN;
		for (Token token : lexer.getAllTokens()) {
			/* The 'state' is used for fixups 2 and 3 */
			switch (state) {
			case ELIDE1:
				state = FixupState.ELIDE2;
				continue;
			case ELIDE2:
				state = FixupState.OPEN;
				continue;
			case ELIDELIST:
				if (token.getType() == SqlBaseLexer.AS) {
					buffer.append(token.getText());
					state = FixupState.OPEN;
				} else if (token.getType() != SqlBaseLexer.WS && !token.getText().equals(",") && !token.getText().equals(")")) {
					foundNames.add(token.getText());
				}
				continue;
			case CREATE:
				buffer.append(token.getText());
				if (token.getType() == SqlBaseLexer.VIEW)
					state = FixupState.VIEW;
				else if (token.getType() == SqlBaseLexer.TABLE)
					state = FixupState.TABLE;
				else if (token.getType() != SqlBaseLexer.WS)
					state = FixupState.OPEN;
				continue;
			case VIEW:
				if (token.getText().equals("(")) {
					state = FixupState.ELIDELIST;
				} else {
					buffer.append(token.getText());
					if (token.getType() == SqlBaseLexer.AS)
						state = FixupState.OPEN;
				}
				continue;
			case TABLE:
				if (token.getType() != SqlBaseLexer.NOT && token.getType() != SqlBaseLexer.NULL)
					buffer.append(token.getText());
				continue;
			case INTERVAL:
				buffer.append(token.getText());
				if (getUnit(token.getText()) != null)
					state = FixupState.UNIT;
				continue;
			case UNIT:
				if (token.getText().equals("(")) {
					state = FixupState.ELIDE1;
				} else {
					buffer.append(token.getText());
					if (token.getType() != SqlBaseLexer.WS)
						state = FixupState.OPEN;
				}
				continue;
			case OPEN:
				if (token.getType() == SqlBaseLexer.INTERVAL) {
					state = FixupState.INTERVAL;
					buffer.append(token.getText());
					continue;
				} else if (token.getType() == SqlBaseLexer.CREATE) {
					state = FixupState.CREATE;
					buffer.append(token.getText());
					continue;
				} // If 'open' and there is not a transition to another state, break the switch and try fixup 1.  This should be the only break in the switch.
				break;
			}
			/* The 'savedInteger' is used for fixup 1 */
			if (token.getType() == SqlBaseLexer.INTEGER_VALUE)
				savedInteger = token;
			else if (savedInteger != null) {
				String unit = getUnit(token.getText());
				if (unit != null) {
					buffer.append("interval '").append(savedInteger.getText()).append("' ").append(unit);
					savedInteger = null;
					savedWS.clear();
				} else if (token.getType() == SqlBaseLexer.WS)
					savedWS.add(token);
				else { 
					buffer.append(savedInteger.getText());
					for (Token ws : savedWS)
						buffer.append(ws.getText());
					buffer.append(token.getText());
					savedInteger = null;
					savedWS.clear();
				}
			} else
				buffer.append(token.getText());
		}
		if (savedInteger != null)
			buffer.append(savedInteger.getText());
		query = buffer.toString();
		if (VERBOSE_LEXICAL) {
			System.out.println("After:");
			System.out.println(query);
		}
		return query;
	}

	/**
	 * Distribute names found during lexical fixup of a 'create view' statement
	 * @param view the statement
	 * @param names the names
	 * @return a new create view statement with the names distributed into the body
	 */
	private static CreateView distributeNames(CreateView view, List<String> names) {
		if (view.getQuery().getQueryBody() instanceof QuerySpecification) {
			QuerySpecification body = (QuerySpecification) view.getQuery().getQueryBody();
			Select select = body.getSelect();
			if (select.getSelectItems().size() != names.size())
				throw new IllegalStateException("Don't know how to distribute names for 'create view' statement when the number of select items doesn't match the number of names");
			List<SelectItem> newItems = new ArrayList<>();
			Iterator<String> namesIter = names.iterator();
			for (SelectItem oldItem : select.getSelectItems()) {
				newItems.add(new SingleColumn(((SingleColumn) oldItem).getExpression(), namesIter.next()));
			}
			body = new QuerySpecification(new Select(select.isDistinct(), newItems), body.getFrom(), body.getWhere(), body.getGroupBy(), 
					body.getHaving(), body.getOrderBy(), body.getLimit());
			return new CreateView(view.getName(), new Query(view.getQuery().getWith(), body, view.getQuery().getOrderBy(), 
					view.getQuery().getLimit(), view.getQuery().getApproximate()), view.isReplace());
		}
		throw new IllegalStateException("Don't know how to distribute names for 'create view' statement when body is not a QuerySpecification");
	}

	/**
	 * Utility to recognize interval unit names in either singular or plural form and return the singular of same
	 */
	private static String getUnit(String text) {
		switch (text.trim().toLowerCase()) {
		case "days": case "day":
			return "day";
		case "months": case "month":
			return "month";
		case "years": case "year":
			return "year";
		}
		return null;
	}

	/**
	 * Alternative parse/encode loop useful when there are lots of statements.  Isolates what parses but does not encode from
	 *   what doesn't parse at all
	 * @param sourceString the source string
	 * @param useDateNameHeuristic if true, all field names ending in "date" are assumed to denote dates
	 * @return the parsed String, which might be vacuous, while rejecting all statements that don't parse (encoding errors still
	 *   cause termination)
	 */
	private static String interleavedParseAndEncode(String sourceString, boolean useDateNameHeuristic) {
		StatementSplitter splitter = new StatementSplitter(sourceString);
		SqlParser parser = new SqlParser();
		StringBuilder buffer = new StringBuilder().append("(statements ");
		int successes = 0;
		
		for(StatementSplitter.Statement statement : splitter.getCompleteStatements()) {
			String body = statement.statement();
			Statement result;
			try {
				result = parseStatement(parser, body);
			} catch (Exception e) {
				String msg = e.getMessage();
				if (msg == null)
					e.printStackTrace();
				System.out.println(msg == null ? e.toString() : msg);
				continue;
			}
			try {
				encode(buffer, result, useDateNameHeuristic);
				successes++;
			} catch (Exception e) {
				System.out.println("Successes: " + successes);
				throw e;
			}
		}
		System.out.println("Successes: " + successes);
		return buffer.append(")").toString();
	}

	/** Parse an individual statement, applying lexical fixups first */
	private static Statement parseStatement(SqlParser parser, String body) {
		List<String> names = new ArrayList<>();
		body = applyLexicalFixups(body, names);
		Statement result = parser.createStatement(body);
		if (!names.isEmpty())
			result = distributeNames((CreateView) result, names); // No CCE possible since result must be a CreateView in this case
		return result;
	}

	/** Enumeration used in lexical fixups */
	private enum FixupState {
		OPEN, /* no interval or create view observed */ 
		INTERVAL, /* observed 'interval' but not yet any unit */ 
		UNIT, /* observed a unit, not yet eliding */ 
		ELIDE1, /* started eliding paren'd number */ 
		ELIDE2, /* still eliding paren'd number */
		CREATE, /* observed 'create', not yet 'view' or 'table' */
		VIEW, /* observed 'view' after 'create' */
		ELIDELIST, /* observed parenthesized list after 'view', before 'as' and names are being elided and saved */
		TABLE, /* observed 'table' after 'create' */
	}
}
