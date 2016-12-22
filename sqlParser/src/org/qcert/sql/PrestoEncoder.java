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
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;

import com.facebook.presto.sql.parser.CaseInsensitiveStream;
import com.facebook.presto.sql.parser.ParsingException;
import com.facebook.presto.sql.parser.SqlBaseLexer;
import com.facebook.presto.sql.parser.SqlParser;
import com.facebook.presto.sql.parser.StatementSplitter;
import com.facebook.presto.sql.tree.Node;
import com.facebook.presto.sql.tree.Statement;

/**
 * Utilities that work with presto-parser to produce other useful forms 
 */
public class PrestoEncoder {
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
	 * Parse a SQL source in string form into one or more presto nodes and then encode the result as
	 *   an S-expression string
	 * @param sourceString the SQL source string to parse and then encode
	 * @param interleaved if true, each statement is parsed then encoded with the outer loop iterating through statements;
	 *   otherwise, all parsing is done, and then all encoding
	 * @param useDateNameHeuristic if true, all field names ending in "date" are assumed to contain dates 
	 * @return the S-expression string
	 */
	public static String parseAndEncode(String sourceString, boolean interleaved, boolean useDateNameHeuristic) {
		sourceString = applyLexicalFixups(sourceString);
		if (interleaved)
			return interleavedParseAndEncode(sourceString, useDateNameHeuristic);
		return encode(parse(sourceString), useDateNameHeuristic);
	}
	
	/**
	 * Apply necessary fixups at the lexical level (needed to get the query to even be parsed by presto-parser).
	 * 1.  Convert occurances of NN [days|months|years] to interval NN [day|month|year] (needed by many TPC-DS queries).
	 * 2.  Remove parenthesized numeric field after an interval unit field (needed to run TPC-H query 1). 
	 * @param query the original query
	 * @return the altered query
	 */
	private static String applyLexicalFixups(String query) {
	    CharStream stream = new CaseInsensitiveStream(new ANTLRInputStream(query));
		SqlBaseLexer lexer = new SqlBaseLexer(stream);
		StringBuilder buffer = new StringBuilder();
		Token savedInteger = null;
		PrestoEncoder.FixupState state = PrestoEncoder.FixupState.OPEN;
		for (Token token : lexer.getAllTokens()) {
			switch (state) {
			case ELIDE1:
				state = PrestoEncoder.FixupState.ELIDE2;
				continue;
			case ELIDE2:
				state = PrestoEncoder.FixupState.OPEN;
				continue;
			case INTERVAL:
				buffer.append(token.getText());
				if (PrestoEncoder.getUnit(token.getText()) != null)
					state = PrestoEncoder.FixupState.UNIT;
				continue;
			case UNIT:
				if (token.getText().equals("(")) {
					state = PrestoEncoder.FixupState.ELIDE1;
				} else {
					buffer.append(token.getText());
					if (token.getType() != SqlBaseLexer.WS)
						state = PrestoEncoder.FixupState.OPEN;
				}
				continue;
			case OPEN:
			default:
				if (token.getType() == SqlBaseLexer.INTERVAL) {
					state = PrestoEncoder.FixupState.INTERVAL;
					buffer.append(token.getText());
					continue;
				}
				break;
			}
			if (token.getType() == SqlBaseLexer.INTEGER_VALUE)
				savedInteger = token;
			else if (savedInteger != null) {
				String unit = PrestoEncoder.getUnit(token.getText());
				if (unit != null) {
					buffer.append("interval '").append(savedInteger.getText()).append("' ").append(unit);
					savedInteger = null;
				} else if (token.getType() == SqlBaseLexer.WS)
					buffer.append(token.getText());
				else { 
					buffer.append(savedInteger.getText()).append(" ").append(token.getText());
					savedInteger = null;
				}
			} else
				buffer.append(token.getText());
		}
		return buffer.toString();
	}

	/**
	 * Utility to recognize interval unit names in either singular or plural form and return the singular of same
	 */
	private static String getUnit(String text) {
		switch (text.trim().toLowerCase()) {
		case "days": case "day":
			return "day:";
		case "months": case "month":
			return "month:";
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
				result = parser.createStatement(body);
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

	/**
	 * Parse a SQL source string.  First separates it into statements, then parses the Statements.
	 * @param sourceString the SQL source string
	 * @return the parsed statement(s) as an List<Statement>
	 */
	private static List<Statement> parse(String query) {
		StatementSplitter splitter = new StatementSplitter(query);
		SqlParser parser = new SqlParser();
		ArrayList<Statement> results = new ArrayList<Statement>(1);

		for(com.facebook.presto.sql.parser.StatementSplitter.Statement statement : splitter.getCompleteStatements()) {
			String body = statement.statement();
			Statement result = parser.createStatement(body);
			results.add(result);
		}

		if(results.isEmpty()) {
			throw new ParsingException("input query does not contain any statements");
		}

		return results;
	}

	/** Enumeration used in lexical fixups of interval syntax */
	private enum FixupState {
		OPEN, INTERVAL, UNIT, ELIDE1, ELIDE2
	}
}
