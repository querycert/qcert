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

import java.io.FileReader;
import java.io.Reader;
import java.util.List;

import org.apache.asterix.common.exceptions.CompilationException;
import org.apache.asterix.lang.common.base.ILangExpression;
import org.apache.asterix.lang.common.base.Statement;
import org.apache.asterix.lang.sqlpp.parser.SqlppParserFactory;

/**
 * A highly preliminary experiment in using a SQL++ parser instead of a SQL parser as a baby-step toward supporting SQL++ as a source
 *  language.  Intended to more or less replace PrestoEncoder eventually.
 */
public class SqlppEncoder {
	/**
	 * Encode a list of SQL++ tree nodes as an S-expression for importing into Coq code
	 * @param toEncode the list of nodes to encode
	 * @param useDateNameHeuristic flag indicating that field names ending in "date" denote dates 
	 * @return the S-expression string
	 * @throws CompilationException 
	 */
	public static String encode(List<? extends ILangExpression> toEncode, boolean useDateNameHeuristic) throws CompilationException {
		StringBuilder buffer = new StringBuilder();
		buffer.append("(statements ");
		for(ILangExpression node : toEncode) {
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
	 * @throws CompilationException 
	 */
	public static StringBuilder encode(StringBuilder buffer, ILangExpression toEncode, boolean useDateNameHeuristic) throws CompilationException {
		SqlppEncodingVisitor visitor = new SqlppEncodingVisitor(useDateNameHeuristic);
		return toEncode.accept(visitor, buffer);
	}

	/** Evolving main driver
	 * TODO move this to its own source file when it becomes elaborate enough
	 */
	public static void main(String[] args) throws Exception {
		Reader input = new FileReader(args[0]);
		List<Statement> stmts = parse(input);
		System.out.println(encode(stmts, true));
	}

	/**
	 * Parse SQL source provided via a Reader.
	 * @param input the Reader providing the source
	 * @return the parsed statement(s) as a List<Statement>
	 */
	public static List<Statement> parse(Reader input) throws Exception {
		return new SqlppParserFactory().createParser(input).parse();
	}

	/**
	 * Parse a SQL source string.
	 * @param query the SQL source string
	 * @return the parsed statement(s) as a List<Statement>
	 */
	public static List<Statement> parse(String query) throws Exception {
		return new SqlppParserFactory().createParser(query).parse();
	}
}
