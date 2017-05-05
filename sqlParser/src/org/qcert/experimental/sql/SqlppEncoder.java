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

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
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
		if (args.length == 3 && isNumber(args[1]) && isNumber(args[2]))
			args = generateRange(args[0], Integer.parseInt(args[1]), Integer.parseInt(args[2]), ".sql");
		for (String arg : args) {
			System.out.print(arg + ": ");
			List<Statement> stmts;
			try {
				stmts = parseFile(arg);
			} catch (CompilationException e) {
				System.out.println(e.getMessage());
				continue;
			} catch (Throwable e) {
				e.printStackTrace();
				continue;
			}
			try { 
				System.out.println(encode(stmts, true));
			} catch (Throwable e) {
				System.out.println(e.toString());
			}
			
		}
	}

	/**
	 * Generate a range of arguments from a stem, a suffix, and two numeric range limits
	 * @param stem the stem to use
	 * @param start the start of the range
	 * @param end the end of the range
	 * @param suffix the suffix to use
	 * @return
	 */
	private static String[] generateRange(String stem, int start, int end, String suffix) {
		List<String> range = new ArrayList<>();
		for (int i = start; i <= end; i++)
			range.add(stem + i + suffix);
		return range.toArray(new String[range.size()]);
	}

	/** Determine if a string looks like an integer number */
	private static boolean isNumber(String string) {
		for (int i = 0; i < string.length(); i++)
			if (!Character.isDigit(string.charAt(i)))
				return false;
		return true;
	}

	/**
	 * Parse SQL source provided in a File
	 * @param file the name of the file containing the source
	 * @return the parsed statement(s) as a List<Statement>
	 */
	public static List<Statement> parseFile(String file) throws Exception {
		// Note: SqlppParserFactory has a method that will make a parser from a Reader but we do not use it because it does not
		// set up the error handling state fully, so you get an NPE instead of an informative error on things like syntax errors.
		String query = new String(Files.readAllBytes(Paths.get(file)));
		return parse(query);
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
