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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringReader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.apache.asterix.common.exceptions.CompilationException;
import org.apache.asterix.lang.common.base.ILangExpression;
import org.apache.asterix.lang.common.base.Statement;
import org.apache.asterix.lang.common.statement.FunctionDecl;
import org.apache.asterix.lang.common.statement.Query;
import org.apache.asterix.lang.sqlpp.parser.JavaCharStream;
import org.apache.asterix.lang.sqlpp.parser.SQLPPParserConstants;
import org.apache.asterix.lang.sqlpp.parser.SQLPPParserTokenManager;
import org.apache.asterix.lang.sqlpp.parser.SqlppParserFactory;
import org.apache.asterix.lang.sqlpp.parser.Token;

/**
 * A parsing front-end for SQL++.  Allows the language to be consumed in S-expression form instead of requiring a Menhir grammar and
 * supporting code.  The structure is similar to the Presto-based SQL parser front-end, and, originally, this encoder was going to
 * subsume that older one.  It turns out that there are enough compatibility issues to require the retention of a SQL parser as well
 * as this (SQL++) one.
 */
public class SqlppEncoder {
	/**
	 * Encode a list of SQL++ tree nodes as an S-expression for importing into Coq code
	 * @param toEncode the list of nodes to encode
	 * @return the S-expression string
	 * @throws CompilationException 
	 */
	public static String encode(List<? extends ILangExpression> toEncode) throws CompilationException {
		StringBuilder buffer = new StringBuilder();
		boolean querySeen = false;
		for (ILangExpression node : toEncode) {
			// For now, we only encode query statements, and we don't encode more than one (the last one)
			if (node instanceof Query) {
				if (querySeen)
					buffer.setLength(0);
				encode(buffer, node);
				querySeen = true;
			}
		}
		return buffer.toString();
	}

	/**
	 * Encode an individual SQL++ tree node as an S-expression using an existing buffer
	 * @param buffer the existing buffer
	 * @param toEncode the presto tree node
	 * @return the buffer, for convenience
	 * @throws CompilationException 
	 */
	public static StringBuilder encode(StringBuilder buffer, ILangExpression toEncode) throws CompilationException {
		SPPEncodingVisitor visitor = new SPPEncodingVisitor();
		return toEncode.accept(visitor, buffer);
	}

	/** Evolving main driver (for testing).
	 * TODO move this to its own source file when it becomes elaborate enough. 
	 */
	public static void main(String[] args) throws Exception {
		if (args.length == 3 && isNumber(args[1]) && isNumber(args[2]))
			args = generateRange(args[0], Integer.parseInt(args[1]), Integer.parseInt(args[2]), ".sql");
		else if (args.length == 4 && args[0].equalsIgnoreCase("-sqlpp") && isNumber(args[2]) && isNumber(args[3]))
			args = generateRange(args[1], Integer.parseInt(args[2]), Integer.parseInt(args[3]), ".sqlpp");
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
			checkAndWarn(stmts);
			try { 
				outputResult(encode(stmts), arg);
				System.out.println("Succeeded");
			} catch (Throwable e) {
				System.out.println(e.toString());
			}
		}
	}

	/**
	 * Parse a SQL source string.
	 * @param query the SQL source string
	 * @return the parsed statement(s) as a List<Statement>
	 */
	public static List<Statement> parse(String query) throws Exception {
		query = applyLexicalFixups(query);
		return new SqlppParserFactory().createParser(query).parse();
	}

	/** 
	 * Convenience method combining parse and encode in one call.
	 * @param query the query
	 * @return the S-expression encoding of the query
	 * @throws Exception 
	 */
	public static String parseAndEncode(String query) throws Exception {
		return encode(parse(query));
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
	 * Adjust to mismatch between TPC's interpretation of SQL and the SQL++ parser's understanding.  We take TPC's view as canonical, despite misgivings.  Note that TPC-H and
	 *   TPC-DS seem to like different dialects.  We try to accommodate both.
	 * @param query the original query
	 * @return an adjusted query with lexical fixups applied
	 */
	private static String applyLexicalFixups(String query) {
		/* Read all the tokens into a list */
		SQLPPParserTokenManager lexer = new SQLPPParserTokenManager(new JavaCharStream(new StringReader(query)));
		List<Token> tokens = new ArrayList<>();
		Token token = lexer.getNextToken();
		while (token != null && token.kind != SQLPPParserConstants.EOF) {
			tokens.add(token);
			token = lexer.getNextToken();
		}
		/* Apply all the fixups */
		for (LexicalFixup fixup : LexicalFixup.list)
			tokens = fixup.apply(tokens);
		/* Re-assemble the final tokens into a String again.  The token manager doesn't provide whitespace as tokens, so we reconstruct the original line/column structure somewhat 
		 * painfully (and rely on the fixups not to mess with it) */
		int line = 1;
		int col = 0;
		StringBuilder output = new StringBuilder();
		String nl = String.format("%n");
		for (Token tok : tokens) {
			int nextLine = tok.beginLine;
			int nextCol = tok.beginColumn;
			while (nextLine > line) {
				output.append(nl);
				line++;
				col = 0;
			}
			line = tok.endLine;
			while (nextCol > col+1) {
				output.append(" ");
				col++;
			}
			col = tok.endColumn;
			output.append(tok.image);
		}
		return output.toString();
	}

	/** When running in test mode, displays useful warnings about source files with zero (or more than one) queries, and 
	 * function definitions in association with queries.
	 */
	private static void checkAndWarn(List<Statement> stmts) {
		int queryCount = 0;
		boolean hasFunction = false;
		for (Statement stmt : stmts) {
			if (stmt instanceof Query)
				queryCount++;
			if (stmt instanceof FunctionDecl)
				hasFunction = true;
		}
		if (queryCount == 0)
			System.out.println("(warning) Source file does not contain any queries");
		else if (queryCount > 1)
			System.out.println("(warning) Source file contains multiple queries; only the last will be processed");
		if (hasFunction && queryCount > 0)
			System.out.println("(warning) Source file contains ignored function declarations that may be used in queries");
		
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
	 * Output an s-exp file after successfully parsing the source
	 * @param parsed the parsed s-exp result as a String
	 * @param arg the command line argument which was the name of the source file (assumed to have a suffix)
	 * @throws IOException 
	 */
	private static void outputResult(String parsed, String arg) throws IOException {
		File output = new File(arg.substring(0, arg.lastIndexOf('.')) +"_j.sexp");
		PrintWriter wtr = new PrintWriter(new FileWriter(output));
		wtr.println(parsed);
		wtr.close();
	}
}
