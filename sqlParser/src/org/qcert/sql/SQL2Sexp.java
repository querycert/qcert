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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;

import com.facebook.presto.sql.parser.CaseInsensitiveStream;
import com.facebook.presto.sql.parser.SqlBaseLexer;
import com.facebook.presto.sql.parser.StatementSplitter;

import util.FileUtil;
import util.SExpParser;
import util.SExpression;

/**
 * Main program for translating SQL into S-expression form for import into qcert.
 */
public class SQL2Sexp {
	/** The default data directory when not "single" unless overridden by -source option */
	private static final File dataDirectory = new File("data");

	/** The default output directory when not "-single" unless overridden by -output option */
	private static final File outputDirectory = new File("sexp");

	/** Suffix completion for input files */
	private static final String inputTemplate = "%s.sql";

	/** Suffix completion for single output files */
	private static final String outputTemplate = "%s.s-sql";

	/** Suffix completion for split output files */
	private static final String splitOutputTemplate = "%s_%d.s-sql";
	
	/** Main program */
	public static void main(String[] args) throws Exception {
		if (args.length == 1 && "-single".equals(args[0])) {
			processSingle();
			return;
		}
		List<String> sources = new ArrayList<>();
		int index = 0;
		File data = dataDirectory;
		File output = outputDirectory;
		boolean interleaved = false;
		boolean splitStatements = false; 
		boolean useDateNameHeuristic = true;
		while (index < args.length) {
			String arg = args[index];
			if (arg.equals("-source")) {
				data = new File(args[index+1]);
				index += 2;
			} else if (arg.equals("-output")) {
				output = new File(args[index+1]);
				index += 2;
			} else {
				index++;
				if (arg.equals("-interleaved"))
					interleaved = true;
				else if (arg.equals("-splitStatements"))
					splitStatements = true;
				else if (arg.equals("-noDateNameHeuristic"))
					useDateNameHeuristic = false;
				else if (arg.startsWith("-"))
					throw new IllegalArgumentException(arg);
				else
					sources.add(arg);
			}
		}
		if (sources.size() == 3 && isNumber(sources.get(1)) && isNumber(sources.get(2)))
			sources = generateRange(sources);
		for (String source : sources) {
			String result = process(source, interleaved, splitStatements, useDateNameHeuristic, data, output);
			if (result == null || result.length() == 0)
				System.out.println("Query " + source + " parsed and converted");
			else {
				System.out.println("Query " + source + " failed to parse or convert");
				System.out.println(" " + result);
			}
		}			
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
		FixupState state = FixupState.OPEN;
		for (Token token : lexer.getAllTokens()) {
			switch (state) {
			case ELIDE1:
				state = FixupState.ELIDE2;
				continue;
			case ELIDE2:
				state = FixupState.OPEN;
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
			default:
				if (token.getType() == SqlBaseLexer.INTERVAL) {
					state = FixupState.INTERVAL;
					buffer.append(token.getText());
					continue;
				}
				break;
			}
			if (token.getType() == SqlBaseLexer.INTEGER_VALUE)
				savedInteger = token;
			else if (savedInteger != null) {
				String unit = getUnit(token.getText());
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

	/** Generate a range of arguments from a stem, start index, and end index */
	private static List<String> generateRange(List<String> sources) {
		String stem = sources.get(0);
		int start = Integer.parseInt(sources.get(1));
		int end = Integer.parseInt(sources.get(2));
		List<String> range = new ArrayList<>();
		for (int i = start; i <= end; i++)
			range.add(stem + i);
		return range;
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

	/** Determine if a "query" has multiple statements */
	private static boolean hasMultipleStatements(String query) {
		StatementSplitter splitter = new StatementSplitter(query);
		return splitter.getCompleteStatements().size() > 1;
	}

	/** Determine if a string looks like an integer number */
	private static boolean isNumber(String string) {
		for (int i = 0; i < string.length(); i++)
			if (!Character.isDigit(string.charAt(i)))
				return false;
		return true;
	}

	/**
	 * Process a single query by simple name (in file-to-file mode).  On success, return null or the empty string
	 * On failure, return the exception message.
	 */
	private static String process(String qn, boolean interleaved, boolean splitStatements, boolean useDateNameHeuristic, 
			File data, File output) {
		try {
			String query = FileUtil.readFile(new File(data, String.format(inputTemplate, qn)));
			query = applyLexicalFixups(query);
			String result = PrestoEncoder.parseAndEncode(query, interleaved, useDateNameHeuristic);
			if (hasMultipleStatements(query) && splitStatements)
				writeSplitOutput(result, qn, output); // subsumes sanity check
			else {
				reparse(result); // sanity check
				FileUtil.writeFile(new File(output, String.format(outputTemplate, qn)), result);
			}
			return null;
		} catch (Exception e) {
			String msg = e.getMessage();
			if (msg == null)
				e.printStackTrace();
			return msg == null ? e.toString() : msg;
		}
	}

	/**
	 * Special version of process to implement "single" mode (runs as pipe segment).
	 */
	private static void processSingle() {
		try {
			String query = readStdin();
			query = applyLexicalFixups(query);
			String result = PrestoEncoder.parseAndEncode(query, false, true);
			System.out.println(result);
		} catch (Exception e) {
			String msg = e.getMessage();
			if (msg == null)
				msg = e.toString();
			System.out.println(msg);
		}
	}

	/** Read stdin into a String until eos (in a pipeline) 
	 * @throws IOException */
	private static String readStdin() throws IOException {
		InputStreamReader srdr = new InputStreamReader(System.in);
		StringWriter swtr = new StringWriter();
		PrintWriter wtr = new PrintWriter(swtr);
		BufferedReader rdr = new BufferedReader(srdr);
		String line = rdr.readLine();
		while (line != null) {
			wtr.println(line);
			line = rdr.readLine();
		}
		rdr.close();
		wtr.close();
		return swtr.toString();
	}

	/**
	 * Parse an s-expression String produced by this utility.  May be used as a sanity check or in order to do further
	 *   processing
	 * @param toParse the s-expression String to be parsed
	 * @return the parsed result
	 * @throws Exception 
	 */
	private static SExpression reparse(String toParse) throws Exception {
		return SExpParser.parse(toParse);
	}

	/**
	 * Write each statement of the output in its own file
	 * @param result the output to split and write
	 * @param qn the query name to use as part of each output file name
	 * @param output the output directory
	 */
	private static void writeSplitOutput(String result, String qn, File output) throws Exception {
		SExpression struct = reparse(result);
		int index = 0;
		for (Object child : struct.getChildren()) {
			String toWrite = String.format("(statements %s)", child.toString());
			reparse(toWrite); // sanity check
			FileUtil.writeFile(new File(output, String.format(splitOutputTemplate, qn, index++)), toWrite);
		}
	}
	
	/** Enumeration used in lexical fixups of interval syntax */
	private enum FixupState {
		OPEN, INTERVAL, UNIT, ELIDE1, ELIDE2
	}
}
