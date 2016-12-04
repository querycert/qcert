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

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;

import util.FileUtil;
import util.SExpParser;
import util.SExpression;

import com.facebook.presto.sql.parser.CaseInsensitiveStream;
import com.facebook.presto.sql.parser.SqlBaseLexer;
import com.facebook.presto.sql.parser.StatementSplitter;

/**
 * Main program for translating SQL into S-expression form for import into qcert.
 */
public class SQL2Sexp {
	/** The default data directory unless overridden by -source option */
	private static final File dataDirectory = new File("data");

	/** The default output directory unless overridden by -output option */
	private static final File outputDirectory = new File("sexp");

	/** Suffix completion for input files */
	private static final String inputTemplate = "%s.sql";

	/** Suffix completion for single output files */
	private static final String outputTemplate = "%s.s-sql";

	/** Suffix completion for split output files */
	private static final String splitOutputTemplate = "%s_%d.s-sql";
	
	/**
	 * Convert occurances of NN [days|months|years] to interval NN [day|month|year]. 
	 * @param query the original query
	 * @return the altered query
	 */
	private static String convertDateIntervals(String query) {
        CharStream stream = new CaseInsensitiveStream(new ANTLRInputStream(query));
		SqlBaseLexer lexer = new SqlBaseLexer(stream);
		StringBuilder buffer = new StringBuilder();
		Token savedInteger = null;
		for (Token token : lexer.getAllTokens()) {
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
	 * Subroutine of convertDateIntervals to recognize interval names in the plural form and return the singular of same
	 */
	private static String getUnit(String text) {
		if (text.trim().equalsIgnoreCase("days"))
			return "day";
		else if (text.trim().equalsIgnoreCase("months"))
			return "month";
		else if (text.trim().equalsIgnoreCase("years"))
			return "year";
		else
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

	/** Main program */
	public static void main(String[] args) throws Exception {
		if (args.length == 2 && "-single".equals(args[0])) {
			processSingle(args[1]);
			return;
		}
		List<String> sources = new ArrayList<>();
		int index = 0;
		File data = dataDirectory;
		File output = outputDirectory;
		boolean convertDateIntervals = false;
		boolean interleaved = false;
		boolean splitStatements = false; 
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
				else if (arg.equals("-convertDateIntervals"))
					convertDateIntervals = true;
				else if (arg.startsWith("-"))
					throw new IllegalArgumentException(arg);
				else
					sources.add(arg);
			}
		}
		if (sources.size() == 3 && isNumber(sources.get(1)) && isNumber(sources.get(2)))
			sources = generateRange(sources);
		for (String source : sources) {
			String result = process(source, convertDateIntervals, interleaved, splitStatements, data, output);
			if (result == null || result.length() == 0)
				System.out.println("Query " + source + " parsed and converted");
			else {
				System.out.println("Query " + source + " failed to parse or convert");
				System.out.println(" " + result);
			}
		}			
	}

	/**
	 * Process a single query by simple name.  On success, return null or the empty string
	 * On failure, return the exception message.
	 */
	private static String process(String qn, boolean useDaysHack, boolean interleaved, boolean splitStatements, 
			File data, File output) {
		try {
			String query = FileUtil.readFile(new File(data, String.format(inputTemplate, qn)));
			if (useDaysHack)
				query = convertDateIntervals(query);
			String result = PrestoEncoder.parseAndEncode(query, interleaved);
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
	 * Special version of process to return the s-exp form of a single sql file (used as a subprocess of qcert)
	 */
	private static void processSingle(String file) {
		try {
			String query = FileUtil.readFile(new File(file));
			query = convertDateIntervals(query);
			String result = PrestoEncoder.parseAndEncode(query, false);
			System.out.println(result);
		} catch (Exception e) {
			String msg = e.getMessage();
			if (msg == null)
				msg = e.toString();
			System.out.println(msg);
		}
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
}
