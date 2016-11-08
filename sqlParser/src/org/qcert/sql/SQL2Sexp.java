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

import util.FileUtil;
import util.SExpParser;
import util.SExpression;

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
	
	/** Main program */
	public static void main(String[] args) throws Exception {
		List<String> sources = new ArrayList<>();
		int index = 0;
		File data = dataDirectory;
		File output = outputDirectory;
		boolean useDaysHack = false;
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
				else if (arg.equals("-useDaysHack"))
					useDaysHack = true;
				else if (arg.startsWith("-"))
					throw new IllegalArgumentException(arg);
				else
					sources.add(arg);
			}
		}
		if (sources.size() == 3 && isNumber(sources.get(1)) && isNumber(sources.get(2)))
			sources = generateRange(sources);
		for (String source : sources) {
			String result = process(source, useDaysHack, interleaved, splitStatements, data, output);
			if (result == null || result.length() == 0)
				System.out.println("Query " + source + " parsed and converted");
			else {
				System.out.println("Query " + source + " failed to parse or convert");
				System.out.println(" " + result);
			}
		}			
	}
	
	/**
	 * Basically an egregious hack to get the TPC-DS queries through presto.  These use notations like
	 * "30 days" where presto needs to see "interval '30' day".  Since we do this without formally parsing
	 * the query, it is highly error prone and dependent on formatting conventions of TPC-DS
	 * @param query the original query
	 * @return the hacked query
	 */
	private static String applyDaysHack(String query) {
		int index = query.indexOf("days");
		StringBuilder revision = new StringBuilder();
		while (index != -1) {
			String before = query.substring(0, index);
			query = query.substring(index + 4);
			if (query.charAt(0) == '"') {
				/* Dirty and imprecise way of finding and skipping the quoted case */
				revision.append(before).append("days\"");
				query = query.substring(1);
			} else {
				while (before.endsWith(" "))
					before = before.substring(0, before.length() - 1);
				int numIndex = before.lastIndexOf(' '); // dubious, but works for present case
				String number = before.substring(numIndex + 1);
				before = before.substring(0, numIndex);
				revision.append(before).append(" interval '").append(number).append("' day ");
			}
			index = query.indexOf("days");
		}
		return revision.append(query).toString();
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
	 * Process a single query by simple name.  On success, return null or the empty string
	 * On failure, return the exception message.
	 */
	private static String process(String qn, boolean useDaysHack, boolean interleaved, boolean splitStatements, 
			File data, File output) {
		try {
			String query = FileUtil.readFile(new File(data, String.format(inputTemplate, qn)));
			if (useDaysHack)
				query = applyDaysHack(query);
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
