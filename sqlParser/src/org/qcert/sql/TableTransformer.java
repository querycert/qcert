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
import java.io.FileReader;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import com.facebook.presto.sql.tree.ColumnDefinition;
import com.facebook.presto.sql.tree.CreateTable;
import com.facebook.presto.sql.tree.Statement;
import com.facebook.presto.sql.tree.TableElement;

import util.FileUtil;

/**
 * Generates data qcert evaluators and backends in the JSON format we use for all testing.
 * 
 * <p>Input consists of a set of .tbl files, a schema, and an output file name.
 * <p>Each .tbl file should contain the data for one table.  The name of the file (not counting the .tbl suffix) is the name of the table).
 * <p>Each line of a .tbl file represents one row.  Fields can be separated by any single character delimiter.  The order of the
 *   fields is given by the order in a separate schema.
 * <p>The schema should consist of one or more "create table" statements.  There needs to be such a statement for each table to be processed
 *   (extras are ignored).
 * <p>The types from the schema are meaningful to a limited degree.
 * <ul><li>If the type is "date" (ignoring case), the field is formatted as a date JSON object with members "year", "month" and "day".
 * <li>If the name of the type (ignoring case) is or contains the word "char" the field is treated as a string and is quoted in the JSON.
 * <li>Otherwise, the field is assumed to be numeric and is not quoted.
 * <li>This type repertoire is clearly too rudimentary in the long run and improvements are TBD.
 * </ul>
 */
public class TableTransformer {
	private static final String TYPE_PREFIX = "CONST$";

	/**
	 * Main program.  
	 * <p>Command line arguments are
	 * <ul><li><b>-dir &lt;path&gt;</b> (optional) the directory in which to find or create all other files, defaults to current directory
	 * <li><b>-output &lt;filename&gt;</b> (required) the name of the output file (absolute or relative to <b>-dir</b>)
	 * <li><b>-schema &lt;filename&gt;</b> (required) the name of the schema file (absolute or relative to <b>-dir</b>)
	 * <li><b>-delimiter &lt;char&gt;</b> (optional) the field-separating delimiter characters (defaults to vertical bar (|))
	 * <li>all other arguments are assumed to be table names.  A file of that name with extension <b>.tbl</b> must be present in <b>-dir</b>
	 * </ul>
	 */
	public static void main(String[] args) throws Exception {
		String directory = null, schema = null, output = null, delimiter = null;
		List<String> tables = new ArrayList<>();
		boolean dirFlag = false, outFlag = false, schemaFlag = false, delimFlag = false;
		for (String arg : args) {
			boolean table = false;
			if (dirFlag)
				directory = arg;
			else if (outFlag)
				output = arg;
			else if (schemaFlag)
				schema = arg;
			else if (delimFlag)
				delimiter = arg;
			else
				table = true;
			dirFlag = outFlag = schemaFlag = delimFlag = false;
			if (arg.charAt(0) == '-') {
				switch(arg) {
				case "-dir":
					if (directory != null)
						throw new IllegalArgumentException("Duplicate -dir");
					else
						dirFlag = true;
					continue;
				case "-output":
					if (output != null)
						throw new IllegalArgumentException("Duplicate -output");
					else
						outFlag = true;
					continue;
				case "-schema":
					if (schema != null)
						throw new IllegalArgumentException("Duplicate -schema");
					else
						schemaFlag = true;
					continue;
				case "-delimiter":
					if (delimiter != null)
						throw new IllegalArgumentException("Duplicate -delimiter");
					else
						delimFlag = true;
					continue;
				default:
					throw new IllegalArgumentException("Unknown option :" + arg);
				}
			}
			if (table)
				tables.add(arg);
		}
		if (output == null)
			throw new IllegalArgumentException("Output file must be specified");
		if (schema == null)
			throw new IllegalArgumentException("Schema file must be specified");
		if (delimiter == null)
			delimiter = "\\|";
		File outputFile = new File(output);
		File schemaFile = new File(schema);
		if (directory != null) {
			if (!outputFile.isAbsolute())
				outputFile = new File(directory, output);
			if (!schemaFile.isAbsolute())
				schemaFile = new File(directory, schema);
		}
		
		Map<String, ColumnDefinition[]> schemas = processSchemas(PrestoEncoder.parse(FileUtil.readFile(schemaFile)));
		PrintWriter jsonWriter = new PrintWriter(new FileWriter(outputFile));
		jsonWriter.print("{ ");
		boolean first = true;
		for (String table : tables) {
			if (!first)
				jsonWriter.println(",");
			first = false;
			File dataFile = directory == null ? new File(table + ".tbl") : new File(directory, table + ".tbl");
			jsonWriter.format("\"%s%s\" : [%n", TYPE_PREFIX, table);
			ColumnDefinition[] defs = schemas.get(table);
			process(dataFile, defs, jsonWriter, delimiter);
			jsonWriter.print("]");
		}
		jsonWriter.println("}");
		jsonWriter.close();
	}

	/** Format a date */
	private static void formatDate(String delim, String name, String data, PrintWriter jsonWriter) {
		String[] dateParts = data.split("-");
		assert dateParts.length == 3;
		jsonWriter.format("%s\"%s\": {\"year\": %s, \"month\": %s, \"day\": %s}", delim, name, dateParts[0], dateParts[1], 
				dateParts[2]);
	}

	/** Process types in an array of ColumnDefinitions to determine which are dates */
	private static boolean[] getDates(ColumnDefinition[] defs) {
		boolean[] ans = new boolean[defs.length];
		for (int i = 0; i < ans.length; i++) {
			ans[i] = defs[i].getType().equalsIgnoreCase("date");
		}
		return ans;
	}

	/** Extract the column names from an array of ColumnDefinitions */
	private static String[] getNames(ColumnDefinition[] defs) {
		String[] names = new String[defs.length];
		for (int i = 0; i < names.length; i++) {
			names[i] = defs[i].getName().toLowerCase();
		}
		return names;
	}

	/** From an array of ColumnDefinitions, determine which are types requiring their content to be quoted */
	private static boolean[] getQuotes(ColumnDefinition[] defs) {
		boolean[] ans = new boolean[defs.length];
		for (int i = 0; i < ans.length; i++) {
			ans[i] = defs[i].getType().toLowerCase().contains("char");
		}
		return ans;
	}

	/** Process an individual table, producing its rows 
	 * @param delimiter */
	private static void process(File dataFile, ColumnDefinition[] defs, PrintWriter jsonWriter, String delimiter) throws Exception {
		String[] names = getNames(defs);
		boolean[] dates = getDates(defs);
		boolean[] quotes = getQuotes(defs);
		BufferedReader dataRdr = new BufferedReader(new FileReader(dataFile));
		String line = dataRdr.readLine();
		boolean first = true;
		while (line != null) {
			if (!first)
				jsonWriter.println(",");
			first = false;
			String[] cols = line.split(delimiter);
			process(cols, names, dates, quotes, jsonWriter);
			line = dataRdr.readLine();
		}
		dataRdr.close();
	}

	/** Process one row */
	private static void process(String[] cols, String[] names, boolean[] dates, boolean[] quotes, PrintWriter jsonWriter) {
		jsonWriter.print(" {");
		String delim = "";
		for (int i = 0; i < cols.length; i++) {
			if (dates[i])
				formatDate(delim, names[i], cols[i], jsonWriter);
			else {
				String quote = quotes[i] ? "\"" : "";
				jsonWriter.format("%s\"%s\": %s%s%s", delim, names[i], quote, cols[i], quote);
			}
			delim = ", ";
		}
		jsonWriter.print("}");
	}

	/** Process the list of "create table" statements into a map from table name to ColumnDefinitions */
	private static Map<String, ColumnDefinition[]> processSchemas(List<Statement> schemas) {
		Map<String, ColumnDefinition[]> answer = new LinkedHashMap<>();
		for (Statement s : schemas) {
			assert s instanceof CreateTable;
			CreateTable ct = (CreateTable) s;
			List<TableElement> elements = ct.getElements();
			answer.put(ct.getName().toString(),  elements.toArray(new ColumnDefinition[elements.size()]));
		}
		return answer;
	}
}
