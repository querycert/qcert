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
package org.qcert.sql;

import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.List;

import org.qcert.util.FileUtil;

import com.facebook.presto.sql.tree.ColumnDefinition;
import com.facebook.presto.sql.tree.CreateTable;
import com.facebook.presto.sql.tree.Statement;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import com.google.gson.internal.Streams;
import com.google.gson.stream.JsonWriter;

/**
 * Transforms SQL "schemas" (SQL sources containing 'create table' statements) into JSON schemas consumable by the rest of qcert
  */
public class SchemaTransformer {

	/**
	 * Convert a list of Statements representating 'create table' statements in SQL into a JsonObject representation of the schema
	 * @param statements the statements
	 * @return the JsonObject
	 */
	public static JsonObject convertSchemas(List<Statement> statements) {
		JsonObject ans = new JsonObject();
		ans.add("inheritance", new JsonArray());
		ans.add("brandTypes", new JsonArray());
		ans.add("typeDefs", new JsonArray());
		JsonObject globals = new JsonObject();
		ans.add("globals", globals);
		for (Statement s : statements) {
			assert s instanceof CreateTable;
			CreateTable ct = (CreateTable) s;
			/* Conversion to array in the following is to check that every TableElement is a ColumnDefinition */
			ColumnDefinition[] defs = ct.getElements().toArray(new ColumnDefinition[ct.getElements().size()]);
			String tableName = ct.getName().toString().toLowerCase();
			JsonObject tableType = new JsonObject();
			tableType.add("dist", new JsonPrimitive("distr"));
			JsonObject collection = new JsonObject();
			tableType.add("type", collection);
			collection.add("$coll", convertColumns(defs));
			globals.add(tableName, tableType);
		}
		JsonObject converted = ans;
		return converted;
	}

	/**
	 * Main program.  
	 * <p>Command line arguments are
	 * <ul><li><b>-output &lt;filename&gt;</b> (required) the name of the output file (absolute or relative to current directory)
	 * <li><b>all other arguments are assumed to be SQL source files containing "create table" statements to be turned clauses in the
	 *   schema
	 * </ul>
	 */
	public static void main(String[] args) throws Exception {
		String output = null;
		List<String> sqlFiles = new ArrayList<>();
		boolean outFlag = false;
		for (String arg : args) {
			if (outFlag) {
				output = arg;
				outFlag = false;
			} else if (arg.equals("-output"))
				outFlag = true;
			else if (arg.charAt(0) == '-')
				throw new IllegalArgumentException("Unknown option :" + arg);
			else 
				sqlFiles.add(arg);
		}
		if (output == null)
			throw new IllegalArgumentException("Output file must be specified");
		List<Statement> createStatements = new ArrayList<>();
		for (String fileName : sqlFiles)
			createStatements.addAll(PrestoEncoder.parse(FileUtil.readFile(new File(fileName))));
		JsonObject converted = convertSchemas(createStatements);
		FileWriter wtr = new FileWriter(new File(output));
		JsonWriter json = new JsonWriter(wtr);
		json.setLenient(true);
		json.setIndent("  ");
		Streams.write(converted, json);
		json.close();
	}

	/**
	 * Convert a list of ColumnDefinitions into JSON Object form
	 * @param defs the list as an array
	 * @return the JsonObject representation
	 */
	private static JsonObject convertColumns(ColumnDefinition[] defs) {
		JsonObject ans = new JsonObject();
		for (ColumnDefinition def : defs) {
			String type = isDate(def) ? "ESqlDate" : isString(def) ? "String" : "Nat";
			ans.add(def.getName().toLowerCase(), new JsonPrimitive(type));
		}
		return ans;
	}

	/** From a ColumnDefinition, determine whether it may be assumed to be of date type */
	private static boolean isDate(ColumnDefinition def) {
		return def.getType().equalsIgnoreCase("date");
	}

	/** From a ColumnDefinition, determine whether it may be assumed to be of string type */
	private static boolean isString(ColumnDefinition def) {
		return def.getType().toLowerCase().contains("char");
	}
}
