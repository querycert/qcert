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
package org.qcert.util;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.commons.csv.CSVFormat;
import org.apache.commons.csv.CSVParser;
import org.apache.commons.csv.CSVRecord;
import org.qcert.util.SchemaUtil.ListType;
import org.qcert.util.SchemaUtil.ObjectType;
import org.qcert.util.SchemaUtil.PrimitiveType;
import org.qcert.util.SchemaUtil.Type;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import com.google.gson.internal.Streams;
import com.google.gson.stream.JsonWriter;

/**
 * Generates the standard qcert input format from one or more "CSV" files and a qcert schema.
 * 
 * <p>There are two public methods, a <b>loadData</b> method, which is flexible enough to handle all sorts of file naming conventions
 *   and "CSV" formats, and a <b>main</b> method, which can be invoked from the command line but requires a strict file naming
 *   convention and handles only strict the RFC 4180 CSV interpretation, with a required header line in each file.
 *    
 * <p>Most generally, the input consists of
 * <ol><li>a set of CSV files and their associated internal type ("table") names.  On the command line, the association is strict:
 *   the file name must be the table name plus the suffix <b>.csv</b> and be found in a specific directory.  For <b>loadData</b>
 *   the association is given explicitly in a Map argument.
 * <li>a CSV format designation (all formats supported by Apache commons-csv, but a header must be available somehow, 
 *  either from the format or from each file).  On the command line, the format is not specified and must be RFC 4180 with in-file
 *  headers (the delimiter may optionally be set to something other than comma).
 *  <li>a qcert schema.  On the command line, this is given as a file path.  For <b>loadData</b> it is given as a <b>JsonElement</b>.
 *  </ol>
 * <p>Each CSV file should contain just data for its corresponding internal type.  That type may be either a brand in 
 *   the schema's <b>brandTypes</b> or a partition name in the schema's <b>globals</b>, depending on the memory
 *  layout intended.
 * <p>The schema should be in one of qcert standard JSON formats supported by <b>SchemaUtil</b>.  
 *   The two different ways that the set of "table" names can match names in the schema gives rise to a different memory layout.
 * <ol><li>If the table name matches a brand in the <b>brandTypes</b>, the type definition is taken from <b>typeDefs</b>
 *  and the input of that type will go in the partition called "WORLD", marked by its type.  
 *  This is a heuristic but works for present cases because, depending on the source language, we either assume this case or the
 *   next one.
 *  <li>If the table name matches a member of <b>globals</b>, the type definition is the <b>type</b> of that member
 *  and input of that type will go in a homogeneous memory partition named for the type.
 *  </ol>
 * In either case, the names of the attributes in the type definition are matched against header names in the CSV file.  A column in 
 * the CSV file that does not match an attribute name is an error.
 * <p>For this to work, all types in the schema must be primitive (numbers, booleans strings, and dates).  Embedded list and
 * object types are not handled.
 * <p>Currently, if the type is "date" (ignoring case), the field is formatted as a date JSON object with members "year", "month" and "day".
 * This is a good convention for SQL but other formats probably need to be investigated.
 */
public class DataLoader {
	private DataLoader() {}
	
	/** Primary entry point to this service.  The 'main' method is also useful but can be bypassed to call this instead
	 *   when files are named in non-standard ways or to use a CSV format understood by Apache commons-csv but other than strict RFC 4180.
	 * @param tableMap a map from "table names" (type names matching CSV files) to the corresponding CSV file contents (as Strings)
	 * @param jsonSchema the JSON format schema in one of several possible variations, as a JsonElement (array or object)
	 * @param format the CSV format to use (if the format does not include a header we assume that the first line of 
	 *   each file constitutes a header
	 * @return a JsonObject representing the loaded data
	 * @throws Exception
	 */
	public static JsonObject loadData(Map<String, String> tableMap, JsonElement jsonSchema, CSVFormat format) throws Exception {
		if (format.getHeader() == null)
			format = format.withHeader();
		Map<String, ObjectType> types = SchemaUtil.getSchema(jsonSchema);
		boolean partitioned = types.size() == 0;
		if (partitioned) {
			if (jsonSchema.isJsonObject())
				types = SchemaUtil.getGlobalsFromSchema(jsonSchema.getAsJsonObject());
			if (types.size() == 0)
				throw new IllegalArgumentException("Schema contains no useful information");
		}
			
		/* Process the data files */
		JsonObject ans = new JsonObject();
		JsonArray world = partitioned ? null : new JsonArray();
		if (!partitioned)
			ans.add("WORLD", world);
		for (Entry<String, String> filePair : tableMap.entrySet()) {
			String table = filePair.getKey();
			ObjectType def = types.get(table);
			if (def == null)
				throw new IllegalArgumentException("Type " + table + " is not in the schema");
			JsonArray thisType = process(filePair.getValue(), def, format);
			if (partitioned)
				ans.add(table, thisType);
			else {
				for (JsonElement elem : thisType) {
					JsonObject toAdd = new JsonObject();
					JsonArray brands = new JsonArray();
					brands.add(new JsonPrimitive(table));
					toAdd.add("type", brands);
					toAdd.add("data", elem);
					world.add(toAdd);
				}
			}
		}
		return ans;
	}

	/**
	 * Main program.  
	 * <p>Command line arguments are
	 * <ul><li><b>-dir &lt;path&gt;</b> (optional) the directory in which to find or create all other files, defaults to current directory
	 * <li><b>-output &lt;filename&gt;</b> (required) the name of the output file (absolute or relative to <b>-dir</b>)
	 * <li><b>-schema &lt;filename&gt;</b> (required) the name of the schema file (absolute or relative to <b>-dir</b>)
	 * <li><b>-delimiter &lt;char&gl;</b> (optional) a character to use as delimiter (defaults to comma; if the chose character is shell-sensitive, be sure to quote it)
	 * <li>all other arguments are assumed to be type names.  A file of that name with extension <b>.csv</b> must be present in <b>-dir</b>
	 * </ul>
	 */
	public static void main(String[] args) throws Exception {
		
		/* Parse the command line */
		String directory = null, schema = null, output = null; char delimiter = 0;
		List<String> tables = new ArrayList<>();
		boolean dirFlag = false, outFlag = false, schemaFlag = false, delimiterFlag = false;
		for (String arg : args) {
			boolean table = false;
			if (dirFlag)
				directory = arg;
			else if (outFlag)
				output = arg;
			else if (schemaFlag)
				schema = arg;
			else if (delimiterFlag) {
				if (arg.length() != 1)
					throw new IllegalArgumentException("Delimiters must be single character");
				else
					delimiter = arg.charAt(0);
			} else
				table = true;
			dirFlag = outFlag = schemaFlag = delimiterFlag = false;
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
					if (delimiter != 0)
						throw new IllegalArgumentException("Duplicate -delimiter");
					else
						delimiterFlag = true;
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
		File outputFile = new File(output);
		File schemaFile = new File(schema);
		if (directory != null) {
			if (!outputFile.isAbsolute())
				outputFile = new File(directory, output);
			if (!schemaFile.isAbsolute())
				schemaFile = new File(directory, schema);
		}
		
		/* Canonicalize the file names, read the contents, and associate each with its corresponding table name */
		Map<String, String> tableMap = new HashMap<>();
		for (String table : tables) {
			File toRead = directory == null ? new File(table + ".csv") : new File(directory, table + ".csv");
			String contents = new String(Files.readAllBytes(Paths.get(toRead.getAbsolutePath())));
			tableMap.put(table, contents);
		}
		
		/* Parse the schema */
		JsonElement jsonSchema = new JsonParser().parse(new FileReader(schemaFile));

		/* Process, using callable service */
		CSVFormat format = CSVFormat.RFC4180;
		if (delimiter != 0)
			format = format.withDelimiter(delimiter);
		JsonObject ans = loadData(tableMap, jsonSchema, format);
		
		/* Write the result */
		FileWriter wtr = new FileWriter(outputFile);
		JsonWriter json = new JsonWriter(wtr);
		json.setLenient(true);
		json.setIndent("  ");
		Streams.write(ans, json);
		json.close();
	}

	/**
	 * Convert a primitive value of designated type to a JsonElement
	 * @param value the value to convert
	 * @param fieldType the type of the field
	 * @return a JsonElement (either a primitive or a date object)
	 */
	private static JsonElement convertPrimitiveValue(String value, Type fieldType) {
		String typeName = ((PrimitiveType) fieldType).typeName;
		switch(typeName) {
		case "String":
			return new JsonPrimitive(value);
		case "Nat":
		case "Float":
			/* We are a little loosy-goosy with numbers since the sources of information are often inexact */
			try {
			    return new JsonPrimitive(Integer.parseInt(value));
			} catch (NumberFormatException ig) {
			    return new JsonPrimitive(Double.parseDouble(value));
			}
		case "ESqlDate":
			return formatDate(value);
		case "Bool":
			return new JsonPrimitive(value.equalsIgnoreCase("true"));
		default:
			throw new UnsupportedOperationException("Don't known how to convert primitive schema type " + typeName);
		}
	}

	/**
	 * Format a SQL-style String date into a JSON date object, which, by convention, we use for this type
	 * TODO support other kinds of dates
	 * @param stringDate the date to format
	 * @return the JSON result
	 */
	private static JsonElement formatDate(String stringDate) {
		String[] dateParts = stringDate.split("-");
		assert dateParts.length == 3;
		String[] names = {"year",  "month", "day"};
		JsonObject ans = new JsonObject();
		for (int i = 0; i < 3; i++) {
			ans.add(names[i], new JsonPrimitive(dateParts[i]));
		}
		return ans;
	}

	/** Process an individual table, producing its rows in JSON form 
	 * @param data the CSV file contents as a String
	 * @param def the type definition as an ObjectType
	 * @param format the CSVFormat to use
	 * @return a JsonArray of the translation of the rows
	 * @throws Exception
	 */
	private static JsonArray process(String data, ObjectType def, CSVFormat format) throws Exception {
		JsonArray ans = new JsonArray();
		List<CSVRecord> records = CSVParser.parse(data, format).getRecords();
		for (CSVRecord record : records) {
			Map<String, String> recmap = record.toMap();
			JsonObject datum = new JsonObject();
			for (Entry<String, String> col : recmap.entrySet()) {
				datum.add(col.getKey(), processColumn(col.getKey(), col.getValue(), def));
			}
			ans.add(datum);
		}
		return ans;
	}

	/**
	 * Process an individual column of an individual row of an individual table, producing its JSON representation as a JSON object
	 * @param fieldName the name of the column
	 * @param value the raw (String) value in the CSV file
	 * @param def the ObjectType that should produce the type for each field name, allowing the value to be interpreted
	 * @return a JsonObject encoding the column of the row
	 */
	private static JsonElement processColumn(String fieldName, String value, ObjectType def) {
		if (fieldName == null)
			throw new IllegalArgumentException("No header information in CSV file");
		Type fieldType = def.attributes.get(fieldName);
		if (fieldType == null)
			throw new IllegalArgumentException("Field " + fieldName + " is not among the attributes of type " + def.brand);
		if (fieldType instanceof PrimitiveType) {
			return convertPrimitiveValue(value, fieldType);
		}
		if (fieldType instanceof ListType) {
			Type elementType = ((ListType) fieldType).elementType;
			if (elementType instanceof PrimitiveType) {
				JsonArray ans = new JsonArray();
				String[] values = value.split(",");
				for (String val : values)
					ans.add(convertPrimitiveValue(val, elementType));
				return ans;
			}
		}
		throw new UnsupportedOperationException("Can't handle embedded object types, lists thereof, or lists of lists, when loading data");
	}
}
