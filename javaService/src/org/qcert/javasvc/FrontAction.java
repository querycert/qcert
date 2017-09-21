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
package org.qcert.javasvc;

import java.io.IOException;
import java.io.StringWriter;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.internal.Streams;
import com.google.gson.stream.JsonWriter;

/**
 * Code that may be deployed as a whisk action in a two-action sequence where the following action is made from QcertJS.js.
 * Incorporates both the Java service and the logic in the demo that decides when to invoke it for a given QcertCompilerConfig.
 * The same code can also be invoked in a simulation under NanoHTTPd (designed to replace the current JavaService).  
  */
public class FrontAction extends Dispatcher {
	/**
	 * The entry point of the action.
	 * @param args a JSON object conforming to the QcertCompilerConfig type.
	 * @return the exact argument if no Java services have been performed or else a modified JSON object of the same type but modified
	 *   by the actions of the applicable JavaServices
	 */
	public static JsonObject main(JsonObject args) {
		String verb = null;
		boolean sourceCAMP = false;
		// TODO add support for CSV conversion of input data, if any
		String source = getAsString(args, "source");
		if (source == null || source.length() == 0)
			return argsWithError(args, "Source not specified");
		String query = getAsString(args, "query");
		if (query == null || query.length() == 0)
			return argsWithError(args, "Query not specified");
		String schema = getAsString(args, "schema"); 
		// Schema can legally be missing in many cases.  If it is present, though, it might need conversion from SQL to JSON
		schema = maybeConvertSchema(schema);
		// Input is only present when evaluation is called for.  If present, it might need conversion from CSV form to our standard form */
		String input = getAsString(args, "input");
		input = maybeConvertInput(input, schema);
		switch (source) {
		case "sql": {
	        verb = "parseSQL";
	        sourceCAMP = false;
	        break;
	    }
		case "sqlpp": {
	        verb = "parseSQLPP";
	        sourceCAMP = false;
	        break;
	    }
		case "tech_rule": {
			if (schema == null || schema.length() == 0)
				return argsWithError(args, "A schema is required for technical rules");
	        verb = "techRule2CAMP";
	        sourceCAMP = true;
	        query = combineInputAndSchema(query, schema);
	        if (query == null)
	        	return argsWithError(args, "Invalid schema");
	        break;
		}
        case  "designer_rule": {
        	verb = "serialRule2CAMP";
	        sourceCAMP = true;
	        break;
        }
	    default:
	    	return args;
	    }
		String result = dispatch(verb, query);
		args.addProperty("query", result);
        args.addProperty("sourcesexp", true);
        if (sourceCAMP) {
            args.addProperty("source", "camp_rule");
            fixPath(args.get("path"));
        }
        if (input != null)
        	args.addProperty("input", input);
        return args;
    }
	
	/** Convenient wrapper for adding an error element to the args */
	private static JsonObject argsWithError(JsonObject args, String error) {
		args.addProperty("error", error);
		return args;
	}

	/** Combines a (String) query with a (JSON-as-String) schema to form a new JSON object and Stringifies the result.
	 * Any error results in a null return. */
	private static String combineInputAndSchema(String query, String schema) {
		try {
			JsonElement parsed = new JsonParser().parse(schema);
			JsonObject ans = new JsonObject();
			ans.add("schema", parsed);
			ans.addProperty("query",  query);
			return stringify(ans);
		} catch (Throwable t) {
			return null;
		}
	}

	/** If an initial jrule-to-camp step was performed by this action, and there is a path, adjust the path to account for the step
	 *   performed.   If the path is invalid, we leave it alone (the error will be handled downstream).
	 * @param path the candidate path (null if absent)
	 */
	private static void fixPath(JsonElement path) {
		if (path == null || !path.isJsonArray())
			return;
		JsonArray patharray = path.getAsJsonArray();
		if (patharray.size() > 0) {
			JsonElement first = patharray.get(0);
			if (first.isJsonPrimitive() && first.getAsJsonPrimitive().isString()) {
				String maybe = first.getAsString();
				if (maybe.equals("camp_rule"))
					patharray.remove(0);
			}
		}
				
		
	}

	/** Convenient wrapper for getting a String, defensively, avoiding any exceptions for unexpected data form.
	 * Returns null if either the member doesn't exist or the member isn't a String
	 */
	private static String getAsString(JsonObject obj, String member) {
		JsonElement ans  = obj.get(member);
		if (ans == null)
			return null;
		if (ans.isJsonPrimitive() && ans.getAsJsonPrimitive().isString())
			return ans.getAsString();
		return null;
	}

	/** Determine if a String contains a SQL schema.  Not intended to be foolproof but just to discriminate the two supported schema
	 	notations (SQL and JSON) when the input is at least mostly valid. */
	private static boolean isSQLSchema(String schemaText) {
		/* A SQL schema should have the word "create" in it but SQL is case insensitive.  For present purposes, we can
		 * just lowercase the entire string.  */
		schemaText = schemaText.toLowerCase();
		int create = schemaText.indexOf("create");
		if (create < 0)
			return false;
		int brace = schemaText.indexOf('{');
		if (brace >= 0 && brace < create)
			/* Word create is coincidentally appearing inside what is probably a JSON schema */
			return false;
		/* Looking more like SQL.  Drop any blanks that follow 'create' */
		schemaText = schemaText.substring(create + 6).trim();
		/* The next word must be 'table' (case insensitive) */
		int table = schemaText.indexOf("table");
		return table == 0;
	}

	/**
	 * Determine if there is input in CSV form; if so, convert it to standard form
	 * @param input the contents of the input member or null if there is no such member
	 * @return
	 */
	private static String maybeConvertInput(String input, String schema) {
		if (input == null)
			return null;
		JsonParser parser = new JsonParser();
		JsonElement parsedInput = parser.parse(input);
		if (parsedInput.isJsonObject() && parsedInput.getAsJsonObject().has("delimiter") && parsedInput.getAsJsonObject().has("data")) {
			parsedInput.getAsJsonObject().add("schema", parser.parse(schema));
			try {
				return dispatch("csv2JSON", stringify(parsedInput));
			} catch (Exception e) {}
		}
		return input;
	}

	/**
	 * Determine if there is a schema in SQL form; if so, convert it to JSON form
	 * @param schema the schema to convert or null if there is no schema
	 * @return the appropriately modified form of the argument (often just the argument itself)
	 */
	private static String maybeConvertSchema(String schema) {
		if (schema != null && isSQLSchema(schema))
			schema = dispatch("sqlSchema2JSON", schema);
		return schema;
	}

	/**
	 * Encapsulate the preferred logic to stringify JSON using GSON (toString will do something close, but this is better)
	 * @param element the JSON element to stringify
	 * @return the String version
	 * @throws IOException if anything goes wrong
	 */
	private static String stringify(JsonElement element) throws IOException {
		StringWriter wtr = new StringWriter();
		JsonWriter json = new JsonWriter(wtr);
		json.setLenient(true);
		json.setIndent("  ");
		Streams.write(element, json);
		json.close();
		return wtr.toString();
	}
}
