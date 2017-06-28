/*
 * Copyright 2015-2016 IBM Corporation
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
package testing.runners;

import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

// Uses JavaScript engine that ships with jdk e.g.,
// http://docs.oracle.com/javase/7/docs/technotes/guides/scripting/programmer_guide/
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

public class RunJavascript {

	// Small load-file method
	private static String readFile(String fileName) throws IOException {
		return new String(Files.readAllBytes(Paths.get(fileName)));
	}

	// Usage
	private static void usage() {
		System.err.println("Q*cert Javascript Runner expects two options:\n [-runtime filename] for the Q*cert Javscript runtime\n [-input filename] for the input data\nAnd the Javascript file\n");
	}

	// Main
	public static void main(String[] args) throws Exception {
		if(args.length != 5) {
			usage();
		}

		ScriptEngineManager factory = new ScriptEngineManager();
		ScriptEngine engine = factory.getEngineByName("JavaScript");

		String inputFile = null;
		String runtimeFile = null;

		for (int i = 0; i < args.length; i++) {
			String arg = args[i];
			// Must have a -input option for the input JSON
			if ("-input".equals(arg)) { inputFile = args[i+1]; i++; }
			// Must have a -runtime option for the Q*cert Javascript runtime
			else if ("-runtime".equals(arg)) { runtimeFile = args[i+1]; i++; }
			else {
				// Load input JSON, which may include schema (inheritance) and output
				JsonArray output;	
				if (inputFile != null) {
					JsonArray[] outputHolder = new JsonArray[1];
					String funCall = loadIO(inputFile, outputHolder);
					engine.eval(funCall);
					output = outputHolder[0];
				} else {
					throw new IllegalArgumentException("Input Data File Missing");
				}
				// Load Q*cert Javascript runtime
				if (runtimeFile != null) {
					engine.eval(readFile(runtimeFile));
				} else {
					throw new IllegalArgumentException("Runtime File Missing");
				}
				engine.eval(new java.io.FileReader(arg));
				// Evaluate the compiler query + stringify the result
				engine.eval("var result = JSON.stringify(query(world));");
				// Get the result
				String result = (String) engine.get("result");
				// Print the result
				System.out.println(result);
				// Validate the result
				if (output != null) {
					if (validate(result, output))
						System.out.println("As expected.");
					else
						System.out.println("Result was not as expected.  Expected result: " + output);
				}
			}
		}
	}

	// Validate a result when output has been provided as a JsonArray (optional)
	private static boolean validate(String result, JsonArray expected) {
		JsonArray actual = new JsonParser().parse(result).getAsJsonArray().get(0).getAsJsonArray();
		if (actual.size() != expected.size())
			return false;
		for (JsonElement e : actual)
			if (!expected.contains(e))
				return false;
		for (JsonElement e : expected)
			if (!actual.contains(e))
				return false;
		return true;
	}

	// Load input, which may optionally also include inheritance and output if actually an "I/O" file.
	private static String loadIO(String inputFile, JsonArray[] output) throws IOException {
		JsonElement rawInput = new JsonParser().parse(new FileReader(inputFile));
		if (rawInput.isJsonObject()) {
			// All acceptable input formats are JSON objects
			JsonObject input = rawInput.getAsJsonObject();
			// Attempt to obtain inheritance (else use empty array)
			JsonArray inheritance = null;
			if (input.has("schema")) {
				JsonObject schema = input.get("schema").getAsJsonObject();
				if (schema.has("hierarchy"))
					inheritance = schema.get("hierarchy").getAsJsonArray();
				else if (schema.has("inheritance"))
					inheritance = schema.get("inheritance").getAsJsonArray();
			}
			if (inheritance == null)
				inheritance = new JsonArray();
			// Attempt to obtain output (else leave output argument as is)
			if (input.has("output"))
				output[0] = input.get("output").getAsJsonArray();
			// Let input contain just the input object
			if (input.has("input"))
				input = input.get("input").getAsJsonObject();
			// Assemble result
			return String.format("var world = %s;%nvar inheritance = %s;", input, inheritance); 
		}
		throw new IllegalArgumentException("Input file does not have a recognized format");
	}
}
