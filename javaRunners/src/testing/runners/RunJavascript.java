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

/* Standard Libraries */
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

/* GSON to import data */
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

// Uses JavaScript engine that ships with jdk e.g.,
// http://docs.oracle.com/javase/7/docs/technotes/guides/scripting/programmer_guide/
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

public class RunJavascript {

    // Small load-file method
    private static String readFile(String fileName) throws IOException {
	return new String(Files.readAllBytes(Paths.get(fileName)));
    }

    // Usage
    private static void usage() {
	System.err.println("Q*cert Javascript Runner requires the option -input or -io, the option -runtime and the Javascript file.\n"+
			   "Options:\n"+
			   " [-runtime filename] the Q*cert Javscript runtime\n"+
			   " [-io filename] a JSON object containing the input data, the schema and the expected output\n"+
			   " [-input filename] the input data\n"+
			   " [-schema filename] the schema\n"+
			   " [-output filename] the expected output\n");
    }

    // Main
    public static void main(String[] args) throws Exception {
	if(args.length < 5) {
	    usage();
	}

	ScriptEngineManager factory = new ScriptEngineManager();
	ScriptEngine engine = factory.getEngineByName("JavaScript");

	String runtimeFile = null;
	String ioFile = null;
	String inputFile = null;
	String schemaFile = null;
	String outputFile = null;
	for (int i = 0; i < args.length; i++) {
	    String arg = args[i];
	    if ("-runtime".equals(arg)) { runtimeFile = args[i+1]; i++; }
	    else if ("-io".equals(arg)) { ioFile = args[i+1]; i++; }
	    else if ("-input".equals(arg)) { inputFile = args[i+1]; i++; }
	    else if ("-schema".equals(arg)) { schemaFile = args[i+1]; i++; }
	    else if ("-output".equals(arg)) { outputFile = args[i+1]; i++; }
	    else {
		// Load Q*cert Javascript runtime
		// Must have a -runtime option for the Q*cert Javascript runtime
		if (runtimeFile != null) {
		    engine.eval(readFile(runtimeFile));
		} else {
		    throw new IllegalArgumentException("Runtime File Missing");
		}
		// Load input JSON, which may include schema (inheritance) and output
		// Must have a -input or -io option for the input JSON
		JsonElement output = null;
		QIO qio = null;
		if (ioFile != null) {
		    qio = new QIO(ioFile);
		} else if (inputFile != null) {
		    qio = new QIO(schemaFile, inputFile, outputFile);
		} else {
		    throw new IllegalArgumentException("Input Data File Missing");
		}
		output = (qio.getOutput())[0];
		String funCall = QUtil.jsFunFromQIO(qio);
		engine.eval(funCall);
		// Eval the compiled JavaScript itself
		engine.eval(new java.io.FileReader(arg));
		// Call the query
		engine.eval("var result = query(world);");
		// Get the result
		String resultAsSting= (String) engine.eval("JSON.stringify(result)");
		// Validate the result
		if (output == null) {
		    // Print the result
		    System.out.println(resultAsSting);
		} else {
		    engine.eval("var expected = "+output+";");
		    Boolean valid = (Boolean)engine.eval("equal(result, expected)");
		    if (valid) {
			System.out.println("["+arg+" js] OK");
		    } else {
			System.out.println("["+arg+" js] ERROR");
			System.out.println("Actual:");
			System.out.println(resultAsSting);
			System.out.println("Expected:");
			System.out.println(output);
      System.exit(1);
		    }
		}
	    }
	}
    }

    // Validate a result when output has been provided as a JsonArray (optional)
    private static boolean validate(String result, JsonArray expected) {
	JsonArray actual = new JsonParser().parse(result).getAsJsonArray();
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
}
