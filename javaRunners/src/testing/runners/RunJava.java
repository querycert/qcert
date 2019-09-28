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

/* Q*cert Java runtime */
import org.qcert.runtime.Inheritance;
import org.qcert.runtime.JavaQuery;
import org.qcert.runtime.BinaryOperators;

public class RunJava {

    // Small load-file method
    private static String readFile(String fileName) throws IOException {
	return new String(Files.readAllBytes(Paths.get(fileName)));
    }

    // Usage
    private static void usage() {
	System.err.println("Q*cert Javascript Runner requires the option -input or -io, and the Java class name.\n"+
			   "Options:\n"+
			   " [-io filename] a JSON object containing the input data, the schema and the expected output\n"+
			   " [-input filename] the input data\n"+
			   " [-schema filename] the schema\n"+
			   " [-output filename] the expected output\n");
    }

    // Running the Query
    public static JsonElement runQuery(JavaQuery query, QIO qio) {
	/* Passes empty class inheritance for now */
	Inheritance inheritance = new Inheritance(qio.getInheritance());
	return query.query(inheritance, qio.getInput());
    }

    // Main
    public static void main(String[] args) throws Exception {
	if(args.length < 3) {
	    usage();
	}

	String ioFile = null;
	String inputFile = null;
	String inputString = null;
	String schemaFile = null;
	String outputFile = null;
	for (int i = 0; i < args.length; i++) {
	    String arg = args[i];
	    // Must have a -input option for the input JSON
	    if ("-io".equals(arg)) { ioFile = args[i+1]; i++; }
	    else if ("-input".equals(arg)) { inputFile = args[i+1]; i++; }
	    else if ("-schema".equals(arg)) { schemaFile = args[i+1]; i++; }
	    else if ("-output".equals(arg)) { outputFile = args[i+1]; i++; }
	    else {
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
		final String queryClassName = arg;
		@SuppressWarnings("unchecked")
		    final Class<JavaQuery> queryClass = (Class<JavaQuery>) Class.forName(queryClassName);
		final JavaQuery query = queryClass.newInstance();
		JsonElement result = runQuery(query, qio);
		// Validate the result
		if (output == null) {
		    // Print the result
		    System.out.println(result);
		} else {
		    Boolean valid = BinaryOperators.equals(result, output).getAsBoolean();
		    if (valid) {
			System.out.println("["+arg+" java] OK");
		    } else {
			System.out.println("["+arg+" java] ERROR");
			System.out.println("Actual:");
			System.out.println(result);
			System.out.println("Expected:");
			System.out.println(output);
      System.exit(1);
		    }
		}
	    }
	}
    }
}
