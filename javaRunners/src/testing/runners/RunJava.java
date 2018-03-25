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
import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;

import java.io.IOException;

/* The Q*cert runtime */
import org.qcert.runtime.Inheritance;
import org.qcert.runtime.JavaQuery;

/* GSON to import data */
import com.google.gson.*;


public class RunJava {
	
    // Small load-file method
    private static String readFile(String fileName) throws IOException {
	return new String(Files.readAllBytes(Paths.get(fileName)));
    }

    // Usage
    private static void usage() {
	System.err.println("Q*cert Java Runner expects one option:\n [-input filename] for the input data\nAnd the Java class name\n");
    }

    // Running the Query
    public static Object runQuery(JavaQuery query, String inputFile) {
	JsonElement jelement = new JsonParser().parse(inputFile);
	JsonObject  jobject = jelement.getAsJsonObject();
	return runQuery(query, jobject);
    }

    public static Object runQuery(JavaQuery query, JsonObject input) {
	/* Passes empty class inheritance for now */
	Inheritance emptyInheritance = new Inheritance(new JsonArray());
	return query.query(emptyInheritance, input);
    }

    // Main
    public static void main(String[] args) throws Exception {
	if(args.length != 3) {
	    usage();
	}
	String inputFile = null;
	String inputString = null;

	for (int i = 0; i < args.length; i++) {
	    String arg = args[i];
	    // Must have a -input option for the input JSON
	    if ("-input".equals(arg)) { inputFile = args[i+1]; i++; }
	    else {
		// Load input JSON
		if (inputFile != null) {
		    inputString = readFile(inputFile);
		} else {
		    throw new IllegalArgumentException("Input Data File Missing");
		}
		final String queryClassName = arg;
		@SuppressWarnings("unchecked")
		    final Class<JavaQuery> queryClass = (Class<JavaQuery>) Class.forName(queryClassName);
		final JavaQuery query = queryClass.newInstance();
		Object output = runQuery(query, inputString);
		System.out.println(output);
	    }
	}
    }
}
