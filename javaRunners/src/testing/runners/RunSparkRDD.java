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

import java.util.List;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.io.FileReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.PrintWriter;
import java.io.StringWriter;

import java.util.Map;
import java.util.Map.Entry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Iterator;

import java.lang.reflect.Type;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

import org.apache.commons.collections.Bag;
import org.apache.commons.collections.bag.HashBag;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import com.google.gson.reflect.TypeToken;

import org.junit.Assert;

public class RunSparkRDD {
	/** Name of the property turns off paranoid behavior of Array.sort */
	private static final String LEGACY_MERGE_SORT = "java.util.Arrays.useLegacyMergeSort";

	/** Template for submitting to spark */
	private static final String SPARK_SUBMIT_TEMPLATE = "%s --class %s --master local[2] " +
			"--driver-java-options -D" + LEGACY_MERGE_SORT + "=true %s %s %s %s";

	// Small load-file method
	private static String readFile(String fileName) throws IOException {
		return new String(Files.readAllBytes(Paths.get(fileName)));
	}

	// Usage
	private static void usage() {
		System.err.println("Q*cert Javascript Runner expects two options:\n [-runtime filename] for the Q*cert Javscript runtime\n [-input filename] for the input data\nAnd the Javascript file\n");
	}

	/**
	 * Get the I/O file in the old format 
	 * @param ioFile the File to put the old format into
	 * @param io the JsonObject containing the parsed new format I/O file
	 * @return the name of the I/O file, having generated it
	 * @throws Exception
	 */
	private static String createOldFormatIoFile(File ioFile, JsonObject io) throws Exception {
		PrintWriter wtr = new PrintWriter(new FileWriter(ioFile));
		wtr.format("var inheritance = %s;%n", io.get("schema").getAsJsonObject().get("inheritance"));
		wtr.format("var input = %s;%n", io.get("input").getAsJsonObject().get("WORLD"));
		wtr.format("var output = %s;%n", io.get("output"));
		wtr.close();
		return ioFile.getAbsolutePath();
	}

	/**
	 * Run a spark end-to-end test by submitting a jar (at a known path from the root of a spark staging area)
	 * @param root the root of the spark staging area for a particular test
	 * @param className the classname of the rule
	 * @param ruleName the name of the rule (used to generate I/O file name for Qcert case)
	 */
        private static void runSpark(File root, String ioFile, String className, String ruleName, String runtime) throws Exception {
		System.out.println("Submitting job to spark");
		String jar = new File(root, QUtil.SCALA_JAR_NAME).getAbsolutePath();
		Map<String, String> env = new HashMap<>(System.getenv());
		String cmd = QUtil.isWindows() ? "spark-submit.cmd" : "spark-submit";
		JsonObject io = QUtil.parseJsonFileToObject(ioFile);
		String ioString = createOldFormatIoFile(new File(root, "iofile"), io);
		String resultFile = new File(root, "execution.results").getAbsolutePath();
		String submitted = String.format(SPARK_SUBMIT_TEMPLATE, cmd, className, jar, runtime, ioFile, resultFile);
		System.out.println(submitted);
		BasicLauncher launcher = new BasicLauncher(true, true, null);
		launcher.setCmd(submitted);
		launcher.setEnv(env);
		int result = launcher.launch();
		String output = new String(launcher.getStdOut());
		System.out.println(output);
		String stderr = new String(launcher.getStderr());
		if (result != 0) {
			System.err.println(stderr);
			throw new RunnerException("Spark execution exit code = " + result, output, stderr);
		}
		JsonArray expected = io.get("output").getAsJsonArray();
 		validate(QUtil.parseJsonFileToArray(resultFile).toString(), expected);
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
				QIO qio = null;
				if (inputFile != null) {
				    qio = new QIO(null, inputFile, null);
				} else {
					throw new IllegalArgumentException("Input Data File Missing");
				}
				// Load Q*cert Javascript runtime
				if (runtimeFile != null) {
					engine.eval(readFile(runtimeFile));
				} else {
					throw new IllegalArgumentException("Runtime File Missing");
				}
				JsonElement output = (qio.getOutput())[0];
				String funCall = QUtil.jsFunFromQIO(qio);
				engine.eval(funCall);
				engine.eval(new java.io.FileReader(arg));
				// Evaluate the compiler query + stringify the result
				engine.eval("var result = JSON.stringify(query(world));");
				// Get the result
				String result = (String) engine.get("result");
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
}
