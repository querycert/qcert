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

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import org.apache.commons.collections.Bag;
import org.apache.commons.collections.bag.HashBag;

import java.util.Map;
import java.util.Map.Entry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Iterator;

import com.sun.nio.file.ExtendedCopyOption;

/**
 * Some utilities for managing compilation for the Spark backend
 */
public class Utils {
	/** Somewhat baked in relative name of the Scala jar to be submitted to spark */
	public static final String SCALA_JAR_NAME = "target/scala-2.10/nnrc-map-reduce_2.10-1.0.jar";

	/**
	 * @return true if running on windows
	 */
	public static boolean isWindows() {
		String os = System.getProperty("os.name");
		return os.startsWith("Windows");
	}

	/**
	 * Make the staging area for compiling to spark
	 * @param ruleName the name of the rule
	 * @param root the root of the staging area as a directory that may not exist but it's parent does
	 * @return the File representing the scala file to be generated (not yet existing)
	 * @throws IOException
	 */
	public static File makeSparkStagingArea(String ruleName, File root) throws IOException {
		root.mkdirs();
		File sbtFile = new File(root, "build.sbt");
		PrintWriter out = new PrintWriter(new FileWriter(sbtFile));
		out.println("name := \"NNRC Map-Reduce\"");
		out.println();
		out.println("version := \"1.0\"");
		out.println();
		out.println("scalaVersion := \"2.10.4\"");
		out.println();
		out.println("libraryDependencies += \"org.apache.spark\" %% \"spark-core\" % \"1.5.1\"");
		out.close();
		File src = new File(root, "src");
		src.mkdir();
		File main = new File(src, "main");
		main.mkdir();
		File scala = new File(main, "scala");
		scala.mkdir();
		return new File(scala, ruleName + ".scala");
	}

	/**
	 * Make the spark2 I/O file
	 * @param ruleName the name of the rule
	 * @param sioFile the name of the Spark2 I/O file to be produced
	 * @return void
	 * @throws IOException
	 */
        public static void makeSioFile(String ruleName, String ioFile, String outDir, Runner cadaRunner) throws IOException {
	    String flags = String.format("-dir %s", outDir);
	    System.out.printf("Running %s to generate Spark I/O file", cadaRunner.getProgramName());
	    String consoleOut = cadaRunner.runProgram(false, flags, ioFile);
	}

	/**
	 * Make the staging area for compiling to spark2
	 * @param ruleName the name of the rule
	 * @param root the root of the staging area as a directory that may not exist but it's parent does
	 * @return the File representing the scala file to be generated (not yet existing)
	 * @throws IOException
	 */
	public static File makeSpark2StagingArea(String ruleName, File root) throws IOException {
		root.mkdirs();
		File sbtFile = new File(root, "build.sbt");
		PrintWriter out = new PrintWriter(new FileWriter(sbtFile));
		out.println("scalaVersion := \"2.11.8\"");
		out.println();
		out.println("libraryDependencies += \"org.qcert\" %% \"qcert-spark2-runtime\" % \"0.1.0-SNAPSHOT\"");
		out.close();
		File src = new File(root, "src");
		src.mkdir();
		File main = new File(src, "main");
		main.mkdir();
		File scala = new File(main, "scala");
		scala.mkdir();
		return new File(scala, ruleName + ".scala");
	}

	/**
	 * Compile scala to produce a deployable jar
	 * @param rootdir the root of the staging area for the build (should be current when 'sbt package' is run)
	 */
	public static void scalaToJar(File rootdir) throws Exception {
		System.out.println("Running sbt to convert scala to jar");
		BasicLauncher launcher = new BasicLauncher(true, true, null);
		launcher.setCmd((isWindows() ? "sbt.bat" : "sbt") + " package");
		launcher.setWorkingDir(rootdir);
		launchAndTest(launcher, "sbt job");
	}

	public static void sbtRun(File root) throws Exception {
		System.out.println("Call sbt run in " + root);
		BasicLauncher launcher = new BasicLauncher(true, true, null);
		launcher.setCmd((isWindows() ? "sbt.bat" : "sbt") + " run");
		launcher.setWorkingDir(root);
		// launchAndTest(launcher, "sbt run");
		launcher.launch();
		System.out.println(new String(launcher.getStdOut()));
		System.err.println(new String(launcher.getStderr()));
	}

    public static String sbtRunSpark2(File root, String sioFileName) throws Exception {
		System.out.println("Call sbt run in " + root);
		String[] cmd = { (isWindows() ? "sbt.bat" : "sbt"), "run " + sioFileName };

		ArrayLauncher launcher = new ArrayLauncher(true, true, null); // Does not capture stderr
		launcher.setCmd(cmd);
		launcher.setWorkingDir(root);
		launcher.launch();
		String fullOut = new String(launcher.getStdOut());

		String[] lines = fullOut.split(System.getProperty("line.separator"));
		String result = "[{\"error\":nil}]";
		for (String line : lines) {
		    if (line.startsWith("[RESULT] [error]")) { line = line.replace("[RESULT] ",""); System.out.println(line); break; }
		    if (line.startsWith("[RESULT] ")) { result = line.replace("[RESULT] ",""); System.out.println("[RESULT] " + result); }
		}
		return result;
		// System.err.println(new String(launcher.getStderr()));
	}

	/**
	 * Launch a process and test its outout
	 * @param launcher the BasicLauncher all primed and ready to run
	 * @param forMsg a descriptive String to include in the failure message iff fails
	 */
	private static void launchAndTest(BasicLauncher launcher, String forMsg) throws Exception {
		int result = launcher.launch();
		if (result != 0) {
			System.out.println(new String(launcher.getStdOut()));
			System.err.println(new String(launcher.getStderr()));
			throw new IllegalStateException(forMsg + " failed with exit code " +  result);
		}
	}

	/**
	 * Flatten any embedded Json arrays into a one-level array
	 * @param toFlatten the JsonArray to flatten
	 * @param into the JsonArray we are flattening into
	 * @return the into argument for convenience
	 */
	private static JsonArray flatten(JsonArray toFlatten, JsonArray into) {
		for (JsonElement e : toFlatten.getAsJsonArray()) {
			if (e.isJsonArray())
				flatten((JsonArray) e, into);
			else
				into.add(e);
		}
		return into;
	}

	/**
	 * Given a JsonObject, return another that has the same "real" information but is canonical in terms of
	 * <ol><li>whether the type is called "type" (legacy CAMP project format) or "$class" (ODM format) and
	 * <li>whether the non-type portion of the object is enclosed in a "data" object (legacy CAMP project
	 *        format) or at the same level (ODM format)</ol>
	 * @param object the JsonObject
	 * @return the canonical form
	 */
	private static JsonObject canonicalize(JsonObject object) {
		JsonElement cls = object.get("$class");
		if (cls != null) {
			JsonObject data = new JsonObject();
			for (Entry<String, JsonElement> entry : object.entrySet()) {
				String name = entry.getKey();
				if (name.charAt(0) == '$') continue;
				data.add(name, entry.getValue());
			}
			JsonObject replacement = new JsonObject();
			JsonArray brands = new JsonArray();
			brands.add(cls);
			replacement.add("type", brands);
			replacement.add("data", data);
			return replacement;
		}
		return object;
	}

	/**
	 * Convert a JsonElement into something (Bag, Map, or self) that will give an accurate answer to the
	 *   equals() method, ignoring order
	 * @param element the element to convert
	 * @return the converted element
	 */
	private static Object makeComparable(JsonElement element) {
		if (element instanceof JsonObject) {
			JsonObject obj = canonicalize((JsonObject) element);
			Map<String,Object> result = new HashMap<>();
			for (Entry<String,JsonElement> entry : obj.entrySet()) {
				result.put(entry.getKey(), makeComparable(entry.getValue()));
			}
			return result;
		}
		if (element instanceof JsonArray) {
			JsonArray array = flatten((JsonArray) element, new JsonArray());
			Bag result = new HashBag();
			for (JsonElement e : array) {
				result.add(makeComparable(e));
			}
			return result;
		}
		// JsonNull and JsonPrimitive already have reasonable equality methods
		return element;
	}

	/**
	 * Compare two JsonArray objects for logical equality as part of validating a test
	 * @param expected the expected result
	 * @param actual the actual result
	 * @return true on successful comparison, false on failure
	 */
	public static boolean compareForValidity(JsonArray expected,
			JsonArray actual) {
		/* Compare the two */
		Object actualCompare = makeComparable(actual);
		Object expectedCompare = makeComparable(expected);
		if (actualCompare.equals(expectedCompare)) {
		    System.out.println("Success!  Expected and actual: " + actual);
		    return true;
		}
		System.out.println("Expected: " + expectedCompare);
		System.out.println("Actual: " + actualCompare);
                return false;
	}

	public static JsonObject parseJsonFileToObject(String ioFile) throws Exception {
		return new JsonParser().parse(new FileReader(ioFile)).getAsJsonObject();
	}

	public static JsonArray parseJsonFileToArray(String ioFile) throws Exception {
		return new JsonParser().parse(new FileReader(ioFile)).getAsJsonArray();
	}

	public static JsonElement parseJsonFileToElement(String inputFile) throws IOException {
		return new JsonParser().parse(new FileReader(inputFile));
	}

	/**
	 * Parse the I/O file, producing a JsonObject with three members (input, output, inheritance)
	 * @param ioFile the path name of the I/O file
	 * @return a JsonObject resulting from the parsing
	 */
	public static String loadIO(String inputFile, JsonElement[] output) throws IOException {
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
			if (input.has("output") && output != null)
				output[0] = input.get("output");
			// Let input contain just the input object
			if (input.has("input"))
				input = input.get("input").getAsJsonObject();
			// Assemble result
			return String.format("var world = %s;%nvar inheritance = %s;", input, inheritance);
		}
		throw new IllegalArgumentException("Input file does not have a recognized format");
	}

	/**
	 * Parse the schema file, producing a JsonObject with member inheritance
	 * @param schemaFile the path name of the schema file
	 * @return string defining the inheritance variable
	 */
	public static String loadSchema(String inputFile) throws IOException {
		JsonElement rawInput = new JsonParser().parse(new FileReader(inputFile));
		if (rawInput.isJsonObject()) {
			// All acceptable input formats are JSON objects
			JsonObject schema = rawInput.getAsJsonObject();
			// Attempt to obtain inheritance (else use empty array)
			JsonArray inheritance = null;
			if (schema.has("hierarchy"))
			    inheritance = schema.get("hierarchy").getAsJsonArray();
			else if (schema.has("inheritance"))
			    inheritance = schema.get("inheritance").getAsJsonArray();
			if (inheritance == null)
				inheritance = new JsonArray();
			// Assemble result
			return String.format("var inheritance = %s;", inheritance);
		}
		throw new IllegalArgumentException("Schema file does not have a recognized format");
	}


}
