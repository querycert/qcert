// Uses JavaScript engine that ships with jdk e.g.,
// http://docs.oracle.com/javase/7/docs/technotes/guides/scripting/programmer_guide/
package testing.runners;

/* Standard Libraries */
import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;

import java.io.IOException;

/* Nashorn Javascript Libraries */
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

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
		// Load input JSON
		if (inputFile != null) {
		    String funCall = "var world = " + readFile(inputFile) + ";";
		    engine.eval(funCall);
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
	    }
	}
    }
}
