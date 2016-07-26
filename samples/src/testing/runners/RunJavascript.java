// Uses JavaScript engine that ships with jdk e.g.,
// http://docs.oracle.com/javase/7/docs/technotes/guides/scripting/programmer_guide/
package testing.runners;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

public class RunJavascript {

    // Small load-file utility
    private static String readFile(String fileName) throws IOException {
	BufferedReader br = new BufferedReader(new FileReader(fileName));
	try {
	    StringBuilder sb = new StringBuilder();
	    String line = br.readLine();
	    
	    while (line != null) {
		sb.append(line);
		sb.append("\n");
		line = br.readLine();
	    }
	    return sb.toString();
	} finally {
	    br.close();
	}
    }

    public static void main(String[] args) throws Exception {
	ScriptEngineManager factory = new ScriptEngineManager();
	ScriptEngine engine = factory.getEngineByName("JavaScript");
	
	String ioFile = null;
	String runtimeFile = null;
	
	for (int i = 0; i < args.length; i++) {
	    String arg = args[i];
	    // Must have a -io option for the input JSON
	    if ("-io".equals(arg)) { ioFile = args[i+1]; i++; }
	    // Must have a -runtime option for the Q*cert Javascript runtime
	    else if ("-runtime".equals(arg)) { runtimeFile = args[i+1]; i++; }
	    else {
		// Load input JSON
		if (ioFile != null) {
		    String funCall = "var world = " + readFile(ioFile) + ";";
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
