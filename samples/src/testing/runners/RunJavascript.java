// Uses JavaScript engine that ships with jdk e.g.,
// http://docs.oracle.com/javase/7/docs/technotes/guides/scripting/programmer_guide/
package testing.runners;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

public class RunJavascript {
  public static void main(String[] args) throws Exception {
    ScriptEngineManager factory = new ScriptEngineManager();
    ScriptEngine engine = factory.getEngineByName("JavaScript");
    for (final String arg : args) {
      engine.put(ScriptEngine.FILENAME, arg);
      engine.eval(new java.io.FileReader(arg));
    }
  }
}
