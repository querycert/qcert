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

import java.io.IOException;
import java.util.Map;

/**
 * Ancestor of JavaRunner and BinaryRunner
 */
public abstract class Runner {
	/** The environment (set in parent constructor or left null if PATH does not require alteration) */
	protected Map<String,String> env;
	/** The command template (with the right number of holes for the expected number of instantiating args) */
	protected String template;
	/** The name of the program for use in diagnostics */
	protected String progName;

	/**
	 * @return the progam name (for display)
	 */
	public String getProgramName() {
		return progName;
	}

	/**
	 * Run a programin our characteristic fashion against a particular input
	 * @param alwaysExceptionOnExit if program exits abnormally, throw an exception (otherwise, an exception is thrown in this case
	 *   only when there is no output, the assumption being that the content of the output is at least as informative as the exit code)
	 * @return the stdout output of an otherwise normal run (the caller must determine whether the
	 *   output is as expected)
	 * @throws IOException if an error occured launching the binary
	 * @throws IllegalStateException if the binary printed on stderr or returned an abnormal completion code
	 */
	public abstract String runProgram(boolean alwaysExceptionOnExit, String... args) throws IOException;
}
