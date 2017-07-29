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

/** 
 * An exception thrown whenever a BinaryRunner detects failure of any kind.
 * Encapsulates the stdout and stderr of the failed process
 */
public class RunnerException extends RuntimeException {
	private static final long serialVersionUID = 1L;
	private final String stdout;
	private final String stderr;
	
	/**
	 * Make a new RunnerException
	 * @param stdout contents of stdout
	 * @param stderr contents of stderr
	 */
	public RunnerException(String message, String stdout, String stderr) {
		super(message);
		this.stdout = stdout;
		this.stderr = stderr;
	}

	/**
	 * @return the stderr
	 */
	public String getStderr() {
		return stderr;
	}

	/**
	 * @return the stdout
	 */
	public String getStdout() {
		return stdout;
	}
}
