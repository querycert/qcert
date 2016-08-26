/**
 * Copyright (C) 2016 Joshua Auerbach 
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
package org.qcert.camp.compiler;

import java.io.File;

import org.qcert.camp.rule.CampRule;

/**
 * Utilities to Compile Rule/CAMP ASTs into CAMP, NRAenv etc., either by forking a process
 *   to run the CACo or CAEv binaries or by using the CACoEngine API.
 */
public class CompileUtil {
	private CompileUtil() {}
	
	/**
	 * Run a CampRule AST through the CACo binary with output in a particular directory
	 * TODO how to specify the various parameters.
	 * @param outDir the output directory
	 * @param input the input AST
	 */
	public static void runCACo(File outDir, CampRule input) {
		
	}
}
