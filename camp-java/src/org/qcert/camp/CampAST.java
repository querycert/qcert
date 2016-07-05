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
package org.qcert.camp;

import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * Describes a node in the Rules/CAMP AST
 */
public abstract class CampAST {
	/** Utility emit method (generally called on the top node of the AST) */
	public String emit() {
		StringWriter sw = new StringWriter();
		PrintWriter pw = new PrintWriter(sw);
		emit(pw);
		pw.close();
		return sw.toString();
	}

	/** General purpose emit node capable of writing to any PrintWriter */
	public abstract void emit(PrintWriter pw);
}
