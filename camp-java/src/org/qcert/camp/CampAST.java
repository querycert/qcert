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
import java.util.Map.Entry;

import org.qcert.camp.data.CampData;
import org.qcert.camp.pattern.BinaryOperator;

/**
 * Describes a node in the Rules/CAMP AST
 */
public abstract class CampAST {
	private static final CharSequence ENTRY_TAG = "datt";

	/** Utility emit method (generally called on the top node of the AST) */
	public final String emit() {
		StringWriter sw = new StringWriter();
		PrintWriter pw = new PrintWriter(sw);
		emit(pw);
		pw.close();
		return sw.toString();
	}

	/** General purpose emit node capable of writing any node to any PrintWriter and called
	 * recursively on an entire AST. 
	 * This implementation serves for almost all nodes, by having the nodes implement
	 *   getTag() and getOperands().  Overriding should be rare, but it done in a few cases.
	 * @param pw the PrintWriter to which to emit
	 */
	public void emit(PrintWriter pw) {
		pw.append("(");
		pw.append(getTag());
		for (Object op : getOperands()) {
			if (op instanceof CampAST)
				((CampAST) op).emit(pw.append(" "));
			else if (op instanceof String)
				pw.append(" \"").append((String) op).append("\"");
			else if (op instanceof BinaryOperator)
				pw.append(" (").append(String.valueOf(op)).append(")");
			else if (op instanceof Entry<?,?>) {
				@SuppressWarnings("unchecked")
				Entry<String, CampData> entry = (Entry<String, CampData>) op;
				pw.append("(").append(ENTRY_TAG).append(" \"").append(entry.getKey()).append("\" ");
				entry.getValue().emit(pw);
				pw.append(")");
			}
		}
		pw.append(")");
	}

	/**
	 * @return the operands for the s-expression form of this node (Strings and/or CampASTs)
	 */
	protected abstract Object[] getOperands();

	/**
	 * @return the s-expression tag for this node 
	 */
	protected abstract String getTag();
}
