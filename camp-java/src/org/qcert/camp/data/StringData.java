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
package org.qcert.camp.data;

import java.io.PrintWriter;


/**
 * Represents the dstring data constructor
 */
public class StringData extends CampData {
	private final String value;

	public StringData(String value) {
		this.value = value;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#emit(java.io.PrintWriter)
	 */
	@Override
	public void emit(PrintWriter pw) {
		pw.append("\"").append(value).append("\"");
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.data.CampData#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.dstring;
	}

	/**
	 * @return the value
	 */
	public String getValue() {
		return value;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return value == null ? "null" : "\"" + value.toString() + "\""; 
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getOperands()
	 */
	@Override
	protected Object[] getOperands() {
		throw new IllegalStateException();  // emit is overridden, this should not be called
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		throw new IllegalStateException();  // emit is overridden, this should not be called
	}
}
