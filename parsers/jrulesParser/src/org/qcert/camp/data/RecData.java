/**
 * Copyright (C) 2016-2017 Joshua Auerbach 
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

import java.util.Map;
import java.util.Map.Entry;

/**
 * Represents the drec data constructor
 * The empty collection is represented by a singleton field in CampData
 */
public class RecData extends CampData {
	private final Map<String, CampData> contents;

	public RecData(Map<String, CampData> contents) {
		this.contents = contents;
	}

	/**
	 * @return the contents
	 */
	public Map<String, CampData> getContents() {
		return contents;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.data.CampData#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.drec;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getOperands()
	 */
	@Override
	protected Object[] getOperands() {
		return contents.entrySet().toArray();
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "drec";
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder bldr = new StringBuilder("{");
		String delim = "";
		for (Entry<String,CampData> entry : contents.entrySet()) {
			bldr.append(delim).append(entry.getKey()).append("=").append(entry.getValue());
			delim = "; ";
		}
		return bldr.append("}").toString();
	}
}
