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
package org.qcert.camp.pattern;

import org.qcert.camp.data.CampData;
import org.qcert.camp.data.FloatData;
import org.qcert.camp.data.NatData;
import org.qcert.camp.data.StringData;

/**
 * Represents a CAMP Constant pattern
 */
public final class ConstPattern extends CampPattern {
	private final CampData data;

	/**
	 * Make a new PatternConst
	 * @param data the CampData for the represented constant
	 */
	public ConstPattern(CampData data) {
		this.data = data;
	}

	/** Convenience constructor for integral constants */
	public ConstPattern(long value) {
		this(new NatData(value));
	}
	
	/** Convenience constructor for the family of "simple" types (Java wrapper types plus String and null) */
	public ConstPattern(Object value) {
		this(convertToCampData(value));
	}
	
	/** Convenience constructor for String constants */
	public ConstPattern(String value) {
		this(new StringData(value));
	}

	/**
	 * @return the data
	 */
	public CampData getData() {
		return data;
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.pattern.CampPattern#getKind()
	 */
	@Override
	public Kind getKind() {
		return Kind.pconst;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return data.toString();
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getOperands()
	 */
	@Override
	protected Object[] getOperands() {
		return new Object[] {data};
	}

	/* (non-Javadoc)
	 * @see org.qcert.camp.CampAST#getTag()
	 */
	@Override
	protected String getTag() {
		return "Pconst";
	}

	private static CampData convertToCampData(Object value) {
		if (value == null)
			return CampData.NULL;
		switch (value.getClass().getName()) {
		case "java.lang.Byte":
		case "java.lang.Short":
		case "java.lang.Integer":
		case "java.lang.Long":
			return new NatData(((Number) value).longValue());
		case "java.lang.Float":
		case "java.lang.Double":
			return new FloatData(((Number) value).doubleValue());
		case "java.lang.Boolean":
			return ((Boolean) value).booleanValue() ? CampData.TRUE : CampData.FALSE;
		case "java.lang.Character":
		case "java.lang.String":
			return new StringData(value.toString());
		default:
			throw new IllegalArgumentException("Can't construct CampData representation for type " + value.getClass().getName());
		}
	}
}
