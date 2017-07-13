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

package org.qcert.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Simple representation for S-expression, used to pass things back and forth between
 *  Java and Coq elements for testing.  This is used strictly for testing and is not
 *  an official part of the compiler. 
 */
public class SExpression {
	private final String nodeName;
	private final List<Object> children = new ArrayList<>();

	public SExpression(String nodeName, Object... children) {
		this.nodeName = nodeName;
		if (children.length > 0)
			this.children.addAll(Arrays.asList(children));
	}

	/**
	 * @return the children
	 */
	public List<Object> getChildren() {
		return children;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder bldr = new StringBuilder("(").append(nodeName);
		for (Object child : children)
			bldr.append(" ").append(child);
		return bldr.append(")").toString();
	}

	/**
	 * @return the nodeName
	 */
	public String getNodeName() {
		return nodeName;
	}
}
