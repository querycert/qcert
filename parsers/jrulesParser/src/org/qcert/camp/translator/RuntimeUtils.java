/**
 * (c) Copyright IBM Corp. 2015-2017
 * Copyright (C) 2017 Joshua Auerbach 
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
package org.qcert.camp.translator;

import java.util.Collections;
import java.util.List;

/** Some utility functions used as support at runtime by code that the jrules2coq translator generates */
public class RuntimeUtils {
	/**
	 * Utility function called from the ODM runtime to sort and format a list of strings in a consistent way
	 * @param ls the list
	 * @return the formatted result
	 */
	public static String stringListToString(List<String> ls) {
		Collections.sort(ls);
		return ls.toString();
	}
}
