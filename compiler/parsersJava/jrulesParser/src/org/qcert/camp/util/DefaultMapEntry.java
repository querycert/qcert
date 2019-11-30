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
package org.qcert.camp.util;

import java.util.Map.Entry;

/**
 * Replacement for apache commons method we used to get from ODM dependencies
 */
public class DefaultMapEntry<T1, T2> extends Pair<T1, T2> implements Entry<T1, T2> {
	public DefaultMapEntry(T1 a, T2 b) {
		super(a, b);
		}

	/* (non-Javadoc)
	 * @see java.util.Map.Entry#getKey()
	 */
	@Override
	public T1 getKey() {
		return a();
	}

	/* (non-Javadoc)
	 * @see java.util.Map.Entry#getValue()
	 */
	@Override
	public T2 getValue() {
		return b();
	}

	/* (non-Javadoc)
	 * @see java.util.Map.Entry#setValue(java.lang.Object)
	 */
	@Override
	public T2 setValue(T2 value) {
		throw new UnsupportedOperationException();
	}
}
