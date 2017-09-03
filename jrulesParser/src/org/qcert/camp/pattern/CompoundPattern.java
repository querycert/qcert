/**
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
package org.qcert.camp.pattern;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/** Represents a function composition of partially applied patterns (of signature pat->pat).  The CompoundPattern is itself such
 *   a pattern.  Other examples are LetItPattern and MapPattern.  The applyTo method does a complete evaluation of the composition
 *   applied to a final operand.
 */
public class CompoundPattern extends CampPattern {
	private final List<CampPattern> members;

	public CompoundPattern(CampPattern left, CampPattern right) {
		ArrayList<CampPattern> members = new ArrayList<>();
		if (left instanceof CompoundPattern)
			members.addAll(((CompoundPattern) left).members);
		else if (left.isFunction())
			members.add(left);
		else
			throw new IllegalArgumentException("First rule argument is not a function");
		if (right instanceof CompoundPattern)
			members.addAll(((CompoundPattern) right).members);
		else if (right.isFunction())
			members.add(right);
		else
			throw new IllegalArgumentException("Second rule argument is not a function");
		this.members = Collections.unmodifiableList(members);
	}

	
	@Override
	public CampPattern applyTo(CampPattern pattern) {
		List<CampPattern> toApply = new ArrayList<>(members);
		Collections.reverse(toApply);
		for (CampPattern next : toApply) {
			pattern = next.applyTo(pattern);
		}
		return pattern;
	}


	@Override
	public Kind getKind() {
		// A compound pattern has no 'kind' per se
		return null;
	}


	@Override
	public boolean isFunction() {
		return true;
	}

	@Override
	protected String getTag() {
		// Should never be called since no CompoundPattern should be emitted
		throw new IllegalStateException();
	}
}
