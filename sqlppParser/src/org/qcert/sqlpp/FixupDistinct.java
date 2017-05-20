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
package org.qcert.sqlpp;

import java.util.Iterator;
import java.util.List;

import org.apache.asterix.lang.sqlpp.parser.Token;

/**
 * This fixup elides the 'distinct' keyword except when it follows 'select', which allows TPC-H query 16 to be parsed.
 * The 'distinct' keyword is second-class in both SQL and SQL++.  In SQL, among other uses, it can appear
 * in aggregating functions, making those functions operate only on distinct values.  This is explicitly stated
 * to be "not supported" in SQL++.  In SQL++, 'distinct' is only supported as a keyword when it follows 'select'.
 * Strictly speaking, if we want to support SQL-style aggregation functions like count and sum, we need to pass through
 * the 'distinct' flag.  However, our Presto parser does not do this, so, simply eliding the keyword makes both encoders
 * behaviorally equivalent.  The s-exp parsing on the OCaml side does not expect or handle this flag.  Perhaps the semantics
 * that we currently assume are incorrect for bags that are not sets, for which the flag would matter.
 */
public class FixupDistinct implements LexicalFixup {

	@Override
	public void apply(Iterator<Token> tokens, List<Token> output) {
		boolean sawSelect = false;
		while (tokens.hasNext()) {
			Token tok = tokens.next();
			if (tok.kind == SELECT) {
				sawSelect = true;
			} else if (tok.kind == DISTINCT && !sawSelect)
				continue;
			else
				sawSelect = false;
			output.add(tok);
		}
	}
	
}
