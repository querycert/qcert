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
 * Lack of support for 
 *    count(distinct X)
 * (etc) is an explicit limitation of SQL++ in terms of its SQL compatibility.
 * 
 * The present fixup is a kluge.  It works because (1) in SQL++, 'distinct' is not allowed except following a 'select', and (2)
 *    our Presto-based code is not currently passing along the 'distinct' flag on a function call and our S-expression
 *    parser for SQL inside qcert wouldn't know what to do with it anyway.
 * I think a more correct handling, to be substituted once we are no longer trying to imitate what the Presto parser does, would be that
 *     count(distinct X)
 * becomes
 *     count((select distinct value foo from X))
 * That should work because subqueries are just expressions in SQL++, a from clause may iterate over any expression.
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
