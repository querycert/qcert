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
 * Lexical fixup to get out of the morass caused by whether or not 'value' is a reserved word.  It IS a reserved word in SQL 92 and beyond,
 *   but it is used as a (non-delimited) identifier in TPC-H query 11 and Presto is willing to parse it as an identifier.  
 *   In SQL++, the word is always reserved, even though it is only significant when it follows 'select'.
 * In all other contexts, we delimit it using the SQL++ convention.
 */
public class FixupValueKeyword implements LexicalFixup {

	@Override
	public void apply(Iterator<Token> tokens, List<Token> output) {
		boolean sawSelect = false;
		while (tokens.hasNext()) {
			Token tok = tokens.next();
			if (tok.kind == SELECT) {
				sawSelect = true;
			} else if (tok.kind == VALUE) {
				if (!sawSelect) {
					tok.kind = IDENTIFIER;
					tok.image = "`value`";
				} else
					sawSelect = false;
			} else
				sawSelect = false;
			output.add(tok);
		}
	}
}
