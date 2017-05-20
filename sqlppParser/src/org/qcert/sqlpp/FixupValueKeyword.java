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
 *   but it is used as an identifier in TPC-H query 11 and Presto is willing to parse it as an identifier.  In SQL++, the word is always
 *   reserved.  The speculation is that it only needs to be reserved when following the keyword 'select' and so this fixup makes it
 *   into an identifier in all other contexts.
 * Kluge alert: this practice is highly questionable and is only here to avoid modifying query 11 in place.  It seems to me that value
 *   should NOT be used as an identifier even if it is correct in standard SQL.
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
					tok.image = "valu_";
				} else
					sawSelect = false;
			} else
				sawSelect = false;
			output.add(tok);
		}
	}

	public List<Token> getExprAndClose(Iterator<Token> tokens, List<Token> accum, int closeTokenKind) {
		return null;
	}
}
