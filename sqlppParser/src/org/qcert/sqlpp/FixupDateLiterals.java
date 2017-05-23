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
 * A lexical fixup to change occurances of 'date <string-literal>' to date(<string-literal>).  The former follows the SQL "generic typed literal"
 * convention, is recognized by Presto, and used by TPC-H.  The latter is a functional equivalent that is recognized by AsterixDB SQL++ (the generic typed literal
 * syntax is not).
 */
public class FixupDateLiterals implements LexicalFixup {

	@Override
	public void apply(Iterator<Token> tokens, List<Token> output) {
		while (tokens.hasNext()) {
			Token tok = tokens.next();
			if (tokens.hasNext() && tok.image.equalsIgnoreCase("date")) {
				Token next1 = tokens.next();
				if (next1.kind == STRING_LITERAL) {
					assert next1.beginLine > tok.endLine || next1.beginColumn > tok.endColumn + 1 : "No room to safely insert left paren";
					Token next2 = tokens.hasNext() ? tokens.next() : null;
					assert next2 == null || next2.beginLine > next1.endLine || next2.beginColumn > next1.endColumn + 1 : 
						"No room to safely insert right paren";
					output.add(tok);
					output.add(LexicalFixup.makeToken(LEFTPAREN, "(", tok.endLine, tok.endColumn + 1));
					output.add(next1);
					output.add(LexicalFixup.makeToken(RIGHTPAREN, ")", next1.endLine, next1.endColumn + 1));
					if (next2 != null)
						output.add(next2);
				} else {
					output.add(tok);
					output.add(next1);
				}
			} else
				output.add(tok);
		}
	}
}
