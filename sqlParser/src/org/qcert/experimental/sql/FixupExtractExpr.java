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
package org.qcert.experimental.sql;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.asterix.lang.sqlpp.parser.Token;

/**
 * Lexical fixup for expressions of the form extract(<unit> from <expr>).  If <unit> is one of year, month or day, we use the builtin
 * AsterixDB functions get_year, get_month, or get_day instead with the single argument <expr>.
 */
public class FixupExtractExpr implements LexicalFixup {

	/* (non-Javadoc)
	 * @see org.qcert.experimental.sql.LexicalFixup#apply(java.util.List)
	 */
	@Override
	public List<Token> apply(List<Token> inputList) {
		List<Token> output = new ArrayList<>();
		Iterator<Token> tokens = inputList.iterator();
		while (tokens.hasNext()) {
			Token tok = tokens.next();
			if (tok.image.equalsIgnoreCase("extract")) {
				int index = 0;
				Token[] pattern = new Token[5];
				while (index < 5 && tokens.hasNext())
					pattern[index++] = tokens.next();
				if (index == 5 && pattern[0].kind == LEFTPAREN && pattern[4].kind == RIGHTPAREN && pattern[2].kind == FROM) {
					String functionName;
					switch (LexicalFixup.getUnit(pattern[1])) {
					case D:
						functionName = "get_day";
						break;
					case M:
						functionName = "get_month";
						break;
					case Y:
						functionName = "get_year";
						break;
					default:
						functionName = null;
						break;
					}
					if (functionName != null) {
						Token function = LexicalFixup.makeToken(IDENTIFIER, functionName, tok.beginLine, tok.beginColumn, tok.endLine, 
								tok.beginColumn + functionName.length());
						output.add(function);
						output.add(pattern[0]); // (
						output.add(pattern[3]); // <expr>
						output.add(pattern[4]); // )
						continue;
					}
				}
				// Here if we fail to match the expected pattern
				output.add(tok);
				for (Token pat : pattern) {
					if (pat == null)
						break;
					output.add(pat);
				}
			} else
				output.add(tok);
		}
		return output;
	}

	public Unit getUnit(Token possible) {
		return null;
	}
}
