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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.asterix.lang.sqlpp.parser.Token;

/**
 * Convert the construct 'substring(<expr1> from <expr2> for <expr3>)' into equivalent builtin function-call form 
 * substr(<expr1>, <expr2>, <expr>3).  I gather the sugared form is accepted in SQL but not in SQL++.  But, the
 * built-in function is also assumed by Presto, whose parser does this conversion also.
 */
public class FixupSubstring implements LexicalFixup {

	@Override
	public void apply(Iterator<Token> tokens, List<Token> output) {
		while (tokens.hasNext()) {
			Token tok = tokens.next();
			if (tok.image.equalsIgnoreCase("substring") && tokens.hasNext()) {
				Token open = tokens.next();
				if (open.kind == LEFTPAREN && tokens.hasNext()) {
					List<Token> accum = new ArrayList<>();
					accum.add(tok);
					accum.add(open);
					List<Token> expr1 = LexicalFixup.getExprAndClose(tokens, accum, FROM);
					if (expr1 != null) {
						Token from = expr1.remove(expr1.size() - 1);
						List<Token> expr2 = LexicalFixup.getExprAndClose(tokens, accum, FOR);
						if (expr2 != null) {
							Token forTok = expr2.remove(expr2.size() - 1);
							List<Token> expr3 = LexicalFixup.getExprAndClose(tokens, accum, RIGHTPAREN);
							if (expr3 != null) {
								tok.image = "substr";
								output.add(tok);
								output.add(open);
								output.addAll(expr1);
								from.kind = COMMA;
								from.image = ",";
								output.add(from);
								output.addAll(expr2);
								forTok.kind = COMMA;
								forTok.image = ",";
								output.add(forTok);
								output.addAll(expr3);
								continue;
							}
						}
					}
					// Something in the pattern failed to match
					output.addAll(accum);
				} else {
					output.add(tok);
					output.add(open);
				}
			} else
				output.add(tok);
		}
	}
}
