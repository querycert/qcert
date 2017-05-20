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
 * Lexical fixup for expressions of the form extract(<unit> from <expr>).  If <unit> is one of year, month or day, we use the builtin
 * AsterixDB functions get_year, get_month, or get_day instead with the single argument <expr>.  Note that <expr> can consist of
 * multiple tokens.  We make the simplifying assumption that parenthesis matching will suffice to find the end.  That might not
 * be foolproof.
 */
public class FixupExtractExpr implements LexicalFixup {
	@Override
	public void apply(Iterator<Token> tokens, List<Token> output) {
		while (tokens.hasNext()) {
			List<Token> accum = new ArrayList<>();
			Token tok = tokens.next();
			accum.add(tok);
			if (tok.image.equalsIgnoreCase("extract") && tokens.hasNext()) {
				Token maybeOpen = tokens.next();
				accum.add(maybeOpen);
				if (maybeOpen.kind == LEFTPAREN && tokens.hasNext()) {
					Token maybeUnit = tokens.next();
					accum.add(maybeUnit);
					Unit unit = LexicalFixup.getUnit(maybeUnit);
					if (unit != null) {
						Token maybeFrom = tokens.next();
						accum.add(maybeFrom);
						if (maybeFrom.kind == FROM) {
							List<Token> exprAndClose = LexicalFixup.getExprAndClose(tokens, accum, RIGHTPAREN);
							if (exprAndClose != null) {
								String functionName;
								switch (unit) {
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
									throw new IllegalStateException();
								}
								Token function = LexicalFixup.makeToken(IDENTIFIER, functionName, tok.beginLine, tok.beginColumn, tok.endLine, 
										tok.beginColumn + functionName.length());
								output.add(function);
								output.add(maybeOpen);
								output.addAll(exprAndClose);
								continue;
							}
						}
					}
				}
			}
			// Here on failure to match pattern
			for (Token restore : accum)
				output.add(restore);
		}
	}
}
