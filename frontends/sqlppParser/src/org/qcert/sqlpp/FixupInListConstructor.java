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
 * Lexical fixup for the construct 'in (.., .., ...)'.  In standard SQL, 'in' is a special operator and its resulting expression has a 
 *   rhs that is either something that can produce a bag or list in standard SQL (like a query) or a static list constructed in that 
 *   special way with parentheses.  In contrast, in SQL++, 'in' is an ordinary binary operator and there is a generalized list constructor
 *   that can appear in any expression context.  That constructor uses square brackets rather than parens.  So, if a parenthesized list
 *   follows 'in', we change the parens to square brackets.  It is not safe to make this transformation in other contexts since, in standard 
 *   SQL, list construction is not general.
 */
public class FixupInListConstructor implements LexicalFixup {

	@Override
	public void apply(Iterator<Token> tokens, List<Token> output) {
		while (tokens.hasNext()) {
			List<Token> accum = new ArrayList<>();
			Token tok = tokens.next();
			accum.add(tok);
			if (tok.kind == IN && tokens.hasNext()) {
				Token start = tokens.next();
				accum.add(start);
				if (start.kind == LEFTPAREN && tokens.hasNext()) {
					/* Get a list of tokens terminated by close paren; if this fails, bail */
					List<Token> listBalance = LexicalFixup.getExprAndClose(tokens, accum, RIGHTPAREN);
					if (listBalance == null) {
						output.addAll(accum);
						return;
					}
					/* See if the list contains a comma at top level */ 
					if (LexicalFixup.hasTopLevel(listBalance, COMMA)) {
						/* Looks enough like the kind of list we want, so proceed */
						start.kind = LEFTBRACKET;
						start.image = "[";
						Token end = listBalance.get(listBalance.size() - 1);
						end.kind = RIGHTBRACKET;
						end.image = "]";
					}
					/* In any case, put the tokens we are holding back */
					output.add(tok);
					output.add(start);
					output.addAll(listBalance);
				} else {
					output.add(tok);
					output.add(start);
				}
			} else
				output.add(tok);
		}
	}
}
