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
			Token tok = tokens.next();
			if (tok.kind == IN && tokens.hasNext()) {
				Token start = tokens.next();
				if (start.kind == LEFTPAREN && tokens.hasNext()) {
					/* Get a list, but only if it looks like a real list (with comma separators) */
					List<Token> list = new ArrayList<>();
					Token end = getList(tokens, list);
					if (end != null) {
						start.kind = LEFTBRACKET;
						start.image = "[";
						end.kind = RIGHTBRACKET;
						end.image = "]";
					}						
					// Both for success and failure, we flush all the tokens we have			
					output.add(tok);
					output.add(start);
					output.addAll(list);
					if (end != null)
						output.add(end);
					continue;
				} else {
					output.add(tok);
					output.add(start);
					continue;
				}
			} else
				output.add(tok);
		}
	}

	/**
	 * Subroutine to get a list of tokens that form a valid paren-seperated list of expressions
	 * @param tokens the Token stream in its current state (with 'in (' havin already been consumed)
	 * @param list a list in which to put either the list contents (on success) or Tokens to be passed through (on failure)
	 * @return the close paren token on success or null on failure
	 */
	private Token getList(Iterator<Token> tokens, List<Token> list) {
		// TODO It is actually impractical to check whether this is really a valid list without building an actual AST with knowledge of the
		// grammar.  Most generally, the elements of the list can themselves be arbitrary expressions containing parentheses and commas.  
		// Here we accept only lists whose elements are literals or identifiers (single tokens).  That way, we succeed in the most common
		// case and at least do no extra harm in the more exotic cases.  I'm not actually sure what standard SQL accepts as list elements
		// anyway (since it isn't a truly expression-oriented language).
		boolean testing = true;
		Token current = null;
		Token last = null;
		while (testing) {
			current = tokens.next();
			switch (current.kind) {
			case IDENTIFIER:
			case INTEGER_LITERAL:
			case STRING_LITERAL:
			case DOUBLE_LITERAL:
			case FLOAT_LITERAL:
				list.add(current);
				current = tokens.next();
				testing = current.kind == COMMA;
				if (testing)
					list.add(current);
				else
					last = current;
				break;
			default:
				list.add(current);
				testing = false;
			}
		}
		return (last != null && last.kind == RIGHTPAREN) ? last : null;
	}
}
