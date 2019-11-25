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
 * A lexical fixup to change occurances of 'interval <string-literal> <unit>' where the unit may be 'day' 'month' or 'year' to the functional form
 *   'duration(<ISO-duration-string-literal>)'.  The former is recognized by Presto and used in TPC-H.  The latter is the equivalent recognized by
 *    AsterixDB SQL++ (which does not recognized the former).  Note that the AsterixDB data model supports both durations and "intervals" but the semantics
 *    here called for a duration, NOT an interval (which is specified by two points in time).  ISO also calls this a duration.
 */
public class FixupIntervalLiterals implements LexicalFixup {
	@Override
	public void apply(Iterator<Token> tokens, List<Token> output) {
		while (tokens.hasNext()) {
			Token tok = tokens.next();
			if (tokens.hasNext() && tok.image.equalsIgnoreCase("interval")) {
				Token next1 = tokens.next();
				if (next1.kind == STRING_LITERAL && tokens.hasNext()) {
					int count;
					try {
						count = Integer.parseInt(next1.image.substring(1, next1.image.length() - 1));
					} catch (NumberFormatException e) {
						output.add(tok);
						output.add(next1);
						continue;
					}
					Token next2 = tokens.next();
					Unit unit = LexicalFixup.getUnit(next2);
					if (unit == null) {
						output.add(tok);
						output.add(next1);
						output.add(next2);
						continue;
					}
					tok.image = "duration"; // handily, this takes up the same amount of room as "interval"
					output.add(tok);
					output.add(LexicalFixup.makeToken(LEFTPAREN, "(", tok.endLine, tok.endColumn + 1));
					String ISOduration = String.format("\"P%d%s\"", count, unit);
					Token lit = LexicalFixup.makeToken(STRING_LITERAL, ISOduration, tok.endLine, tok.endColumn + 1, tok.endLine, tok.endColumn + 1 + ISOduration.length());
					output.add(lit);
					output.add(LexicalFixup.makeToken(RIGHTPAREN, ")", lit.endLine, lit.endColumn + 1));
					elideParenNum(tokens, output);
				} else {
					output.add(tok);
					output.add(next1);
				}
			} else
				output.add(tok);
		}
	};

	/** Elide a parenthesized int literal if the next three tokens consist of it.  This was found to be necessary using Presto
	 * with TPC-H query 1.  It is unclear what the parenthesized number is supposed to denote.  It does not appear to be standard
	 * SQL.  It might even be a bug in the TPC template.  We are just taking a path of least resistance here rather than investigating
	 * further.
	 * @param tokens the tokens interator
	 * @param output the output List being assembled
	 */
	private void elideParenNum(Iterator<Token> tokens, List<Token> output) {
		if (!tokens.hasNext())
			return;
		Token first = tokens.next();
		if (first.kind != LEFTPAREN || !tokens.hasNext()) {
			output.add(first);
			return;
		}
		Token second = tokens.next();
		if (second.kind != INTEGER_LITERAL || !tokens.hasNext()) {
			output.add(first);
			output.add(second);
			return;
		}
		Token third = tokens.next();
		if (third.kind == RIGHTPAREN)
			return; // elided
		// Not elided
		output.add(first);
		output.add(second);
		output.add(third);
	}
}
