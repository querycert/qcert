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

import java.util.Arrays;
import java.util.List;

import org.apache.asterix.lang.sqlpp.parser.SQLPPParserConstants;
import org.apache.asterix.lang.sqlpp.parser.Token;

/**
 * Represents a single lexical fixup.  The interface also provides the list of fixups to be applied.
 *
 */
public interface LexicalFixup extends SQLPPParserConstants {
	public List<LexicalFixup> list = Arrays.asList(
			new FixupDateLiterals(),
			new FixupIntervalLiterals()
			// Add more fixups here
	);

	/** Apply this fixup.  The resulting list of tokens should have reasonable line and column assignments based on the originals so that restoring the linear text form 
	 *  is possible
	 * @param tokens the list of tokens before the fixup
	 * @return the fixed up list of tokens
	 */
	public List<Token> apply(List<Token> tokens);
	
	/**
	 * Augments the Token constructor with settings for begin/end line/column
	 * @param kind the kind
	 * @param image the image
	 * @param beginLine the beginning line
	 * @param beginColumn the beginning column
	 * @param endLine the ending line
	 * @param endColumn the ending column
	 * @return the new Token
	 */
	public static Token makeToken(int kind, String image, int beginLine, int beginColumn, int endLine, int endColumn) {
		Token ans = new Token(kind, image);
		ans.beginLine = beginLine;
		ans.beginColumn = beginColumn;
		ans.endLine = endLine;
		ans.endColumn = endColumn;
		return ans;
	}
	
	/**
	 *  A variant of makeToken that assumes a single character image so that the begin/end line/column are the same
	 * @param kind the kind
	 * @param image the image
	 * @param line the beginning and ending line
	 * @param column the beginning and ending column
	 * @return the new Token
	 */
	public static Token makeToken(int kind, String image, int line, int column) {
		return makeToken(kind, image, line, column, line, column);
	}
}
