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

import java.io.FileReader;

import org.apache.asterix.lang.sqlpp.parser.JavaCharStream;
import org.apache.asterix.lang.sqlpp.parser.SQLPPParserConstants;
import org.apache.asterix.lang.sqlpp.parser.SQLPPParserTokenManager;
import org.apache.asterix.lang.sqlpp.parser.Token;

public class TestLexer {
	public static void main(String[] args) throws Exception {
		String nl = String.format("%n");
		SQLPPParserTokenManager lexer = new SQLPPParserTokenManager(new JavaCharStream(new FileReader(args[0])));
		int line = 1;
		int col = 0;
		StringBuilder output = new StringBuilder();
		Token tok = lexer.getNextToken();
		while (tok != null && tok.kind != SQLPPParserConstants.EOF) {
			int nextLine = tok.beginLine;
			int nextCol = tok.beginColumn;
			while (nextLine > line) {
				output.append(nl);
				line++;
				col = 0;
			}
			line = tok.endLine;
			while (nextCol > col+1) {
				output.append(" ");
				col++;
			}
			col = tok.endColumn;
			output.append(tok.image);
			tok = lexer.getNextToken();
		}
		System.out.println(output);
	}
}
