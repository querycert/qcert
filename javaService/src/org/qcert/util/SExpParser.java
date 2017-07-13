/*
 * Copyright 2015-2016 IBM Corporation
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

package org.qcert.util;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.util.Stack;

/**
 * Parser for S-expression forms.   Strictly used for testing. 
 */
public class SExpParser {
	/**
	 * Parse the file named in the cmdline and display the result
	 */
	public static void main(String[] args) throws IOException {
		SExpression expr = parse(new File(args[0]));
		System.out.println(expr);
	}
	
	/**
	 * Parse the contents of a file
	 * @param file the file
	 * @return the SExpression
	 * @throws IOException
	 */
	public static SExpression parse(File file) throws IOException {
		return parse(new FileReader(file));
	}
	
	/**
	 * Parse the stream provided by a Reader
	 * @param rdr the Reader
	 * @return the SExpression
	 * @throws IOException
	 */
	public static SExpression parse(Reader rdr) throws IOException {
		Stack<SExpression> stack = new Stack<>();
		StreamTokenizer tokens = new StreamTokenizer(rdr);
		tokens.ordinaryChar('(');
		tokens.ordinaryChar(')');
		int tokenState = tokens.nextToken();
		tokens.wordChars('_', '_');
		while (tokenState != StreamTokenizer.TT_EOF) {
			switch (tokenState) {
			case '"':
				processValue(stack, String.format("\"%s\"", tokens.sval));
				break;
			case StreamTokenizer.TT_NUMBER:
				processValue(stack, formatNumber(tokens.nval));
				break;
			case StreamTokenizer.TT_WORD:
				throw new IllegalArgumentException(tokens.sval + " found in improper context");
			case '(':
				processStartExpression(tokens, stack);
				break;
			case ')':
				processEndExpression(stack);
				break;
			default:
				// do nothing
			}
			tokenState = tokens.nextToken();
		}
		assert stack.size() == 1;
		return stack.pop();
	}

	/**
	 * Format a number according to whether it looks like an integer or floating point
	 */
	private static String formatNumber(double number) {
		int rounded = (int) number;
		if (rounded == number)
			return String.format("%d", rounded);
		else
			return String.format("%f", number);
	}
	
	
	/**
	 * Parse the contents of a String
	 * @param input the input String
	 * @return the SExpression
	 * @throws IOException
	 */
	public static SExpression parse(String input) throws IOException {
		return parse(new StringReader(input));
	}

	/**
	 * Perform appropriate processing at close-paren
	 */
	private static void processEndExpression(Stack<SExpression> stack) {
		SExpression child = stack.pop();
		if (stack.isEmpty())
			stack.push(child);
		else
			stack.peek().getChildren().add(child);
	}

	/**
	 * Perform appropriate processing at open-paren
	 */
	private static void processStartExpression(StreamTokenizer tokens, Stack<SExpression> stack) throws IOException {
		int next = tokens.nextToken();
		if (next != StreamTokenizer.TT_WORD)
			throw new IllegalArgumentException("Identifier not found where expected");
		stack.push(new SExpression(tokens.sval));
	}

	/**
	 * Perform appropriate processing for a token (number or String literal) that is not an identifier or paren
	 */
	private static void processValue(Stack<SExpression> stack, String value) {
		stack.peek().getChildren().add(value);
	}
}	
