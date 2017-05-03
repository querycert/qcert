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

import java.io.FileReader;
import java.io.Reader;
import java.util.List;

import org.apache.asterix.lang.common.base.Statement;
import org.apache.asterix.lang.sqlpp.parser.SqlppParserFactory;

/**
 * A highly preliminary experiment in using a SQL++ parser instead of a SQL parser as a baby-step toward supporting SQL++ as a source
 *  language
 */
public class TestSQLPP {
	public static void main(String[] args) throws Exception {
		Reader input = new FileReader(args[0]);
		List<Statement> parsed = new SqlppParserFactory().createParser(input).parse();
		System.out.println(parsed);
	}
}
