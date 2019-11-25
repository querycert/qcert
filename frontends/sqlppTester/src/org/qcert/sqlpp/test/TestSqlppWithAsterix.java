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
package org.qcert.sqlpp.test;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.apache.asterix.common.utils.Servlets;
import org.apache.asterix.test.common.TestExecutor;
import org.apache.commons.io.IOUtils;

public class TestSqlppWithAsterix {

	public static void main(String[] args) throws Exception {
		if (args.length != 1) {
			System.err.println("One required arguments: a file containing valid SQL++ or DDL");
			return;
		}
		String query = readFile(args[0]);
		OpenTestExecutor executor = new OpenTestExecutor();
		InputStream answerStream = executor.executeQueryService(query, executor.getEndpoint(Servlets.QUERY_SERVICE));
		System.out.println("Result:");
        System.out.println(IOUtils.toString(answerStream, Charset.defaultCharset()));
	}

	private static String readFile(String fileName) throws IOException {
		return new String(Files.readAllBytes(Paths.get(fileName)));
	}
	
	private static class OpenTestExecutor extends TestExecutor {
		@Override
		public URI getEndpoint(String servlet) throws URISyntaxException {
			return super.getEndpoint(servlet);
		}
	}
}
