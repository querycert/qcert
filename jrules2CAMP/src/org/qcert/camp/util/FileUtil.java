/**
 * Copyright (C) 2016 Joshua Auerbach 
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
package org.qcert.camp.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

/**
 * Trivial file utilities
 */
public class FileUtil {
	/**
	 * Read text from a file into a String
	 * @param srcFile the input file
	 */
	public static String readFile(File srcFile) throws IOException {
		StringWriter swtr = new StringWriter();
		PrintWriter wtr = new PrintWriter(swtr);
		FileReader frdr = new FileReader(srcFile);
		BufferedReader rdr = new BufferedReader(frdr);
		String line = rdr.readLine();
		while (line != null) {
			wtr.println(line);
			line = rdr.readLine();
		}
		rdr.close();
		wtr.close();
		return swtr.toString();
	}

	/**
	 * Read a file as a list of lines
	 * @param file the file
	 * @return the list
	 * @throws Exception
	 */
	public static List<String> readLinesAsList(File file) throws Exception {
		List<String> ans = new ArrayList<>();
		FileReader frdr = new FileReader(file);
		BufferedReader rdr = new BufferedReader(frdr);
		String line = rdr.readLine();
		while (line != null) {
			ans.add(line);
			line = rdr.readLine();
		}
		rdr.close();
		return ans;
	}

	/**
	 * Write text to a file
	 * @param file the file
	 * @param text the text to write
	 */
	public static void writeFile(File file, String text) throws IOException {
		PrintWriter wtr = new PrintWriter(new FileWriter(file));
		wtr.println(text);
		wtr.close();
	}

}
