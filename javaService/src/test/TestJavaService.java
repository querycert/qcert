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
package test;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Base64;
import java.util.List;
import java.util.logging.Level;

import org.apache.commons.logging.LogFactory;
import org.apache.commons.logging.impl.Jdk14Logger;
import org.apache.http.HttpEntity;
import org.apache.http.HttpResponse;
import org.apache.http.HttpStatus;
import org.apache.http.client.HttpClient;
import org.apache.http.client.methods.HttpPost;
import org.apache.http.client.protocol.ResponseProcessCookies;
import org.apache.http.entity.StringEntity;
import org.apache.http.impl.client.HttpClients;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

/**
 * Just a test that we are able to communicate with the Java service at localhost or AWS instance, port 9879
 */
public class TestJavaService {
	private static final String REMOTE_LOC = "35.164.159.76";

	/**
	 * Main.  The cmdline arguments either do or don't contain the flag -remote: those are the only supported flags.  
	 * If -remote is specified, we test code on the AWS instance using the "server" protocol.  
	 * If -remote is not specified, we test code running locallly using the "server" protocol.
	 * The first non-flag argument is the "verb", which (currently) should be one of the verbs set at the top of source file
	 *   org.qcert.javasrc.Dispatcher.  Remaining non-flag arguments are file names.  There must be at least one.  The number of such 
	 *   arguments and what they should contain depends on the verb.
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		/* Parse command line */
		List<String> files = new ArrayList<>();
		String loc = "localhost", verb = null;
		for (String arg : args) {
			if (arg.equals("-remote"))
				loc = REMOTE_LOC;
			else if (arg.startsWith("-"))
				illegal();
			else if (verb == null)
				verb = arg;
			else 
				files.add(arg);
		}
		/* Simple consistency checks and verb-specific parsing */
		if (files.size() == 0)
			illegal();
		String file = files.remove(0);
		String schema = null;
		switch (verb) {
		case "parseSQL":
		case "serialRule2CAMP":
		case "sqlSchema2JSON":
			if (files.size() != 0)
				illegal();
			break;
		case "techRule2CAMP":
			if (files.size() != 1)
				illegal();
			schema = files.get(0);
			break;
		case "csv2JSON":
			if (files.size() < 1)
				illegal();
			break;
		default:
			illegal();
		}

		/* Assemble information from arguments */
		String url = String.format("http://%s:9879?verb=%s", loc, verb);
		byte[] contents = Files.readAllBytes(Paths.get(file));
		String toSend;
		if ("serialRule2CAMP".equals(verb))
			toSend = Base64.getEncoder().encodeToString(contents);
		else
			toSend = new String(contents);
		if ("techRule2CAMP".equals(verb))
			toSend = makeSpecialJson(toSend, schema);
		else if ("csv2JSON".equals(verb))
			toSend = makeSpecialJson(toSend, files);
		HttpClient client = HttpClients.createDefault();
		HttpPost post = new HttpPost(url);
		StringEntity entity;
    entity = new StringEntity(toSend);
    entity.setContentType("text/plain");
		post.setEntity(entity);
		HttpResponse resp = client.execute(post);
		int code = resp.getStatusLine().getStatusCode();
		if (code == HttpStatus.SC_OK) {
			HttpEntity answer = resp.getEntity();
			InputStream s = answer.getContent();
			BufferedReader rdr = new BufferedReader(new InputStreamReader(s));
			String line = rdr.readLine();
			while (line != null) {
				System.out.println(line);
				line = rdr.readLine();
			}
			rdr.close();
			s.close();
		} else
			System.out.println(resp.getStatusLine());
	}

	/** Indicates basic error on command line */
	private static void illegal() {
		System.out.println("Illegal syntax or wrong arguments for verb");
		System.exit(-1);
	}

	/**
	 * Make the special JSON encoding with both a schema and some number of CSV files must be provided
	 * TODO at present there is no way to send "format" or "delimiter" members
	 * @param schemaString a String containing the JSON schema
	 * @param files the list of file names which are to be read to obtain CSV and whose names are to be decomposed to
	 *   form type (table) names
	 * @return the JSON encoding to send
	 * @throws IOException 
	 */
	private static String makeSpecialJson(String schemaString, List<String> files) throws IOException {
		JsonObject result = new JsonObject();
		JsonObject schema = new JsonParser().parse(schemaString).getAsJsonObject();
		result.add("schema", schema);
		JsonObject data = new JsonObject();
		result.add("data", data);
		for (String file : files) {
			Path path = Paths.get(file);
			String csv = new String(Files.readAllBytes(path));
			String table = path.getFileName().toString();
			if (table.endsWith(".csv"))
				table = table.substring(0, table.length() - 4);
			data.add(table, new JsonPrimitive(csv));
		}
		return result.toString();
	}

	/**
	 * Make the special JSON encoding when both source and schema must be provided
	 * @param source the source string
	 * @param schemaFile the file containing the schema
	 * @return the string containing both as a JSON object
	 * @throws IOException 
	 */
	private static String makeSpecialJson(String source, String schemaFile) throws IOException {
		/* This is done using GSON rather than naive string operations to avoid issues with embedded quotes */
		JsonObject result = new JsonObject();
		result.add("source", new JsonPrimitive(source));
		JsonObject schema = new JsonParser().parse(new FileReader(schemaFile)).getAsJsonObject();
		result.add("schema", schema);
		return result.toString();
	}
}
