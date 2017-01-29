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
import java.nio.file.Paths;
import java.util.Base64;

import org.apache.http.HttpEntity;
import org.apache.http.HttpResponse;
import org.apache.http.HttpStatus;
import org.apache.http.client.HttpClient;
import org.apache.http.client.methods.HttpPost;
import org.apache.http.entity.StringEntity;
import org.apache.http.impl.client.HttpClients;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

/**
 * Just a test that we are able to communicate with the Java service at localhost or AWS instance, port 9879.
 */
public class TestJavaService {
	private static final String REMOTE_LOC = "35.164.159.76";

	/**
	 * Main.  The cmdline arguments either do or don't contain the flag -remote: that's the only supported flag.  If it is specified,
	 *   we test code on the AWS instance.  If it is not, we test code running locally.
	 * The first non-flag argument is the "verb", which (currently) should be one of the verbs set at the top of source file
	 *   org.qcert.javasrc.Main.  The second non-flag argument is a file containing source to send to the server.
	 *   The third non-flag argument, if present, is a file containing the schema to send to the server.  The third argument
	 *   is ignored unless the verb is one that requires it, in which case it is required.
	 * All other arguments and argument forms are illegal.
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		/* Parse command line */
		String file = null, loc = "localhost", verb = null, schema = null;
		for (String arg : args) {
			if (arg.equals("-remote"))
				loc = REMOTE_LOC;
			else if (arg.startsWith("-"))
				illegal();
			else if (verb == null)
				verb = arg;
			else if (file == null)
				file = arg;
			else if (schema == null)
				schema = arg;
			else
				illegal();
		}
		/* Simple consistency checks */
		if (verb == null || file == null)
			illegal();
		if (needsSchema(verb)) {
			if (schema == null)
				illegal();
		} else if (schema != null)
			illegal();
		/* Assemble information from arguments */
		String url = String.format("http://%s:9879?verb=%s", loc, verb);
		byte[] contents = Files.readAllBytes(Paths.get(file));
		String toSend;
		if (needsEncoding(verb))
			toSend = Base64.getEncoder().encodeToString(contents);
		else
			toSend = new String(contents);
		if (needsSchema(verb))
			toSend = makeSpecialJson(toSend, schema);
		HttpClient client = HttpClients.createDefault();
		HttpPost post = new HttpPost(url);
		StringEntity entity = new StringEntity(toSend);
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

	/** Determines if a given verb needs base64 encoding of its file contents (currently true only of serialRule2CAMP) */
	private static boolean needsEncoding(String verb) {
		return "serialRule2CAMP".equals(verb);
	}

	/** Determines if a given verb needs a schema (currently true only of techRule2CAMP) */
	private static boolean needsSchema(String verb) {
		return "techRule2CAMP".equals(verb);
	}
}
