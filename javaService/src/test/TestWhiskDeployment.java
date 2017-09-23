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
package test;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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
import org.qcert.javasvc.FrontAction;

import com.google.gson.JsonObject;

/**
 * Test a whisk deployment of a two-action sequence (FrontAction with a Java runtime, followed by QcertJS with a Node runtime).
 * This should provide function equivalent to the qcert command line or the equivalent done through the demo UI.
 * Not all capabilities are tested, but we should be able to compile and evaluate from all legal source languages to all legal targets,
 * supplying schema and input where required in all legal formats.
 * Also permits local testing of the FrontAction in isolation.
 */
public class TestWhiskDeployment {
	/** The default URL when the -url flag is not used */
	private static final String URL_DEFAULT = // TODO this default is highly temporary 
			"https://openwhisk.ng.bluemix.net/api/v1/web/JoshAuerbachThoughts_test/qcert/qcert.json";

	/**
	 * Main.  
	 * <p>The cmdline args must include a filename for the file containing the query.  All other arguments are flags, often followed by
	 *   single String arguments, and are optional.
	 * <ul>
	 * <li><b>-url</b> followed by the whisk URL to use for the request.  
	 *     Defaults to the deployment of the service in Josh Auerbach's testing namespace.
	 *     Illegal if <b>-local</b> is also specified.
	 * <li><b>-local</b> (not followed by an argument) means that only the FrontAction is tested and it is tested by direct invocation.  
	 *     The <b>-url</b> argument is illegal with this and the default URL is ignored because there is no network activity at all.
	 * <li><b>-source</b> followed by the name of the source language.  If omitted, the source language will be inferred from the suffix 
	 *    of the file containing the query.  It is an error if the option is omitted <em>and</em> the inference fails.  
	 *    E.g. if there is SQL source in a file whose suffix isn't <b>.sql</b> you could specify <b>'-source SQL'</b>
	 * <li><b>-target</b> followed by the name of the target language.  Defaults to JS
	 * <li><b>-schema</b> followed by a filename.  Supplies the schema, which is read from the file.  The format may be either SQL or our 
	 *    JSON format.
	 * <li><b>-input</b> followed by a filename.  Supplies the input, which is read from the file.  The format may be either our standard 
	 *    JSON format or our special JSON format for holding tabular data (normally, this is generated internal to the demo).  
	 *    The presence of input also turns on the <b>-eval</b> option in the request, but this will only produce a meaningful result if the 
	 *    target language can be evaluated by the compilation tool (for example, JavaScript cannot)
	 *  </ul>
	 */
	public static void main(String[] args) throws Exception {
		/* Parse arguments */
		String url = null, source = null, target = null, query = null, schema = null, input = null;
		boolean urlSeen = false, sourceSeen = false, targetSeen = false, schemaSeen = false, inputSeen = false;
		boolean local = false;
		for (String arg : args) {
			if (arg.charAt(0) == '-') {
				switch (arg) {
				case "-url": urlSeen = true; break;
				case "-source": sourceSeen = true; break;
				case "-target": targetSeen = true; break;
				case "-schema": schemaSeen = true; break;
				case "-input": inputSeen = true; break;
				case "-local": local = true; break;
				default:
					error("Bad flag: " + arg);
				}
			} else if (urlSeen) {
				urlSeen = false;
				url = checkAndAssign(arg, url, "url");
			} else if (sourceSeen) {
				sourceSeen = false;
				source = checkAndAssign(arg, source, "source");
			} else if (targetSeen) {
				targetSeen = false;
				target = checkAndAssign(arg, target, "target");
			} else if (schemaSeen) {
				schemaSeen = false;
				schema = checkAndAssign(arg, schema, "schema");
			} else if (inputSeen) {
				inputSeen = false;
				input = checkAndAssign(arg, input, "input");
			} else
				query = checkAndAssign(arg, query, null);
		}
		
		/* Check for adequate arguments, apply defaults */
		if (query == null)
			error("No query file specified");
		if (source == null) {
			source = sourceLanguageFromFile(query);
			if (source == null) {
				error("Source language not specified and could not be inferred from file name");
			}
		}
		if (url == null)
			url = URL_DEFAULT;
		else if (local)
			error("Cannot specify a URL with -local");
		if (target == null)
			target = "JS";
		
		/* Build the appropriate JSON structure for POST or for local invocation */
		JsonObject toPost = new JsonObject();
		toPost.addProperty("query", readFile(query));
		toPost.addProperty("source", source);
		toPost.addProperty("target", target);
		if (schema != null)
			toPost.addProperty("schema", readFile(schema));
		if (schema != null)
			toPost.addProperty("schema", readFile(schema));
		if (input != null) {
			toPost.addProperty("input", readFile(input));
			toPost.addProperty("eval", true);
		}
		
		/* Perform the post or local invocation */
		if (local) {
			System.out.println(FrontAction.main(toPost));
			return;
		}
		HttpResponse resp = post(toPost, url);
		
		/* Display the result of a POST, which can include "soft" (remotely detected) errors.  "Hard" errors (like a failure to perform the 
		 * POST at all) cause exceptions.
		 */
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

	/**
	 * Check that an argument isn't a duplicate, return it if not
	 * @param arg the argument
	 * @param oldval the current value of the field to which it is to be assigned (should be null)
	 * @param context the name of a flag argument or null to indicate the main (non-flag) argument
	 * @return arg
	 * @throws IllegalArgumentException for duplicates
	 */
	private static String checkAndAssign(String arg, String oldval, String context) {
		if (oldval == null)
			return arg;
		if (context != null)
			throw new IllegalArgumentException("Duplicate flag argument for " + context);
		throw new IllegalArgumentException("Duplicate query source file " + arg);
	}

	/**
	 * Convenient shortcut for error throwing
	 */
	private static void error(String msg) {
		throw new IllegalArgumentException(msg);
	}

	/**
	 * Perform a POST using REST conventions compatible with whisk
	 * @param toPost the JSON object to post
	 * @param url the URL to which it should be posted
	 * @return an HttpResponse containing the response
	 * @throws Exception
	 */
	private static HttpResponse post(JsonObject toPost, String url) throws Exception {
		HttpClient client = HttpClients.createDefault();
		HttpPost post = new HttpPost(url);
		/* Responses from whisk can include cookies which are rejected by the HTTP client; this is a warning-level event only,
		 * and we suppress it here to avoid distraction. */
		((Jdk14Logger) LogFactory.getLog(ResponseProcessCookies.class)).getLogger().setLevel(Level.SEVERE);
		StringEntity entity = new StringEntity(toPost.toString());
		entity.setContentType("application/json");
		post.setEntity(entity);
		return client.execute(post);
	}

	/**
	 * Trivial file reader
	 */
	private static String readFile(String fileName) throws IOException {
		Path filePath = Paths.get(fileName);
		return new String(Files.readAllBytes(filePath));
	}

	/**
	 * Attempt to infer a source language from the extension portion of a file name
	 * @param fileName the file name
	 * @return the source language tag or null if none could be inferred
	 */
	private static String sourceLanguageFromFile(String fileName) {
		String simpleName = Paths.get(fileName).getFileName().toString();
		int lastDot = simpleName.lastIndexOf('.');
		if (lastDot < 0)
			return null;
		String ext = simpleName.substring(lastDot + 1);
		switch (ext) {
		/* TODO Being lazy here.  Fill in cases as we need them.  Otherwise, specify the -source flag */
		case "sql": return "SQL";
		case "oql": return "OQL";
		default:
			return null;
		}
		
	}
}
