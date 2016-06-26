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

import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.time.ZonedDateTime;

import org.qcert.runtime.Hierarchy;
import org.qcert.runtime.JavaQuery;

import com.google.gson.*;


public class JavaTestRunner {
	
	public static Object runQuery(JavaQuery query, String combinedInput) {
	    JsonElement jelement = new JsonParser().parse(combinedInput);
	    JsonObject  jobject = jelement.getAsJsonObject();
	    return runQuery(query, jobject);
	}

	public static Object runQuery(JavaQuery query, JsonObject combinedInput) {
		JsonArray hierarchy = combinedInput.getAsJsonArray("inheritance");
		JsonElement input = combinedInput.get("input");
		final ZonedDateTime now;
		JsonPrimitive primnow = combinedInput.getAsJsonPrimitive("now");
		if(primnow == null) {
			now = ZonedDateTime.now();
		} else {
  		        final String strnow = (String) (primnow.getAsString());
			now = ZonedDateTime.parse(strnow);
		}
		return runQuery(query, hierarchy, input, now);
	}


	public static Object runQuery(JavaQuery query, JsonArray hierarchy, JsonElement input, ZonedDateTime now) {
		return runQuery(query, new Hierarchy(hierarchy), input, now);
	}


	public static Object runQuery(JavaQuery query, Hierarchy hierarchy, JsonElement input, ZonedDateTime now) {
		return query.query(hierarchy, mkConstants(input, now));
	}

	private static JsonObject mkConstants(JsonElement input, ZonedDateTime now) {
	    JsonObject jsonObject = new JsonObject();
	    jsonObject.add("CONST$WORLD", input);
	    jsonObject.addProperty("CONST$NOW", now.toString());
	    return jsonObject;
	}

	private static void usage() {
		System.err.println("Java CAMP Runner expects two or three argument: a query class name, a filename,\nAnd an optional result file\n");

	}

	public static void main(String[] args) throws Exception {
		if(args.length != 2 && args.length != 3) {
			usage();
		}
		final String queryClassName = args[0];
		@SuppressWarnings("unchecked")
		final Class<JavaQuery> queryClass = (Class<JavaQuery>) Class.forName(queryClassName);
		final JavaQuery query = queryClass.newInstance();
		final String inputName = args[1];
		String combinedInput = new String(Files.readAllBytes(Paths.get(inputName)));
		Object output = runQuery(query, combinedInput);
		if (args.length == 3) {
		    PrintWriter pw = new PrintWriter(new File(args[2]));
		    pw.write(output.toString());
		    pw.close();
		} else {
		    System.out.println("The query returned: " + output);
		}
	}
}
