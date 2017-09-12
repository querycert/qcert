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
package org.qcert.javasvc;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

public class WhiskMain extends Dispatcher {
	public static JsonObject main(JsonObject args) {
        String verb = args.has("verb") ? args.getAsJsonPrimitive("verb").getAsString() : null;
        String arg = args.has("arg") ? args.getAsJsonPrimitive("arg").getAsString() : null;
        JsonObject response = new JsonObject();
        if (verb == null || arg == null)
        	response.add("error", analyzeError(verb, arg));
        else
        	response.add("response", new JsonPrimitive(dispatch(verb, arg)));
        return response;
    }

	private static JsonElement analyzeError(String verb, String arg) {
		String msg;
		if (verb == null && arg == null)
			msg = "No verb or argument supplied to whisk service";
		else if (verb == null)
			msg = "A missing verb with argument " + arg + " was illegally passed to the whisk service";
		else
			msg = "The verb " + verb + " with no argument was illegally passed to the whisk servicee";
		return new JsonPrimitive(msg);
	}
}
