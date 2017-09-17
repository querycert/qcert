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

/**
 * This is the source to a Whisk web action wrapper for the JavaService.  Assuming it is built using the 'export' ant script in this
 * project and packaged as qcertJavaWhiskAction.jar, then it can be deployed using the command
 * 
 * wsk action create|update qcertJavaService qcertJavaWhiskAction.jar --main org.qcert.javasvc.WhiskMain --web true|false
 * 
 * If --web true, the deployment is a web action that does not require an authenticated user and its execution is charged to the
 * deployer.  If --web false, the deployment creates an ordinary whisk action that does require a valid authorization token to be
 * called and is suitable for being integrated into a wider graph of whisk actions.
 */
public class WhiskMain extends Dispatcher {
	public static JsonObject main(JsonObject args) {
        String verb = args.has("verb") ? args.getAsJsonPrimitive("verb").getAsString() : null;
        String arg = args.has("arg") ? args.getAsJsonPrimitive("arg").getAsString() : null;
        JsonObject response = new JsonObject();
        if (verb == null || arg == null)
        	response.add("error", analyzeError(verb, arg, args));
        else
        	response.add("response", new JsonPrimitive(dispatch(verb, arg)));
        return response;
    }

	private static JsonElement analyzeError(String verb, String arg, JsonObject args) {
		String msg;
		if (verb == null && arg == null)
			msg = "No verb or argument; instead: " + args.toString();
		else if (verb == null)
			msg = "A missing verb with argument " + arg + " was illegally passed to the whisk service";
		else
			msg = "The verb " + verb + " with no argument was illegally passed to the whisk servicee";
		return new JsonPrimitive(msg);
	}
}
