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
package org.qcert.camp.translator;

import java.io.StringReader;

import org.qcert.camp.pattern.CampPattern;
import org.qcert.javasvc.Command;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

/**
 * Implement Java Service command for converting a technical rule (ie, an "ARL file") to CAMP
 */
public class TechRule2CAMP implements Command {
	@Override
	public String invoke(String arg) {
		try {
			StringReader rdr = new StringReader(arg);
			JsonObject input = new JsonParser().parse(rdr).getAsJsonObject();
			JsonElement schema = input.get("schema");
			rdr = new StringReader(input.get("source").getAsString());
			ODMFrontEnd frontEnd = new ODMFrontEnd(rdr, null, schema);
			SemRule2CAMP semRule2Camp = new SemRule2CAMP(frontEnd.getFactory());
			CampPattern translated = semRule2Camp.translate(frontEnd.getRule()).convertToPattern();
			return translated.emit();
		} catch (Exception e) {
			return "ERROR: " + e.getMessage() + ", while parsing " + arg;
		}
	}
}
