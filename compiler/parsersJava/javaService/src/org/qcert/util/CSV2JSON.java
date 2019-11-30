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
package org.qcert.util;

import java.io.StringWriter;
import java.lang.reflect.Field;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.commons.csv.CSVFormat;
import org.qcert.javasvc.Command;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.internal.Streams;
import com.google.gson.stream.JsonWriter;

/**
 * JavaService command to turn a set of CSVs plus a schema into valid JSON-format input
 * The input to this service is itself a JSON object, containing required "schema" and "data" members and optional
 * "format" and "delimiter" members.
 */
public class CSV2JSON implements Command {
	@Override
	public String invoke(String arg) {
		try {
			JsonObject input = new JsonParser().parse(arg).getAsJsonObject();
			JsonElement schema = input.get("schema");
			JsonObject data = input.get("data").getAsJsonObject();
			String formatName = input.has("format") ? input.get("format").getAsString() : "RFC4180";
			Field formatField = CSVFormat.class.getField(formatName);
			CSVFormat format = (CSVFormat) formatField.get(null);
			if (input.has("delimiter")) {
				String delimiter = input.get("delimiter").getAsString();
				format = format.withDelimiter(delimiter.charAt(0));
			}
			// TODO we could support more format details in this way or support deserializing an entire CSVFormat object
			Map<String, String> tableMap = new LinkedHashMap<>();
			for (Entry<String, JsonElement> entry : data.entrySet()) {
				tableMap.put(entry.getKey(), entry.getValue().getAsString());
			}
			JsonObject ans = DataLoader.loadData(tableMap, schema, format);
			StringWriter wtr = new StringWriter();
			JsonWriter json = new JsonWriter(wtr);
			json.setLenient(true);
			json.setIndent("  ");
			Streams.write(ans, json);
			json.close();
			return wtr.toString();
		} catch (Throwable t) {
			return "ERROR: " + t.getMessage();
		}
	}
}