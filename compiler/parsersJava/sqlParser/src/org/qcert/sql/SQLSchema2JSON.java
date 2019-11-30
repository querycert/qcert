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
package org.qcert.sql;

import java.io.StringWriter;
import java.util.List;

import org.qcert.javasvc.Command;

import com.facebook.presto.sql.tree.Statement;
import com.google.gson.JsonObject;
import com.google.gson.internal.Streams;
import com.google.gson.stream.JsonWriter;

/**
 * Java service command for converting SQL schema into JSON form for use by other parts of qcert
 */
public class SQLSchema2JSON implements Command {
	@Override
	public String invoke(String arg) {
		try {
			List<Statement> stmts = PrestoEncoder.parse(arg);
			JsonObject ans = SchemaTransformer.convertSchemas(stmts);
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
