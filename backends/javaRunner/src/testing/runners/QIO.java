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
package testing.runners;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

/** Content of I/O files
 */
public class QIO {

    JsonObject _schema;
    JsonArray _inheritance;
    JsonElement[] _output;
    JsonObject _input;

    /**
     * Parse the I/O file containing schema, input and output in JSON
     * @param ioFile the path to the I/O file
     * @return a QIO object
     */
    QIO(String ioFile) throws IOException {
	JsonElement rawIo = new JsonParser().parse(new FileReader(ioFile));
	if (rawIo.isJsonObject()) {
	    // All acceptable input formats are JSON objects
	    JsonObject io = rawIo.getAsJsonObject();
	    // Attempt to obtain inheritance (else use empty array)
	    if (io.has("schema")) {
		_schema = io.get("schema").getAsJsonObject();
		if (_schema.has("inheritance"))
		    _inheritance = _schema.get("inheritance").getAsJsonArray();
	    }
	    if (_inheritance == null)
		_inheritance = new JsonArray();
	    // Attempt to obtain output (else leave output argument as is)
	    _output = new JsonElement[1];
	    if (io.has("output")) {
		_output[0]= io.get("output");
	    }
	    // Let input contain just the input object
	    if (io.has("input"))
		_input = io.get("input").getAsJsonObject();
	}
    }

    /**
     * Parse the files containing schema, input and output in JSON
     * @param schemaFile the path to the schema file
     * @param inputFile the path to the input file
     * @param outputFile the path to the output file
     * @return a QIO object
     */
    QIO(String schemaFile, String inputFile, String outputFile) throws IOException {
	if (inputFile == null) throw new IllegalArgumentException("Must have input file");
	// Set the input
	JsonElement rawInput = new JsonParser().parse(new FileReader(inputFile));
	_input = rawInput.getAsJsonObject();
	// Set the schema and inheritance
	if (schemaFile != null) {
	    JsonElement rawSchema = new JsonParser().parse(new FileReader(schemaFile));
	    _schema = rawSchema.getAsJsonObject();
	    if (_schema.has("inheritance"))
		_inheritance = _schema.get("inheritance").getAsJsonArray();
	}
	if (_inheritance == null)
	    _inheritance = new JsonArray();
	// Set the output
	_output = new JsonElement[1];
	if (outputFile != null) {
	    JsonElement rawOutput = new JsonParser().parse(new FileReader(outputFile));
	    _output[0]= rawOutput;
	}
    }

    // Return schema
    public JsonObject getSchema() {
	return _schema;
    }
	
    // Return inheritance derivation
    public JsonArray getInheritance() {
	return _inheritance;
    }
	
    // Return expected output
    public JsonElement[] getOutput() {
	return _output;
    }
	
    // Return input
    public JsonObject getInput() {
	return _input;
    }
}
