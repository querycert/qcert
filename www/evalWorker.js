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

// Code designed to run as an asynchronous "web worker" to do evaluation of queries compiled to Javascript.
// We isolate the code in a worker to avoid hanging the UI, since we have no idea how long evaluation will take or
// even whether it will terminate.  The master thread containing the UI should have a kill button in case evaluation 
// is going on too long.

// Put all the harness functions at global scope so they are available to the query
importScripts("../runtime/javascript/qcert-merged-runtime.js");

// Here upon receiving the input text, schema text, compiled query (in string form) from the main thread
onmessage = function(e) {
	// Unpack the arguments
	var inputText = e.data[0];
	var schemaText = e.data[1];
	var compiledQuery = e.data[2];

	// Convert input text to an object
	var io = JSON.parse(inputText);
	
	// Find input in an 'io' object or else the object simply IS the input
	var input = ("input" in io) ? io.input : io;
	
	// Convert the schema
	var schema = JSON.parse(schemaText);
	
	// Put inhertance at global scope so the evaluated query can see it
	inheritance = ("hierarchy" in schema) ? schema.hierarchy
			: ("inheritance" in schema) ? schema.inheritance : [];
	
	// Evaluate the query as a string, producing the function 'query' at global scope
	eval(compiledQuery);
	
	// Run the actual query against the input (and 'inheritance')   This is what could potentially take a LONG time
	var result = query(input);
	
	// Build the output display, including the output comparison if called for.
	var prefix = "";
	if ("output" in io)
		prefix = verify(result, io.output) ? "Equal to the expected result:\n"
				: "Differs from expected result:\n";
	var result = prefix + JSON.stringify(result);

	// Send the result back
	postMessage(result);
	
	// Each spawned worker is designed to be used once
	close();
}
