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

// Get dependencies.  We put our merged runtime functions at global scope so they are available to the query
importScripts("../../runtimes/javascript/qcert-runtime.js", "qcertWhiskDispatch.js", "../../bin/qcertJS.js");

// Here upon receiving the activation message from the main thread.  This has two possible forms.
// 1.  An array of Strings containing inputText, schemaText, and compiledQuery (requesting Javascript execution).
// 2.  A QcertCompilerConfig containing invocation arguments for qcert (requesting evaluation of an intermediate language).
onmessage = function(e) {
	console.log("Web worker entered") ;
	console.log(e);
	// Execute according to what is requested
	if (Array.isArray(e.data))
		jsEval(e.data);
	else
		qcertEval(e.data);
}

// qcert intermediate language evaluation
function qcertEval(inputConfig) {
	console.log("qcertEval chosen");
	var handler = function(result) {
		console.log("Compiler returned");
		console.log(result);
		postMessage(result.eval);
		console.log("reply message posted");

		// Each spawned worker is designed to be used once
		close();
	}
	qcertWhiskDispatch(inputConfig, handler);
}

// Javascript evaluation
function jsEval(args) {
	console.log("jsEval chosen");

	// Unpack the arguments
	var inputText = args[0];
	var schemaText = args[1];
	var compiledQuery = args[2];

	// Convert input text to an object
	var io = JSON.parse(inputText);
	
	// Find input in an 'io' object or else the object simply IS the input
	var input = ("input" in io) ? io.input : io;
	
	// Convert the schema
	var schema = schemaText.length > 0 ? JSON.parse(schemaText) : {};
	
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

function verify(result, expected) {
	result = result[0]; // TODO is this always right?  
	if (result.length != expected.length)
		return false;
	for (var i = 0; i < result.length; i++) {
		var resultMember = result[i];
		var expectedMember = expected[i];
		if (resultMember.constructor == Array
				&& expectedMember.constructor == Array) {
			if (!verify(resultMember, expectedMember))
				return false;
		} else if (resultMember != expectedMember)
			return false;
	}
	return true;
}
