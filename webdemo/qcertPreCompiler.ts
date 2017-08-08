/**
 * Copyright (C) 2016-2017 Joshua Auerbach 
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

// List server hosts in the order they should be attempted.  It is a good idea (but not required) to put localhost first so that
// new functionality can be tested without updating remote server hosts.
var serverHosts = [ "localhost", "35.164.159.76" ];

function preProcess(text: string, verb: string, callback: (result: string) => any) {
    var next = function() {
        callback("ERROR: no server found to process " + verb + " request");
    }
    for (var i = serverHosts.length - 1; i >=0; i--)
        next = makeHandler(text, verb, serverHosts[i], callback, next); 
    next();
}

function makeHandler(text: string, verb: string, host: string, success: (result: string) => any, failure: () => any) {
    return function() {
        console.log("Handler invoked for host " + host);
        var url = "http://" + host + ":9879?verb=" + verb;
        var request = new XMLHttpRequest();
        request.open("POST", url, true);
        request.setRequestHeader("Content-Type", "text/plain");
        request.onloadend = function() {
            if (request.status == 200) {
                console.log("Success with verb " + verb + " at host " + host);
                success(request.responseText);
            } else {
                console.log("Failure with verb " + verb + " at host " + host);
                failure();
            }
        }
        try {
            console.log("Sending request to host " + host);
            request.send(text);
        } catch (e) {
        }
    }
}

function combineInputAndSchema(input: string, schema: string) {
    var parsed = JSON.parse(schema);
    var combined = { source: input, schema: parsed };
    return JSON.stringify(combined);
}

function qcertPreCompile(input: QcertCompilerConfig, callback: (result: QcertResult) => any) {
    var verb = null, sourceCAMP = false, query = null;
    console.log("Starting pre-compile for source language " + input.source);
    if (input.source == "sql") {
        verb = "parseSQL";
        sourceCAMP = false;
        query = input.query;
    } else if (input.source == "tech_rule") {
        verb = "techRule2CAMP";
        sourceCAMP = true;
        query = combineInputAndSchema(input.query, input.schema);
    } else if (input.source == "designer_rule") {
        verb = "serialRule2CAMP";
        sourceCAMP = true;
        query = input.query;
    } else {
        console.log("No precompile, synchronous callback");
        callback(qcertCompile(input));
        return;
    }
    if (query.length == 0) {
        callback({ result: "ERROR: No source query provided", eval: undefined, emit: null, emitall: []});
        return
    }
    var handler = function(result: string) {
        if (result.substring(0, 6) == "ERROR:") {
            console.log("Calling back with error: " + result);
            callback({ result: result, eval: undefined, emit: null, emitall: []});
        } else {
            input.query = result;
            input.sourcesexp = true;
            if (sourceCAMP) {
                input.source = "CAMP";
                if (input.path[0].toLowerCase() == "camp")
                    input.path.shift();
            }
            console.log("Doing qcertCompile after successful preProcess");
            console.log("Path: " + input.path);
            callback(qcertCompile(input));
        }
    }
    console.log("Dispatching preprocess");
    preProcess(query, verb, handler);
}
