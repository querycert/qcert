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
function preProcess(text, verb) {
    var request = preProcessOnce(text, verb, "localhost");
    if (request.status == 0)
        request = preProcessOnce(text, verb, "35.164.159.76");
    if (request.status == 0)
        throw Error("No server found to perform the " + verb + " function");
    if (request.status == 200)
        return request.responseText;
    return "ERROR " + request.status + ": " + request.responseText;
}
function preProcessOnce(text, verb, host) {
    var url = "http://" + host + ":9879?verb=" + verb;
    var request = new XMLHttpRequest();
    request.open("POST", url, false);
    request.setRequestHeader("Content-Type", "text/plain");
    try {
        request.send(text);
    }
    catch (e) { }
    return request;
}
function combineInputAndSchema(input, schema) {
    var parsed = JSON.parse(schema);
    var combined = { source: input, schema: parsed };
    return JSON.stringify(combined);
}
function qcertPreCompile(input, schema) {
    try {
        if (input.source == "sql") {
            input.query = preProcess(input.query, "parseSQL");
            input.sourcesexp = true;
        }
        else if (input.source == "techrule") {
            var combined = combineInputAndSchema(input.query, schema);
            input.query = preProcess(combined, "techRule2CAMP");
            input.sourcesexp = true;
            input.source = "camp";
        }
        else if (input.source == "designerrule") {
            input.query = preProcess(input.query, "serialRule2CAMP");
            input.sourcesexp = true;
            input.source = "camp";
        }
    }
    catch (e) {
        return { result: "ERROR: " + e.message };
    }
    if (input.query.substring(0, 6) == "ERROR:")
        return { result: input.query };
    return qcertCompile(input);
}
//# sourceMappingURL=qcertPreCompiler.js.map