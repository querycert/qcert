/**
 * Copyright (C) 2016 Joshua Auerbach
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
function preProcessSQL(sql, useLocal) {
    var url = useLocal ? "http://localhost:9879" : "http://35.164.159.76:9879";
    //	console.log("URL: " + url);
    //	console.log("local flag: " + useLocal);
    var request = new XMLHttpRequest();
    request.open("POST", url, false);
    request.setRequestHeader("Content-Type", "text/plain");
    request.send(sql);
    //	console.log("Returning encoded form:");
    //	console.log(request.responseText);
    return request.responseText;
}
function qcertPreCompile(input, useLocal) {
    if (input.source == "sql") {
        try {
            input.query = preProcessSQL(input.query, useLocal);
        }
        catch (e) {
            return { "result": e.message };
        }
        input.sourcesexp = true;
    }
    //		console.log("Input to qcertCompile:");
    //		console.log(input);
    return qcertCompile(input);
}
//# sourceMappingURL=qcertPreCompiler.js.map