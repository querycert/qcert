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

// List URLs for the "whisk" qcert service in the order they should be attempted.  It is a good idea (but not required) to put a 
// localhost URL first so that new functionality can be tested without perturbing publically deployed whisk actions.  Note that
// our long-running server (what you would run on localhost) is not actually a whisk runtime; it just emulates enough of its behavior
// to run our two actions.

var serverHosts = [ 
    "http://localhost:9879", 
    "https://openwhisk.ng.bluemix.net/api/v1/web/JoshAuerbachThoughts_test/qcert/qcert.json"
    ];

function whiskDispatch(input: Qcert.CompilerConfig, callback: (result: Qcert.Result) => any) {
    var next = function() {
        console.log("No server found to process request, calling qcertJS.js directly");
        callback(Qcert.compile(input));
    }
    for (var i = serverHosts.length - 1; i >=0; i--)
        next = makeHandler(input, serverHosts[i], callback, next); 
    next();
}

function makeHandler(input: Qcert.CompilerConfig, url: string, success: (result: Qcert.Result) => any, failure: () => any) {
    return function() {
        console.log("Handler invoked on URL " + url);
        var request = new XMLHttpRequest();
        request.open("POST", url, true);
        request.setRequestHeader("Content-Type", "application/json");
        request.onloadend = function() {
            if (request.status == 200) {
                console.log("Success at url " + url);
                var response = JSON.parse(request.responseText);
                success(response);
            } else {
                console.log("Failure at url " + url);
                failure();
            }
        }
        try {
            console.log("Posting request on url " + url);
            request.send(JSON.stringify(input));
        } catch (e) {
        }
    }
}

function qcertWhiskDispatch(input: Qcert.CompilerConfig, callback: (result: Qcert.Result) => any) {
    var handler = function(result: Qcert.Result) {
        if (result.result.substring(0, 6) == "ERROR:")
            console.log("Calling back with error: " + result.result);
        else
            console.log("Calling back after success");
        callback(result);
    }
    console.log("Dispatching whiskDispatch");
    whiskDispatch(input, handler);
}
