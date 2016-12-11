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

function preProcessSQL(sql) {
		var url = "http://localhost:9879"; /* TODO: how to parameterize this */
		var request = new XMLHttpRequest();
		request.open("POST", url, false);
		request.setRequestHeader("Content-Type", "text/plain");
		request.send(sql);
//		console.log("Returning encoded form:");
//		console.log(request.responseText);
		return request.responseText;
}

function preMain(input) {
		if (input.source == "sql") {
			input.query = preProcessSQL(input.query);
			input.sourcesexp = true;
		}
//		console.log("Input to main:");
//		console.log(input);
		return main(input);
}
