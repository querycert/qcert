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

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

/** Provides support for I/O files
 */
public class IO {

        JsonObject _schema;
	JsonArray _hierarchy;
        JsonArray[] _output;
        JsonObject _input;

        IO() {
	    _schema=null;
	    _hierarchy=null;
	    _output=new JsonArray[1];
	    _input=null;
        }
    
	// Return full schema
	public JsonObject getSchema() {
		return _schema;
	}
	
	// Return brand hierarchy
	public JsonArray getHierarchy() {
		return _hierarchy;
	}
	
	// Return expected output
	public JsonArray[] getoutput() {
		return _output;
	}
	
	// Return data input
	public JsonObject getInput() {
		return _input;
	}

}
