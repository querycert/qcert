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
package org.qcert.javasvc;

import java.util.HashMap;
import java.util.Map;

import org.qcert.util.CSV2JSON;

/**
 * Contains logic used by Main (long-running http server).
 */
public class Dispatcher {
	/** Mapping from verb names to class names where the class implements the Command interface and provides the logic for the verb */
	static Map<String, String> verbToClass = new HashMap<>();
	static {
		// Extend this table as needed as verbs are added to the system
		verbToClass.put("parseSQL", "org.qcert.sql.EncodingService");
		verbToClass.put("parseSQLPP", "org.qcert.sqlpp.EncodingServicePP");
		verbToClass.put("techRule2CAMP", "org.qcert.camp.translator.TechRule2CAMP");
		verbToClass.put("serialRule2CAMP", "org.qcert.camp.translator.SerialRule2CAMP");
		verbToClass.put("csv2JSON", CSV2JSON.class.getName());
		verbToClass.put("sqlSchema2JSON", "org.qcert.sql.SQLSchema2JSON");
	}
	
	/** Mapping from class names to Command instances (conserves instantiations in the long running case). */
	static Map<String, Command> classToInstance = new HashMap<>(); 

	/**
	 * Dispatch a request no matter how it arrived.  
	 * @param verb the request verb
	 * @param arg the request argument
	 * @return the request result
	 */
	static String dispatch(String verb, String arg) {
		String implClass = Dispatcher.verbToClass.get(verb);
		if (implClass == null)
			return "ERROR: no implementation class for verb " + verb;
		Command cmd = instantiate(implClass);
		if (cmd == null)
			return "ERROR: implementation of " + verb + " is not available";
		try {
			return cmd.invoke(arg);
		} catch (Throwable t) {
			return "ERROR: implementation of " + verb + " failed with the error -- " + t.getMessage();
		}
	}

	/**
	 * Retrieve a valid instance of a class that implements Command
	 * @param implClass the class name
	 * @return the Command or null if the class could not be instantiated
	 */
	private static Command instantiate(String implClass) {
		Command cmd = Dispatcher.classToInstance.get(implClass);
		if (cmd == null) {
			try {
				cmd = (Command) Class.forName(implClass).newInstance();
				Dispatcher.classToInstance.put(implClass, cmd);
			} catch (Exception e) {
			}
		}
		return cmd;
	}
}
