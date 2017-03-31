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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.qcert.util.CSV2JSON;

import fi.iki.elonen.NanoHTTPD;

/**
 * Main service shell by which 'subroutines' in Java may be invoked from the primary code of qcert, written in OCaml or extracted to OCaml
 *   from Coq.
 */
public class Main extends NanoHTTPD {
	/** Mapping from verb names to class names where the class implements the Command interface and provides the logic for the verb */
	private static Map<String, String> verbToClass = new HashMap<>();
	static {
		// Extend this table as needed as verbs are added to the system
		verbToClass.put("parseSQL", "org.qcert.sql.EncodingService");
		verbToClass.put("techRule2CAMP", "org.qcert.camp.translator.TechRule2CAMP");
		verbToClass.put("serialRule2CAMP", "org.qcert.camp.translator.SerialRule2CAMP");
		verbToClass.put("csv2JSON", CSV2JSON.class.getName());
		verbToClass.put("sqlSchema2JSON", "org.qcert.sql.SQLSchema2JSON");
	}
	
	/** Mapping from class names to Command instances (conserves instantiations) */
	private static Map<String, Command> classToInstance = new HashMap<>(); 

	/** Pass-through constructor */
	private Main(int port) {
		super(port);
	}
	
	/* (non-Javadoc)
	 * @see fi.iki.elonen.NanoHTTPD#serve(fi.iki.elonen.NanoHTTPD.IHTTPSession)
	 */
	@Override
	public Response serve(IHTTPSession session) {
        Map<String, String> files = new HashMap<String, String>();
        Method method = session.getMethod();
        if (Method.POST.equals(method)) {
        	List<String> verb = session.getParameters().get("verb");
        	if (verb == null || verb.size() != 1) {
        		System.out.println("Rejecting request with no verb or invalid verb");
        		return respond(Response.Status.BAD_REQUEST, "No verb supplied, cannot interpret request");
        	}
            try {
                session.parseBody(files);
            } catch (IOException ioe) {
            	System.out.println("I/O Exception parsing body");
                return respond(Response.Status.INTERNAL_ERROR, "SERVER INTERNAL ERROR: IOException: " + ioe.getMessage());
            } catch (ResponseException re) {
            	System.out.println("Response Exception parsing body");
                return respond(re.getStatus(), re.getMessage());
            }
            String arg = files.get("postData");
            String response = dispatch(verb.get(0), arg);
			return respond(Response.Status.OK, response);
        } else {
        	System.out.println("Rejecting non-post request");
        	return respond(Response.Status.BAD_REQUEST, "Only POST requests accepted");
        }
	}

	/** Issue a response from server mode */
	private Response respond(Response.Status status, String content) {
		Response response = newFixedLengthResponse(status, NanoHTTPD.MIME_PLAINTEXT, content);
    	response.addHeader("Access-Control-Allow-Origin", "*");
    	return response;
	}


	/**
	 * Command line may or may not begin with the special token -server.  If it does, there must be exactly two arguments and the second
	 *   argument is a port to listen on.  It causes the service shell to run as an http server and respond to post requests.
	 * Otherwise, there must be only one argument and it is taken to be a function name.  The single string argument to the function
	 * is read from stdin and the result of the execution (or an error message) is written to stdout.
	 */
	public static void main(String[] args) {
		if (args.length < 1 || args.length > 2)
			error("Improperly invoked via command line with " + args.length + " arguments");
		else if (args[0].equals("-server")) {
			if (args.length != 2)
				error("Port number required with -server option");
			int port = -1;
			try {
				port = Integer.parseInt(args[1]);
			} catch (NumberFormatException e) {}
			if (port < 1 || port > Character.MAX_VALUE)
				error("Invalid port number " + args[1]);
			runAsServer(port);
		} else if (args.length != 1)
			error("Unless -server is specified, there must be exactly one (method name) argument");
		else
			runAsCmdline(args[0]);
	}

	/**
	 * Dispatch a request no matter how it arrived.  
	 * @param verb the request verb
	 * @param arg the request argument
	 * @return the request result
	 */
	private static String dispatch(String verb, String arg) {
		String implClass = verbToClass.get(verb);
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
	 * Print a message and exit.  The message is printed to stdout, not stderr, and is prepended with the ERROR: token in case
	 *   the invokation came from qcert.
	 * @param msg the message
	 */
	private static void error(String msg) {
		System.out.println("ERROR: " + msg);
		System.exit(-1);
	}

	/**
	 * Retrieve a valid instance of a class that implements Command
	 * @param implClass the class name
	 * @return the Command or null if the class could not be instantiated
	 */
	private static Command instantiate(String implClass) {
		Command cmd = classToInstance.get(implClass);
		if (cmd == null) {
			try {
				cmd = (Command) Class.forName(implClass).newInstance();
				classToInstance.put(implClass, cmd);
			} catch (Exception e) {
			}
		}
		return cmd;
	}

	/** Read stdin into a String until eos (in a pipeline) 
	 * @throws IOException */
	private static String readStdin() throws IOException {
		InputStreamReader srdr = new InputStreamReader(System.in);
		StringWriter swtr = new StringWriter();
		PrintWriter wtr = new PrintWriter(swtr);
		BufferedReader rdr = new BufferedReader(srdr);
		String line = rdr.readLine();
		while (line != null) {
			wtr.println(line);
			line = rdr.readLine();
		}
		rdr.close();
		wtr.close();
		return swtr.toString();
	}
	
	/**
	 * Run a single verb and set of arguments through the dispatcher in a single invocation from the command line
	 * @param cmdargs the command line arguments (at least one, and not "-server")
	 */
	private static void runAsCmdline(String verb) {
		String arg = null;
		try {
			arg = readStdin();
		} catch (Exception e) {
			error("Problem reading stdin");
			return; // not reached
		}
		System.out.println(dispatch(verb, arg));
	}

	/**
	 * Run as an http service.
	 * @param port the port to listen on for http post requests
	 */
	private static void runAsServer(int port) {
		Main svc = new Main(port);
		try {
			svc.start(NanoHTTPD.SOCKET_READ_TIMEOUT, false);
		} catch (Exception e) {
			error("Could not start: " + e.getMessage());
		}
		System.out.println("Java service started on port " + port);
	}
}
