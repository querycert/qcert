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
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import fi.iki.elonen.NanoHTTPD;

/**
 * Main service shell Allows 'subroutines' in Java may be invoked from the primary code of qcert, written in OCaml or extracted to OCaml.  This
 *   service can be obtained either by fork/exec or by running with the -server option.
 */
public class Main extends NanoHTTPD {
	/** Constructor; passes through to NanoHTTPD constructor
	 * @throws various exceptions when initialization fails in whisk mode
	 */
	private Main(int port) throws Exception {
		super(port);
	}
	
	/* (non-Javadoc)
	 * @see fi.iki.elonen.NanoHTTPD#serve(fi.iki.elonen.NanoHTTPD.IHTTPSession)
	 */
	@Override
	public Response serve(IHTTPSession session) {
        Method method = session.getMethod();
        if (Method.POST.equals(method)) {
        	List<String> verb = session.getParameters().get("verb");
          Map<String, String> files = new HashMap<String, String>();
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
          String response = Dispatcher.dispatch(verb.get(0), arg);
          return respond(Response.Status.OK, response);
        } else if (Method.OPTIONS.equals(method)) {
            Response response = respond(Response.Status.OK, "");
            response.addHeader("Access-Control-Allow-Methods", "POST");
            response.addHeader("Access-Control-Allow-Headers", "Content-Type");
            return response;
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
	 * Main.
	 * <p>Command line must conform to one of the following templates.
	 * <ol>
	 * <li><em>verb</em>
	 * <li><b>-server</b> <em>portnumber</em>
	 * </ol>
	 * <p>In the first template, the verb must be one recognized by the Java service dispatcher.  The argument is read from stdin and
	 *   the result posted to stdout.
	 * <p>In the second template, the server is started on the given port.  It then responds to "old-style" Java service requests via
	 *   http Post (verb passed in the URL query and argument passed in the POST body).
	 */
	public static void main(String[] args) {
		String portString = null;
		if (args.length < 1 || args.length > 3)
			error("Improperly invoked via command line with " + args.length + " arguments");
		else if (args[0].equals("-server")) {
			if (args.length != 2)
				error("Port number (only) required with -server option");
			portString = args[1];
		} else if (args.length != 1)
			error("Unless -server is specified, there must be exactly one (method name) argument");
		else
			runAsCmdline(args[0]);
	
		/* Server modes */
		int port = -1;
		try {
			port = Integer.parseInt(portString);
		} catch (NumberFormatException e) {}
		if (port < 1 || port > Character.MAX_VALUE)
			error("Invalid port number " + portString);
		runAsServer(port);
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
		System.out.println(Dispatcher.dispatch(verb, arg));
	}

	/**
	 * Run as an http service.
	 * @param port the port to listen on for http post requests
	 * @param mode either -server or -whiskserver
	 */
	private static void runAsServer(int port) {
		try {
			Main svc = new Main(port);
			svc.start(NanoHTTPD.SOCKET_READ_TIMEOUT, false);
		} catch (Exception e) {
			error("Could not start: " + e.getMessage());
		}
		System.out.println("Java service started on port " + port);
	}
}
