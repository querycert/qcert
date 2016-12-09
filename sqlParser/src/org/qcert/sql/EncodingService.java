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
package org.qcert.sql;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import fi.iki.elonen.NanoHTTPD;

/**
 * A small nonohttpd-based server that does SQL parse-encode (to sexp) via http get requests.
 */
public class EncodingService extends NanoHTTPD {
	public EncodingService(int port) {
		super(port);
	}
	
	public static void main(String[] args) throws IOException {
		int port = args.length == 0 ? 9879 : Integer.parseInt(args[0]);
		EncodingService svc = new EncodingService(port);
		svc.start(NanoHTTPD.SOCKET_READ_TIMEOUT, false);
	}

	/* (non-Javadoc)
	 * @see fi.iki.elonen.NanoHTTPD#serve(fi.iki.elonen.NanoHTTPD.IHTTPSession)
	 */
	@Override
	public Response serve(IHTTPSession session) {
        Map<String, String> files = new HashMap<String, String>();
        Method method = session.getMethod();
        if (Method.POST.equals(method)) {
            try {
                session.parseBody(files);
            } catch (IOException ioe) {
            	System.out.println("I/O Exception parsing body");
                return newFixedLengthResponse(Response.Status.INTERNAL_ERROR, NanoHTTPD.MIME_PLAINTEXT, "SERVER INTERNAL ERROR: IOException: " + ioe.getMessage());
            } catch (ResponseException re) {
            	System.out.println("Response Exception parsing body");
                return newFixedLengthResponse(re.getStatus(), NanoHTTPD.MIME_PLAINTEXT, re.getMessage());
            }
            String query = files.get("postData");
            if (query == null) {
            	System.out.println("No postData in body");
                return newFixedLengthResponse(Response.Status.BAD_REQUEST, NanoHTTPD.MIME_PLAINTEXT, "Invalid input");
            }
            try { 
            	return newFixedLengthResponse(Response.Status.OK, NanoHTTPD.MIME_PLAINTEXT, PrestoEncoder.parseAndEncode(query, false));
            } catch (Throwable t) {
            	t.printStackTrace();
            	return newFixedLengthResponse(Response.Status.BAD_REQUEST, NanoHTTPD.MIME_PLAINTEXT, "*ERROR*: " + t.getMessage());
            }
        } else {
        	System.out.println("Rejecting non-post request");
            return newFixedLengthResponse(Response.Status.BAD_REQUEST, NanoHTTPD.MIME_PLAINTEXT, "Only POST requests accepted");
        }
	}
}
