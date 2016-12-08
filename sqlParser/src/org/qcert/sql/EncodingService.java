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

import fi.iki.elonen.NanoHTTPD;

/**
 * A small nonohttpd-based server that does SQL parse-encode (to sexp) via http get requests.
 */
public class EncodingService extends NanoHTTPD {
	public EncodingService(int port) {
		super(port);
	}

	/* (non-Javadoc)
	 * @see fi.iki.elonen.NanoHTTPD#serve(fi.iki.elonen.NanoHTTPD.IHTTPSession)
	 */
	@Override
	public Response serve(IHTTPSession session) {
		// TODO
		return null;
	}

}
