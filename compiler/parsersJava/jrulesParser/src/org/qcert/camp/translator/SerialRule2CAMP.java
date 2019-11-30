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
package org.qcert.camp.translator;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Base64;
import java.util.Base64.Decoder;

import org.qcert.camp.pattern.CampPattern;
import org.qcert.javasvc.Command;

/**
 * Implement Java Service command for converting a serialized SemRule (ie, an "ARL file") to CAMP
 * The input String of the command is a base64 encoding of the serialized SemRule.
 */
public class SerialRule2CAMP implements Command {

	@Override
	public String invoke(String arg) {
		Decoder decoder = Base64.getMimeDecoder();
		InputStream stream = new ByteArrayInputStream(decoder.decode(arg));
		try {
			ODMFrontEnd frontEnd = new ODMFrontEnd(stream, null);
			SemRule2CAMP semRule2Camp = new SemRule2CAMP(frontEnd.getFactory());
			CampPattern translated = semRule2Camp.translate(frontEnd.getRule()).convertToPattern();
			return translated.emit();
		} catch (Exception e) {
			return "ERROR: " + e.getMessage();
		}
	}

}
