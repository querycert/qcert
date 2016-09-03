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
package org.qcert.camp;

import org.qcert.calib.CACoEngine;
import org.qcert.calib.CACoEngineAPI;
import org.qcert.calib.CALibWrapper.camp;
import org.qcert.camp.pattern.CampPattern;

/**
 * Contains utilities to drive Java AST forms through the ML/Coq code as needed (via CALib)
 */
public class BridgeToML {
	private CACoEngineAPI caco = new CACoEngine();
	
	public camp importCAMP(CampPattern pattern) {
		return new CACoEngine().import_camp(pattern.emit());
	}
	
	public String dumpCAMP(camp toDump) {
		return new CACoEngine().export_camp(toDump);
	}
}
