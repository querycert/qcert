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
package org.qcert.camp.data;

import java.util.Collections;

import org.qcert.camp.CampAST;

/**
 * Represents CAMP data (for use in constants) 
 */
public abstract class CampData extends CampAST {
	public enum Kind {
		  dunit, dnat, dbool, dstring, dcoll, drec, dleft, dright, dbrand,
		  dfloat, dtime_scale, dtime_duration, dtime_point;
	}
	/** Single instance of dunit */
	public static final UnitData UNIT = new UnitData();
	/** Single instance of dright of dunit */
	public static final RightData RIGHT_UNIT = new RightData(UNIT);
	/** The RIGHT_UNIT value is also called NULL */
	public static final CampData NULL = RIGHT_UNIT;
	/** Single instance of the true dbool */
	public static final BoolData TRUE = new BoolData(true);
	/** Single instance of the false dbool */
	public static final BoolData FALSE = new BoolData(false);
	/** Single instance of the empty collection */
	public static final CollData EMPTY_COLL = new CollData(Collections.emptyList());
	
	/** Single instance of the empty record */
	public static final RecData EMPTY_REC = new RecData(Collections.emptyMap());
	
	public abstract Kind getKind();
}
