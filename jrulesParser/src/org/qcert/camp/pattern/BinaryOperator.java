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
package org.qcert.camp.pattern;

/**
 * Enumerates the possible binary operators
 */
public enum BinaryOperator {
	ArithPlus,
	ArithMinus,
	ArithMult,
	ArithMin,
	ArithMax,
	ArithDivide,
	ArithRem,
	AEq, 
	AConcat, 
	AMergeConcat, 
	AAnd, 
	AOr, 
	ALt, 
	ALe, 
	AUnion, 
	AMinus, 
	AMin, 
	AMax, 
	AContains, 
	ASConcat, 
    AFloatPlus, 
    AFloatMinus,
    AFloatMult,  
    AFloatDiv,  
    AFloatPow,  
    AFloatMin,  
    AFloatMax,  
    AFloatNe, 
    AFloatLt,  
    AFloatLe,  
    AFloatGt,  
    AFloatGe,  
    ATimeAs, 
    ATimeShift, 
    ATimeNe,
    ATimeLt,
    ATimeLe,
    ATimeGt,
    ATimeGe,
    ATimeDurationFromScale, 
    ATimeDurationBetween;
	
	public boolean isBoolean() {
		switch (this) {
		case AEq:
		case AAnd:
		case AContains:
		case AFloatGe:
		case AFloatGt:
		case AFloatLe:
		case AFloatLt:
		case AFloatNe:
		case ALe:
		case ALt:
		case AOr:
		case ATimeGe:
		case ATimeGt:
		case ATimeLe:
		case ATimeLt:
		case ATimeNe:
			return true;
		default:
			return false;
		}
	}

	public boolean isArithmetic() {
		switch (this) {
		case AFloatDiv:
		case AFloatMax:
		case AFloatMin:
		case AFloatMinus:
		case AFloatMult:
		case AFloatPlus:
		case AFloatPow:
		case ArithDivide:
		case ArithMax:
		case ArithMin:
		case ArithMinus:
		case ArithMult:
		case ArithPlus:
		case ArithRem:
			return true;
		default:
			return false;
		}
	}
}
