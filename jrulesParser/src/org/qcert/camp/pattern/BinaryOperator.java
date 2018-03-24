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
    NatPlus,
    NatMinus,
    NatMult,
    NatMin,
    NatMax,
    NatDiv,
    NatRem,
    OpEqual,
    OpRecConcat,
    OpRecMerge,
    OpAnd,
    OpOr,
    OpLt,
    OpLe,
    OpBagUnion,
    OpBagMinus,
    OpBagMin,
    OpBagMax,
    OpContains,
    OpStringConcat,
    FloatPlus,
    FloatMinus,
    FloatMult,
    FloatDiv,
    FloatPow,
    FloatMin,
    FloatMax,
    FloatNe,
    FloatLt,
    FloatLe,
    FloatGt,
    FloatGe,
    TimeAs,
    TimeShift,
    TimeNe,
    TimeLt,
    TimeLe,
    TimeGt,
    TimeGe,
    TimeDurationFromScale,
    TimeDurationBetween;

    public boolean isBoolean() {
	switch (this) {
	case OpEqual:
	case OpAnd:
	case OpContains:
	case OpLe:
	case OpLt:
	case OpOr:
	case FloatGe:
	case FloatGt:
	case FloatLe:
	case FloatLt:
	case FloatNe:
	case TimeGe:
	case TimeGt:
	case TimeLe:
	case TimeLt:
	case TimeNe:
	    return true;
	default:
	    return false;
	}
    }

    public boolean isArithmetic() {
	switch (this) {
	case OpLe:
	case OpLt:
	case FloatDiv:
	case FloatMax:
	case FloatMin:
	case FloatMinus:
	case FloatMult:
	case FloatPlus:
	case FloatPow:
	case FloatGe:
	case FloatGt:
	case FloatLe:
	case FloatLt:
	case FloatNe:
	case NatDiv:
	case NatMax:
	case NatMin:
	case NatMinus:
	case NatMult:
	case NatPlus:
	case NatRem:
	    return true;
	default:
	    return false;
	}
    }
}
