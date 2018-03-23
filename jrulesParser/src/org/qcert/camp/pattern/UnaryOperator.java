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
package org.qcert.camp.pattern;


/**
 * Enumerates the possible unary operators and describes what parameters they take 
 */
public enum UnaryOperator {
    NatAbs,
    NatLog2,
    NatSqrt,
    OpIdentity,
    OpNeg,
    OpBag,
    OpSingleton,
    OpFlatten,
    OpDistinct,
    OpRec(ParameterKind.String),
    OpDot(ParameterKind.String),
    OpRecRemove(ParameterKind.String),
    OpRecProject(ParameterKind.StringList),
    OpCount,
    OpNatSum,
    OpNatMin,
    OpNatMax,
    OpNatMean,
    OpToString,
    OpLeft,
    OpRight,
    OpBrand(ParameterKind.StringList),
    OpUnbrand,  
    OpCast(ParameterKind.StringList),
    OpFloatOfNat,
    OpFloatTruncate,
    FloatNeg,
    FloatSqrt,
    FloatExp,
    FloatLog,
    FloatLog10,
    FloatCeil,
    FloatFloor,
    FloatAbs,
    OpFloatSum,
    OpFloatMean,
    OpFloatBagMin,
    OpFloatBagMax,
    TimeToSscale,
    TimeFromString,
    TimeDurationFromString;

    /** The kind of parameter taken by this operator */
    private ParameterKind parameterKind;

    /** Alternate constructor for the usual case of no parameter */
    UnaryOperator() {
	this(ParameterKind.None);
    }

    /** Constructor */
    UnaryOperator(ParameterKind parameterKind) {
	this.parameterKind = parameterKind;
    }

    /**
     * @return the parameterKind
     */
    public ParameterKind getParameterKind() {
	return parameterKind;
    }

    /** Enumerate the kinds of parameters */
    public enum ParameterKind {None, String, StringList }
}

