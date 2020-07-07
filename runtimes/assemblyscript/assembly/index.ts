class EjValue {}

export class EjNull extends EjValue {
  constructor() { super(); }
}
export const IdEjNull = idof<EjNull>()

const c_null = new EjNull();

export class EjBool extends EjValue {
  value: bool
  constructor(a: bool) { super(); this.value = a; }
}
export const IdEjBool = idof<EjBool>()

const c_true = new EjBool(true);
const c_false = new EjBool(false);

export class EjNumber extends EjValue {
  value: f64
  constructor(a: f64) { super(); this.value = a; }
}
export const IdEjNumber = idof<EjNumber>()

const c_neg1 = new EjNumber(-1);
const c_1 = new EjNumber(1);
const c_0 = new EjNumber(0);

export class EjBigInt extends EjValue {
  value: i64
  constructor(a: i64) { super(); this.value = a; }
}
export const IdEjBigInt = idof<EjBigInt>()

export class EjString extends EjValue {
  value: string
  constructor(a: string) { super(); this.value = a; }
}
export const IdEjString = idof<EjString>()

export class EjStringBuilder {
  private buf: Array<i32>
  private pos: i32
  constructor() {
    this.pos = 0;
    this.buf = new Array<i32>(32);
  }
  append(val: i32): EjStringBuilder {
    if (this.pos >= this.buf.length) {
      this.buf = this.buf.concat(new Array(this.buf.length * 2));
    }
    this.buf[this.pos] = val;
    this.pos++;
    return this;
  }
  finalize(): EjString {
    let buf = this.buf.slice(0, this.pos);
    let str = String.fromCharCodes(buf);
    return new EjString(str);
  }
}

export class EjArray extends EjValue {
  values: Array<EjValue>
  constructor(a: Array<EjValue>) { super(); this.values = a; }
}
export const IdArrayEjValue = idof<Array<EjValue>>()
export const IdEjArray = idof<EjArray>()

export class EjObject extends EjValue {
  values: Map<string, EjValue>
  constructor() { super(); this.values = new Map<string, EjValue>(); }
  set(k: string, v: EjValue): void {
    this.values.set(k,v);
  }
  get(k: string): EjValue {
    return this.values.get(k);
  }
  keys(): Array<string> {
    return this.values.keys();
  }
}
export const IdEjObject = idof<EjObject>()

export class EjLeft extends EjValue {
  value: EjValue
  constructor(a: EjValue) { super(); this.value = a; }
}
export const IdEjLeft = idof<EjLeft>()

export class EjRight extends EjValue {
  value: EjValue
  constructor(a: EjValue) { super(); this.value = a; }
}
export const IdEjRight = idof<EjRight>()

// EJson Operators

export function opNot(a: EjBool): EjBool {
  return new EjBool(!a.value);
}

export function opNeg(a: EjNumber): EjNumber {
  return new EjNumber(-a.value);
}

export function opAnd(a: EjBool, b: EjBool): EjBool {
  return new EjBool(a.value && b.value);
}

export function opOr(a: EjBool, b: EjBool): EjBool {
  return new EjBool(a.value || b.value);
}

export function opLt(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value < b.value);
}

export function opLe(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value <= b.value);
}

export function opGt(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value > b.value);
}

export function opGe(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value >= b.value);
}

export function opAddString(a: EjString, b: EjString): EjString {
  return new EjString(a.value + b.value);
}

export function opAddNumber(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value + b.value);
}

export function opSub(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value - b.value);
}

export function opMult(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value * b.value);
}

export function opDiv(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value / b.value);
}

export function opStrictEqual(a: EjValue, b: EjValue): EjBool {
  if (a instanceof EjNull && b instanceof EjNull) {
    return c_true;
  }
  if (a instanceof EjBool && b instanceof EjBool) {
    let aa : EjBool = changetype<EjBool>(a) ;
    let bb : EjBool = changetype<EjBool>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjNumber && b instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    let bb : EjNumber = changetype<EjNumber>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjString && b instanceof EjString) {
    let aa : EjString = changetype<EjString>(a) ;
    let bb : EjString = changetype<EjString>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  return unreachable();
}

export function opStrictDisEqual(a: EjValue, b: EjValue): EjBool {
  if (a instanceof EjNull && b instanceof EjNull) {
    return c_false;
  }
  if (a instanceof EjBool && b instanceof EjBool) {
    let aa : EjBool = changetype<EjBool>(a) ;
    let bb : EjBool = changetype<EjBool>(b) ;
    return aa.value != bb.value ? c_true : c_false;
  }
  if (a instanceof EjNumber && b instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    let bb : EjNumber = changetype<EjNumber>(b) ;
    return aa.value != bb.value ? c_true : c_false;
  }
  if (a instanceof EjString && b instanceof EjString) {
    let aa : EjString = changetype<EjString>(a) ;
    let bb : EjString = changetype<EjString>(b) ;
    return aa.value != bb.value ? c_true : c_false;
  }
  return unreachable();
}

export function opArray(a: EjValue): EjArray {
  // TODO: opArray
  return unreachable();
}

export function opArrayLength(a: EjArray): EjBigInt {
  return new EjBigInt(i64(a.values.length));
}

export function opArrayPush(a: EjArray, b: EjValue): EjArray {
  // TODO: opArrayPush: should we mutate the array?;
  return new EjArray(a.values.concat([b]));
}

export function opArrayAccess(a: EjArray, b: EjBigInt): EjValue {
  // TODO: opArrayAccess: should we check out of bound and i32 overflow?
  return a.values[i32(b.value)];
}

export function opObject(a: EjValue): EjObject {
  // TODO: opObject
  return unreachable();
}

export function opAccess(a: EjObject, k: EjString): EjValue {
  // TODO: opAccess redundant with runtimeRecDot?
  // TODO: opAccess: check for key not found needed?
  return a.values.get(k.value);
}

export function opHasOwnProperty(a: EjObject, k: EjString): EjValue {
  // TODO: opHasOwnProperty
  return unreachable();
}

export function opMathMin(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.min(a.value, b.value));
}

export function opMathMax(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.max(a.value, b.value));
}

export function opMathExp(a: EjNumber): EjNumber {
  return new EjNumber(Math.exp(a.value));
}

export function opMathPow(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.pow(a.value, b.value));
}

export function opMathAbs(a: EjNumber): EjNumber {
  return new EjNumber(Math.abs(a.value));
}

export function opMathLog(a: EjNumber): EjNumber {
  return new EjNumber(Math.log(a.value));
}

export function opMathLog10(a: EjNumber): EjNumber {
  return new EjNumber(Math.log10(a.value));
}

export function opMathSqrt(a: EjNumber): EjNumber {
  return new EjNumber(Math.sqrt(a.value));
}

export function opMathCeil(a: EjNumber): EjNumber {
  return new EjNumber(Math.ceil(a.value));
}

export function opMathFloor(a: EjNumber): EjNumber {
  return new EjNumber(Math.floor(a.value));
}

export function opMathTrunc(a: EjNumber): EjNumber {
  return new EjNumber(Math.trunc(a.value));
}

// EJson Runtime Operators

// TODO: this seems to be redundant with opStrictEqual, is it?
export function runtimeEqual(a: EjValue, b: EjValue): EjBool {
  return opStrictEqual(a, b);
}

function compare<T>(a: T, b: T): EjNumber {
  if (a < b) { return c_neg1; }
  if (a > b) { return c_1; }
  return c_0;
}

export function runtimeCompare(a: EjValue, b: EjValue): EjNumber {
  if (a instanceof EjNumber && b instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    let bb : EjNumber = changetype<EjNumber>(b) ;
    return compare<f64>(aa.value, bb.value);
  }
  if (a instanceof EjBigInt && b instanceof EjBigInt) {
    let aa : EjBigInt = changetype<EjBigInt>(a) ;
    let bb : EjBigInt = changetype<EjBigInt>(b) ;
    return compare<i64>(aa.value, bb.value);
  }
  return unreachable();
}

// TODO: this seems to be redundant with opAccess, is it?
export function runtimeRecDot(a: EjObject, b:EjString): EjValue {
  return opAccess(a, b);
}
