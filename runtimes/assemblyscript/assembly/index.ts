/////////////////////////
// EJson Data Encoding //
/////////////////////////

class EjValue {}

function cast<T>(x : EjValue): T {
  if (x instanceof T) {
    let r : T = changetype<T>(x);
    return r;
  }
  throw new Error('invalid cast');
}

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
export function ejBigInt_of_f64(x: f64) : EjBigInt {
  let i = I64.parseInt(Math.trunc(x).toString());
  return new EjBigInt(i);
}

export class EjString extends EjValue {
  value: string
  constructor(a: string) { super(); this.value = a; }
}
export const IdEjString = idof<EjString>()

export class EjArray extends EjValue {
  values: Array<EjValue>
  constructor(a: Array<EjValue>) { super(); this.values = a; }
}
export const IdArrayEjValue = idof<Array<EjValue>>()
export const IdEjArray = idof<EjArray>()
const c_empty_array = new EjArray([])

// ImpEJson's n-ary runtimeArray operator constructs EjArrays at runtime
// The compiled wasm module relies on the following helper to do this.
export class EjArrayBuilder {
  private arr: Array<EjValue>
  private pos: i32
  constructor(n: i32) {
    this.pos = 0;
    this.arr = new Array<EjValue>(n);
  }
  put(val: EjValue): EjArrayBuilder {
    this.arr[this.pos] = val;
    this.pos++;
    return this;
  }
  finalize(): EjArray {
    return new EjArray(this.arr)
  }
}

export class EjObject extends EjValue {
  values: Map<string, EjValue>
  constructor() { super(); this.values = new Map<string, EjValue>(); }
  has(k: EjString): bool {
    return this.values.has(k.value);
  }
  set(k: EjString, v: EjValue): EjObject {
    this.values.set(k.value, v);
    return this;
  }
  get(k: EjString): EjValue {
    // redundant safety check
    if (! this.has(k)) {
      // unreachable for valid engine, runtime, and compiled ergo
      throw new Error("EjObject misses key '" + k.value + "'");
    }
    // actual code
    return this.values.get(k.value);
  }
  keys(): Array<EjString> {
    return this.values.keys().map<EjString>(x => new EjString(x));
  }
}
export const IdEjObject = idof<EjObject>()

/////////////////////////
// EJson Serialization //
/////////////////////////

// We use a prefix-encoded binary representation of EjValue for IO.

///////////////////////////////////////////////
// EJson Serialization // EjValue --> binary //
///////////////////////////////////////////////

// BytesBuilder helps me to construct long ArrayBuffers.
// ArrayBuffers are binary strings.
class BytesBuilder {
  segments: Array<ArrayBuffer>
  size: i32

  constructor() { this.segments = []; this.size = 0; }

  // virtually append an ArrayBuffer segment
  append(s: ArrayBuffer): void {
    this.segments.push(s);
    this.size += s.byteLength;
  }

  // concatenate all segments
  finalize(): ArrayBuffer {
    let b = new ArrayBuffer(this.size);
    let p : i32 = 0;
    let v = Uint8Array.wrap(b);
    for (let i = 0; i < this.segments.length; i++) {
      let s = Uint8Array.wrap(this.segments[i]);
      // this is byte-by-byte copy. Could be much faster when copying words.
      for (let j = 0; j < s.length; j++) {
        v[p] = s[j];
        p++;
      }
    }
    return b;
  }
}

// Append EjValue x to BytesBuilder b
// Core of EjValue --> binary
function ejson_to_bytes_(b: BytesBuilder, x:EjValue): void {
  if (x instanceof EjNull) {
    let s = new ArrayBuffer(1);
    Uint8Array.wrap(s)[0] = 0; // tag
    b.append(s);
    return;
  }
  if (x instanceof EjBool) {
    let xx : EjBool = changetype<EjBool>(x) ;
    let s = new ArrayBuffer(1);
    Uint8Array.wrap(s)[0] = xx.value ? 2 : 1; // tag
    b.append(s);
    return;
  }
  if (x instanceof EjNumber) {
    let xx : EjNumber = changetype<EjNumber>(x) ;
    let s = new ArrayBuffer(9);
    let v = new DataView(s);
    v.setUint8(0, 3);
    v.setFloat64(1, xx.value, true);
    b.append(s);
    return;
  }
  if (x instanceof EjBigInt) {
    let xx : EjBigInt = changetype<EjBigInt>(x) ;
    let s = new ArrayBuffer(9);
    let v = new DataView(s);
    v.setUint8(0, 4); // tag
    v.setInt64(1, xx.value, true);
    b.append(s);
    return;
  }
  if (x instanceof EjString) {
    let xx : EjString = changetype<EjString>(x) ;
    let utf8 = String.UTF8.encode(xx.value);
    let s = new Uint8Array(5);
    let v = new DataView(s.buffer);
    s[0] = 5; // tag
    v.setUint32(1, utf8.byteLength, true);
    b.append(s.buffer);
    b.append(utf8);
    return;
  }
  if (x instanceof EjArray) {
    let xx : EjArray = changetype<EjArray>(x) ;
    let s = new Uint8Array(5);
    let v = new DataView(s.buffer);
    s[0] = 6; // tag
    v.setUint32(1, xx.values.length, true);
    b.append(s.buffer);
    for (let i = 0; i < xx.values.length; i++) {
      ejson_to_bytes_(b, xx.values[i]);
    }
    return;
  }
  if (x instanceof EjObject) {
    let xx : EjObject = changetype<EjObject>(x) ;
    let s = new Uint8Array(5);
    let v = new DataView(s.buffer);
    s[0] = 7; // tag
    v.setUint32(1, xx.values.size, true);
    b.append(s.buffer);
    let keys = xx.values.keys();
    for (let i = 0; i < xx.values.size; i++) {
      let k = keys[i];
      // write key as utf8 string with byte length prefix
      let utf8 = String.UTF8.encode(k);
      let s = new Uint8Array(4);
      let v = new DataView(s.buffer);
      v.setUint32(0, utf8.byteLength, true);
      b.append(s.buffer);
      b.append(utf8);
      // write value
      ejson_to_bytes_(b, xx.values.get(k));
    }
    return;
  }
  throw new Error ('ejson_to_bytes_: unsupported value')
}

// Convert EjValue x to (binary) ArrayBuffer
export function ejson_to_bytes(x: EjValue): ArrayBuffer {
  let b = new BytesBuilder();
  ejson_to_bytes_(b, x);
  return b.finalize();
}

///////////////////////////////////////////////
// EJson Serialization // binary --> EjValue //
///////////////////////////////////////////////

// This iterator helps me to consume a long ArrayBuffer.
// The ArrayBuffer holds the binary EjValue.
class MovingPointer {
  value: i32
  constructor(x: i32) { this.value = x }
  advance(by: i32): i32 {
    let r = this.value;
    this.value += by;
    return r;
  }
}

// Read EjValue from ArrayBuffer b at Pointer p.
// Core of binary --> EjValue
function ejson_of_bytes_(p: MovingPointer, b:ArrayBuffer): EjValue {
  // switch tag
  switch(Uint8Array.wrap(b, p.advance(1), 1)[0]) {
    case 0:
      return c_null;
    case 1:
      return c_false;
    case 2:
      return c_true;
    case 3: {
      let v = new DataView(b, p.advance(8), 8);
      return new EjNumber(v.getFloat64(0, true));
    }
    case 4: {
      let v = new DataView(b, p.advance(8), 8);
      return new EjBigInt(v.getInt64(0, true));
    }
    case 5: {
      let v = new DataView(b, p.advance(4), 4);
      let len = v.getUint32(0, true);
      // ArrayBuffer is a pointer
      let str = String.UTF8.decodeUnsafe(changetype<i32>(b) + p.advance(len), len);
      return new EjString(str);
    }
    case 6: {
      let v = new DataView(b, p.advance(4), 4)
      let len = v.getUint32(0, true);
      let arr = new Array<EjValue>(len);
      for (let i=<u32>0; i < len; i++) {
        arr[i] = ejson_of_bytes_(p, b);
      }
      return new EjArray(arr);
    }
    case 7: {
      let v = new DataView(b, p.advance(4), 4)
      let len = v.getUint32(0, true);
      let obj = new EjObject();
      for (let i=<u32>0; i < len; i++) {
        let v = new DataView(b, p.advance(4), 4);
        let key_len = v.getUint32(0, true);
        let key = String.UTF8.decodeUnsafe(changetype<i32>(b) + p.advance(key_len), key_len);
        let val = ejson_of_bytes_(p, b);
        obj.set(new EjString(key), val);
      }
      return obj;
    }
  }
  throw new Error('ejson_of_bytes_: unsupported tag')
}

export function ejson_of_bytes(b: ArrayBuffer): EjValue {
  return ejson_of_bytes_(new MovingPointer(0), b);
}

///////////////////////////////////////////////////
// IO: Constants provided by the compiled module //
///////////////////////////////////////////////////

// Compiled wasm modules have their constants stored in their memory in the
// format described above.
// Compiled wasm modules operate on pointers into the runtime's memory.
// Before using a constant, the compiled module has to copy the constant to
// the runtime's memory. It does so using the following two functions and
// ejson_of_bytes.

export function alloc_bytes(n: i32): ArrayBuffer {
  return new ArrayBuffer(((n + 7) >> 3) << 3);
}

export function bytes_set_i64(b: ArrayBuffer, offset: i32, value: i64): void {
  Int64Array.wrap(b)[offset >> 3] = value;
}

/////////////////////
// EJson Operators //
/////////////////////

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
  throw new Error('opStrictEqual: invalid arguments');
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
  throw new Error('opStrictDisEqual: invalid arguments');
}

// n-ary, compiled
// export function opArray(a: EjValue): EjArray {}

export function opArrayLength(a: EjArray): EjBigInt {
  return new EjBigInt(a.values.length);
}

export function opArrayPush(a: EjArray, b: EjValue): EjArray {
  // concat creates new array
  // TODO: opArrayPush: avoid cloning the array on each push.
  return new EjArray(a.values.concat([b]));
}

// Crashes on out of bound like imp eval.
export function opArrayAccess(a: EjArray, b: EjBigInt): EjValue {
  return a.values[i32(b.value)];
}

// n-ary, compiled
// export function opObject(a: EjValue): EjObject {}

// Crashes on missing key like imp eval
export function opAccess(a: EjObject, k: EjString): EjValue {
  return a.get(k);
}

export function opHasOwnProperty(a: EjObject, k: EjString): EjBool {
  return (a.values.has(k.value)) ? c_true : c_false;
}

export function opMathMin(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.min(a.value, b.value));
}

export function opMathMax(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.max(a.value, b.value));
}

export function opMathPow(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.pow(a.value, b.value));
}

export function opMathExp(a: EjNumber): EjNumber {
  return new EjNumber(Math.exp(a.value));
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

/////////////////////////////
// EJson Runtime Operators //
/////////////////////////////

export function runtimeEqual(a: EjValue, b: EjValue): EjBool {
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
  if (a instanceof EjBigInt && b instanceof EjBigInt) {
    let aa : EjBigInt = changetype<EjBigInt>(a) ;
    let bb : EjBigInt = changetype<EjBigInt>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjString && b instanceof EjString) {
    let aa : EjString = changetype<EjString>(a) ;
    let bb : EjString = changetype<EjString>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjArray && b instanceof EjArray) {
    let aa : EjArray = changetype<EjArray>(a) ;
    let bb : EjArray = changetype<EjArray>(b) ;
    if (aa.values.length != bb.values.length) {
      return c_false;
    }
    for (let i = 0; i < aa.values.length; i++) {
      if (! runtimeEqual(aa.values[i], bb.values[i]).value) {
        return c_false;
      }
    }
    return c_true;
  }
  if (a instanceof EjObject && b instanceof EjObject) {
    let aa : EjObject = changetype<EjObject>(a) ;
    let bb : EjObject = changetype<EjObject>(b) ;
    if (aa.values.size != bb.values.size) {
      return c_false;
    }
    let keys = aa.values.keys();
    for (let i = 0; i < keys.length; i++) {
      let k = keys[i];
      if (! bb.values.has(k) ||
          ! runtimeEqual(aa.values[k], bb.values[k]).value ) {
        return c_false;
      }
    }
    return c_true;
  }
  return c_false;
}

function compare<T>(a: T, b: T): EjNumber {
  if (a < b) { return c_1; }
  if (a > b) { return c_neg1; }
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
  throw new Error('runtimeCompare: invalid arguments');
}

function ejValueToString(a: EjValue): string {
  if (a instanceof EjNull) {
    return "unit";
  }
  if (a instanceof EjBool) {
    let aa : EjBool = changetype<EjBool>(a) ;
    return aa.value ? "true" : "false";
  }
  if (a instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    return aa.value.toString();
  }
  if (a instanceof EjBigInt) {
    let aa : EjBigInt = changetype<EjBigInt>(a) ;
    return aa.value.toString();
  }
  if (a instanceof EjString) {
    let aa : EjString = changetype<EjString>(a) ;
    return aa.value;
  }
  if (a instanceof EjArray) {
    let aa : EjArray = changetype<EjArray>(a) ;
    let s : string = "[";
    for (let i = 0; i < aa.values.length - 1; i++) {
       s += ejValueToString(aa.values[i]) + ", " ;
    }
    if (aa.values.length > 0) {
      s += ejValueToString(aa.values[aa.values.length - 1]);
    }
    return s + "]";
  }
  if (a instanceof EjObject) {
    let aa : EjObject = changetype<EjObject>(a) ;
    let keys = aa.values.keys();
    let s : string = "{";
    let n = keys.length;
    for (let i = 0; i < n - 1; i++) {
       s += keys[i] + "->" + ejValueToString(aa.values[keys[i]]) + ", " ;
    }
    if (n > 0) {
      s += keys[n - 1] + "->" + ejValueToString(aa.values[keys[n - 1]]);
    }
    return s + "}";
  }
  throw new Error('ejValueToString: unknown value');
}
// wrap assemblyscript string into EjString
export function runtimeToString(a: EjValue): EjString {
  return new EjString(ejValueToString(a));
}

export function runtimeToText(a: EjValue): EjString {
  throw new Error('runtimeToText: not implemented');
}

// Merges two objects. First argument is preferred in case of key conflict.
// Returned object has sorted keys.
export function runtimeRecConcat(a: EjObject, b:EjObject): EjObject {
  let r = new EjObject();
  let va = a.values;
  let vb = b.values;
  let ka = va.keys().sort();
  let kb = vb.keys().sort();
  let ia = 0, ib= 0;
  while (ia < ka.length && ib < kb.length) {
    if (ka[ia] < kb[ib]) {
      r.values.set(ka[ia], va.get(ka[ia]));
      ia++;
    } else if (ka[ia] > kb[ib]) {
      r.values.set(kb[ib], vb.get(kb[ib]));
      ib++;
    } else {
      r.values.set(ka[ia], vb.get(ka[ia]));
      ia++;
      ib++;
    }
  }
  while (ia < ka.length) {
      r.values.set(ka[ia], va.get(ka[ia]));
      ia++;
  }
  while (ib < kb.length) {
      r.values.set(kb[ib], vb.get(kb[ib]));
      ib++;
  }
  return r;
}

// Variation of runtimeRecConcat which checks equality of duplicate keys
// Returns empty array on merge conflict.
// Returned object has sorted keys.
export function runtimeRecMerge(a: EjObject, b:EjObject): EjArray {
  let r = new EjObject();
  let va = a.values;
  let vb = b.values;
  let ka = va.keys().sort();
  let kb = vb.keys().sort();
  let ia = 0, ib= 0;
  while (ia < ka.length && ib < kb.length) {
    if (ka[ia] < kb[ib]) {
      r.values.set(ka[ia], va.get(ka[ia]));
      ia++;
    } else if (ka[ia] > kb[ib]) {
      r.values.set(kb[ib], vb.get(kb[ib]));
      ib++;
    } else {
      if (!runtimeEqual(va.get(ka[ia]), vb.get(ka[ia])).value) {
        return c_empty_array;
      }
      r.values.set(ka[ia], vb.get(ka[ia]));
      ia++;
      ib++;
    }
  }
  while (ia < ka.length) {
      r.values.set(ka[ia], va.get(ka[ia]));
      ia++;
  }
  while (ib < kb.length) {
      r.values.set(kb[ib], vb.get(kb[ib]));
      ib++;
  }
  return new EjArray([r]);
}

export function runtimeRecRemove(a: EjObject, b:EjString): EjObject {
  let r = new EjObject();
  let v = a.values;
  let k = v.keys();
  for (let i = 0; i < k.length; i++) {
    if (b.value != k[i]) {
      r.values.set(k[i], v.get(k[i]));
    }
  }
  return r;
}

// Remove all keys not listed in b.
// Preserve order of keys.
export function runtimeRecProject(a: EjObject, b:EjArray): EjObject {
  let keep = new Map<string, i32>();
  for(let i = 0; i < b.values.length; i++) {
    let str = cast<EjString>(b.values[i]);
    keep.set(str.value, 42);
  }
  let r = new EjObject();
  let v = a.values;
  let k = v.keys();
  for (let i = 0; i < k.length; i++) {
    if (keep.has(k[i])) {
      r.values.set(k[i], v.get(k[i]));
    }
  }
  return r;
}

export function runtimeRecDot(a: EjObject, k:EjString): EjValue {
  return opAccess(a, k);
}

// n-ary, compiled
// export function runtimeArray(): EjArray {}

export function runtimeArrayLength(a: EjArray) : EjBigInt {
  return new EjBigInt(a.values.length);
}

export function runtimeArrayPush(a: EjArray, b: EjValue) : EjArray {
  return opArrayPush(a, b);
}

export function runtimeArrayAccess(a: EjArray, b: EjBigInt): EjValue {
  return opArrayAccess(a, b);
}

function ejObject(l: Array<Array<EjValue>>): EjObject {
  let obj = new EjObject();
  for (let i=0; i < l.length; i++) {
    obj.set(<EjString>l[i][0], l[i][1]);
  }
  return obj
}

const c_$left = new EjString("$left")
const c_$right = new EjString("$right")

function ejLeft(v: EjValue): EjObject {
  return ejObject([[c_$left, v]]);
}

function ejRight(v: EjValue): EjObject {
  return ejObject([[c_$right, v]]);
}

export function runtimeEither(a: EjObject): EjBool {
  if (a.has(c_$left)){
    return c_true;
  }
  if (a.has(c_$right)) {
    return c_false;
  }
  throw new Error('runtimeEither: invalid arguments');
}

export function runtimeToLeft(a: EjObject): EjValue {
  return runtimeRecDot(a, c_$left);
}

export function runtimeToRight(a: EjObject): EjValue {
  return runtimeRecDot(a, c_$right);
}

const c_$data = new EjString("$data")
const c_$class = new EjString("$class")
const c_none = ejRight(c_null)

export function runtimeUnbrand(a: EjObject): EjValue {
  return runtimeRecDot(a, c_$data);
}

// this is a binary imp ejson operator
// hierarchy is added by the compiler
export function runtimeCast(hierarchy: EjArray, brands: EjArray, x: EjObject) : EjValue {
  let from_brands = cast<EjArray>(runtimeRecDot(x, c_$class)).values;
  let to_brands = brands.values;
  let pairs = hierarchy.values;
  for (let i = 0; i < to_brands.length; i++) {
    let to_brand = cast<EjString>(to_brands[i]).value;
    let to_brand_ok = false;
    for (let j = 0; j < from_brands.length; j++) {
      let from_brand = cast<EjString>(from_brands[j]).value;
      if (to_brand == from_brand) {
        to_brand_ok = true;
        // break j loop
        j = I32.MAX_VALUE - 1;
      } else {
        for (let k = 0; k < pairs.length; k++) {
          let pair = cast<EjArray>(pairs[k]).values;
          assert(pair.length == 2);
          let sub = cast<EjString>(pair[0]).value;
          let sup = cast<EjString>(pair[1]).value;
          if (from_brand == sub && to_brand == sup) {
            to_brand_ok = true;
            // break j loop
            j = I32.MAX_VALUE - 1;
            k = I32.MAX_VALUE - 1;
          }
        }
      }
    }
    if (!to_brand_ok) {
      return c_none;
    }
  }
  return ejLeft(x);
}

export function runtimeDistinct(a: EjArray) : EjArray {
  let result = new Array<EjValue>(0);
  let content = a.values;
  for (let i=0; i < content.length; i=i+1) {
    let v = content[i];
    let dup = false;
    for (let j=i+1; j < content.length; j=j+1) {
      if (runtimeEqual(v,content[j]).value) { dup = true; break; }
    }
    if (!(dup)) { result.push(v); } else { dup = false; }
  }
  return new EjArray(result);
}

export function runtimeSingleton(a: EjArray) : EjObject {
  if (a.values.length == 1) {
    return ejLeft(a.values[0]);
  } else {
    return ejRight(c_null);
  }
}

export function runtimeFlatten(a: EjArray) : EjArray {
  let result = new Array<EjValue>(0);
  let content = a.values;
  for (let iOuter=0; iOuter < content.length; iOuter++) {
    let aInner = changetype<EjArray>(content[iOuter]);
    let aInnerContent = aInner.values;
    for (let iInner=0; iInner < aInnerContent.length; iInner = iInner+1) {
      result.push(aInnerContent[iInner]);
    }
  }
  return new EjArray(result);
}

export function runtimeUnion(a: EjArray, b: EjArray) : EjArray {
  return new EjArray(a.values.concat(b.values));
}

// Remove elements of b from a.
// TODO: runtimeMinus, can we improve complexity?
export function runtimeMinus(a: EjArray, b: EjArray) : EjArray {
  let result = new Array<EjValue>();
  let before = a.values;
  let remove = b.values;
  for (let i=0; i < before.length; i++) {
    let keep = true;
    for (let j=0; j < remove.length; j++) {
      if (runtimeEqual(before[i], remove[j]).value) {
        keep = false;
        break;
      }
    }
    if (keep) {
      result.push(before[i]);
    }
  }
  return new EjArray(result);
}

export function runtimeMin(a: EjArray, b: EjArray) : EjArray {
  throw new Error('runtimeMin: not implemented');
}

export function runtimeMax(a: EjArray, b: EjArray) : EjArray {
  throw new Error('runtimeMax: not implemented');
}

export function runtimeNth(a: EjArray, b: EjBigInt) : EjObject {
  let arr = a.values;
  let i = b.value;
  if (i < 0 || i >= arr.length) return c_none;
  return ejLeft(arr[i32(i)]);
}

// TODO: runtimeCount redundant with opArrayLength
export function runtimeCount(a: EjArray) : EjBigInt {
  return opArrayLength(a);
}

export function runtimeContains(a: EjValue, b: EjArray) : EjBool {
  throw new Error('runtimeContains: not implemented');
}

export function runtimeSort(a: EjArray, b: EjNull) : EjArray {
  throw new Error('runtimeSort: not implemented');
}

export function runtimeGroupBy(a: EjArray, b: EjNull, c:EjNull) : EjArray {
  throw new Error('runtimeGroupBy: not implemented');
}

export function runtimeLength(a: EjString) : EjBigInt {
  throw new Error('runtimeLength: not implemented');
}

export function runtimeSubstring(a: EjString, start: EjBigInt, len:EjBigInt) : EjString {
  throw new Error('runtimeSubstring: not implemented');
}

export function runtimeSubstringEnd(a: EjString, start: EjBigInt) : EjString {
  throw new Error('runtimeSubstringEnd: not implemented');
}

export function runtimeStringJoin(sep: EjString, a: EjArray): EjString {
  throw new Error('runtimeStringJoin: not implemented');
}

export function runtimeLike(reg: EjString, target:EjString): EjBool {
  throw new Error('runtimeLike: not implemented');
}

export function runtimeNatLt(a: EjBigInt, b: EjBigInt): EjBool {
  return new EjBool(a.value < b.value);
}

export function runtimeNatLe(a: EjBigInt, b: EjBigInt): EjBool {
  return new EjBool(a.value <= b.value);
}

export function runtimeNatPlus(a: EjBigInt, b: EjBigInt): EjBigInt {
  return new EjBigInt(a.value + b.value);
}

export function runtimeNatMinus(a: EjBigInt, b: EjBigInt): EjBigInt {
  return new EjBigInt(a.value - b.value);
}

export function runtimeNatMult(a: EjBigInt, b: EjBigInt): EjBigInt {
  return new EjBigInt(a.value * b.value);
}

export function runtimeNatDiv(a: EjBigInt, b: EjBigInt): EjBigInt {
  return new EjBigInt(a.value / b.value);
}

export function runtimeNatRem(a: EjBigInt, b: EjBigInt): EjBigInt {
  return new EjBigInt(a.value % b.value);
}

export function runtimeNatAbs(a: EjBigInt): EjBigInt {
  if (a.value < 0) {
    return new EjBigInt(-a.value);
  } else {
    return a;
  }
}

export function runtimeNatLog2(a: EjBigInt): EjBigInt {
  throw new Error('runtimeNatLog2: not implemented');
}

export function runtimeNatSqrt(a: EjBigInt): EjBigInt {
  throw new Error('runtimeNatSqrt: not implemented');
}

export function runtimeNatMinPair(a: EjBigInt, b: EjBigInt): EjBigInt {
  if (a.value < b.value) {
    return a;
  } else {
    return b;
  }
}

export function runtimeNatMaxPair(a: EjBigInt, b: EjBigInt): EjBigInt {
  if (a.value < b.value) {
    return b;
  } else {
    return a;
  }
}

export function runtimeNatSum(a: EjArray): EjBigInt {
  throw new Error('runtimeNatSum: not implemented');
}

export function runtimeNatMin(a: EjArray): EjBigInt {
  throw new Error('runtimeNatMin: not implemented');
}

export function runtimeNatMax(a: EjArray): EjBigInt {
  throw new Error('runtimeNatMax: not implemented');
}

export function runtimeNatArithMean(a: EjArray): EjBigInt {
  throw new Error('runtimeNatArithMean: not implemented');
}

export function runtimeFloatOfNat(a: EjBigInt): EjNumber {
  // TODO runtimeFloatOfNat : smarter conversion possible?
  let s : string = a.value.toString();
  let x : f64 = F64.parseFloat(s);
  return new EjNumber(x);
}

export function runtimeFloatSum(a: EjArray): EjNumber {
  throw new Error('runtimeFloatSum: not implemented');
}

export function runtimeFloatArithMean(a: EjArray): EjNumber {
  throw new Error('runtimeFloatArithMean: not implemented');
}

export function runtimeFloatMin(a: EjArray): EjNumber {
  throw new Error('runtimeFloatMin: not implemented');
}

export function runtimeFloatMax(a: EjArray): EjNumber {
  throw new Error('runtimeFloatMax: not implemented');
}

export function runtimeNatOfFloat(a: EjNumber): EjBigInt {
  let x : f64 = trunc(a.value);
  let i : i64 = <i64>x;
  return new EjBigInt(i);
}

export function runtimeForeign(): EjNull  {
  throw new Error('runtimeForeign: not implemented');
}
