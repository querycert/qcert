'use strict';

// This follows closely the ejson_(to|of)_bytes function in the Assemblyscript
// runtime.

class BytesBuilder {
  // segments: Array<ArrayBuffer>
  // size: i32

  constructor() { this.segments = []; this.size = 0; }

  // expects
  // s: ArrayBuffer
  // returns void
  append(s) {
    this.segments.push(s);
    this.size += s.byteLength;
  }

  // returns ArrayBuffer
  finalize() {
    let b = new ArrayBuffer(this.size);
    let p = 0;
    let v = new Uint8Array(b);
    for (let i = 0; i < this.segments.length; i++) {
      let s = new Uint8Array(this.segments[i]);
      // this is byte-by-byte copy. Could be much faster when copying words.
      for (let j = 0; j < s.length; j++) {
        v[p] = s[j];
        p++;
      }
    }
    return b;
  }
}

// expects
// s: string
// return ArrayBuffer holding utf8 encoded string
function string_to_bytes(s) {
  let utf8 = Buffer.from(s, 'utf8');
  let buf = new ArrayBuffer(utf8.length);
  utf8.copy(Buffer.from(buf))
  return buf;
}

// expects
// b: BytesBuilder
// x: EJson value
// returns void
function ejson_to_bytes_(b, x) {
  switch (typeof x) {
    case 'boolean': {
      let s = new ArrayBuffer(1);
      (new Uint8Array(s))[0] = x ? 2 : 1; // tag
      b.append(s);
      return;
    }
    case 'string': {
      let utf8 = string_to_bytes(x)
      let s = new Uint8Array(5);
      let v = new DataView(s.buffer);
      s[0] = 5; // tag
      v.setUint32(1, utf8.byteLength, true);
      b.append(s.buffer);
      b.append(utf8);
      return;
    }
    case 'number': {
      let s = new ArrayBuffer(9);
      let v = new DataView(s);
      v.setUint8(0, 3); // tag
      v.setFloat64(1, x, true);
      b.append(s);
      return;
    }
    case 'object': {
      if (x === null) {
        let s = new ArrayBuffer(1);
        (new Uint8Array(s))[0] = 0; // tag
        b.append(s);
        return;
      }
      if (Array.isArray(x)) {
        let s = new Uint8Array(5);
        let v = new DataView(s.buffer);
        s[0] = 6; // tag
        v.setUint32(1, x.length, true);
        b.append(s.buffer);
        for (let i = 0; i < x.length; i++) {
          ejson_to_bytes_(b, x[i]);
        }
        return;
      }
      let keys = Object.getOwnPropertyNames(x);
      if ( keys.length === 1 ) {
        switch (keys[0]) {
          case '$nat': {
            let s = new ArrayBuffer(9);
            let v = new DataView(s);
            v.setUint8(0, 4); // tag
            v.setBigInt64(1, BigInt(x.$nat), true);
            b.append(s);
            return;
          }
        }
      }
      // it's an object!
      let s = new Uint8Array(5);
      let v = new DataView(s.buffer);
      s[0] = 7; // tag
      v.setUint32(1, keys.length, true);
      b.append(s.buffer);
      for (let i = 0; i < keys.length; i++) {
        let k = keys[i];
        // write key as utf8 string with byte length prefix
        let utf8 = string_to_bytes(k);
        let s = new Uint8Array(4);
        let v = new DataView(s.buffer);
        v.setUint32(0, utf8.byteLength, true);
        b.append(s.buffer);
        b.append(utf8);
        // write value
        ejson_to_bytes_(b, x[k]);
      }
      return;
    }
    default:
      throw new Error(`unknown type: ${typeof x}`);
  }
}

// expects
// x: EJson value
// returns ArrayBuffer
function ejson_to_bytes(x) {
  let b = new BytesBuilder();
  ejson_to_bytes_(b, x);
  return b.finalize();
}

module.exports = { ejson_to_bytes };

/* TODO: ejson_of_bytes
