const string_encoder = new TextEncoder();

class Allocator {
  constructor(memory, alloc_p) {
    this.view = new DataView(memory.buffer);
    this.alloc_p = alloc_p;
  }

  // <i32u> 0
  null_() {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 0, true);
    this.alloc_p.value += 4;
    return p;
  }

  // <i32u> 1
  false_() {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 1, true);
    this.alloc_p.value += 4;
    return p;
  }

  // <i32u> 2
  true_() {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 2, true);
    this.alloc_p.value += 4;
    return p;
  }

  // <i32u> 3 || <f64> x
  number(x) {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 3, true);
    this.view.setFloat64(p + 4, x, true);
    this.alloc_p.value += 12;
    return p;
  }

  // <i32u> 4 || len(bytes) || <i8u> bytes[0] || bytes[1] || ...
  string(x) {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 4, true);
    const u8 = new Uint8Array(this.view.buffer, p + 8);
    const n = string_encoder.encodeInto(x, u8).written;
    this.view.setUint32(p + 4, n, true);
    this.alloc_p.value += 8 + n;
    return p;
  }

  // <i32u> 5 || len(x) || x[0] || x[1] || ...
  array(x) {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 5, true);
    let n = 0;
    x.forEach(x => {
      this.view.setUint32(p + 8 + 4 * n, x, true);
      n += 1;
    });
    this.view.setUint32(p + 4, n, true);
    this.alloc_p.value += 8 + n * 4;
    return p;
  }

  // <i32u> 6 || len(x) || x[0][0] || x[0][1] || x[1][0] || x[1][1] || ...
  object(x) {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 6, true);
    let n = 0;
    x.forEach(x => {
      this.view.setUint32(p + 8  + n * 4, x[0], true);
      this.view.setUint32(p + 12 + n * 4, x[1], true);
      n += 1;
    });
    this.view.setUint32(p + 4, n, true);
    this.alloc_p.value += 8 + n * 8;
    return p;
  }

  // <i32u> 7 || x
  left(x) {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 7, true);
    this.view.setUint32(p + 4, x, true);
    this.alloc_p.value += 8;
    return p;
  }

  // <i32u> 8 || x
  right(x) {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 8, true);
    this.view.setUint32(p + 4, x, true);
    this.alloc_p.value += 8;
    return p;
  }

  // <i32u> 9 || <i64> x
  nat(x) {
    const p = this.alloc_p.value;
    this.view.setUint32(p, 9, true);
    this.view.setBigInt64(p + 4, x, true);
    this.alloc_p.value += 12;
    return p;
  }
}

export function write(memory, alloc_p, x) {
  const alloc = new Allocator(memory, alloc_p);
  function recurse(x) {
    switch (typeof x) {
    case 'boolean':
      if (x) {
        return alloc.true_();
      } else {
        return alloc.false_();
      }
    case 'string':
      return alloc.string(x);
    case 'number':
      return alloc.number(x);
    case 'object':
    {
      if (x === null) {
        return alloc.null_();
      }
      if (Array.isArray(x)) {
        return alloc.array(x.map(x => recurse(x)));
      }
      let keys = Object.getOwnPropertyNames(x).sort();
      if ( keys.length === 1 ) {
        switch (keys[0]) {
        case '$left' : return alloc.left(recurse(x.$left));
        case '$right' : return alloc.right(recurse(x.$right));
        case '$nat' : return alloc.nat(x.$nat);
        }
      }
      return alloc.object(keys.map(k => [recurse(k), recurse(x[k])]));
    }
    default:
      throw new Error(`unknown type: ${typeof x}`);
    }
  }
  return recurse(x);
}

export function read(memory, p) {
  const view = new DataView(memory.buffer);
  function recurse(p) {
    switch(view.getUint32(p, true)) {
    case 0:
      return null;
    case 1:
      return false;
    case 2:
      return true;
    case 3: // number
      return view.getFloat64(p + 4, true);
    case 4: { // string
      let n = view.getUint32(p + 4, true);
      let b = new Uint8Array(memory.buffer, p + 8, n);
      return (new TextDecoder('utf8').decode(b));
    }
    case 5: { // array
      let n = view.getUint32(p + 4, true);
      let array = [];
      let pos = p + 8;
      for (let i=0; i < n; i++) {
        array[i] = recurse(view.getUint32(pos, true));
        pos += 4;
      }
      return array;
    }
    case 6: { // object
      let n = view.getUint32(p + 4, true);
      let object = {};
      let pos = p + 8;
      for (let i=0; i < n; i++) {
        let key = recurse(view.getUint32(pos, true));
        if (typeof key !== 'string') {
          throw new Error('invalid value');
        }
        object[key] = recurse(view.getUint32(pos + 4, true));
        pos += 8;
      }
      return object;
    }
    case 7: // left
      return {$left: recurse(view.getUint32(p + 4, true))};
    case 8: // right
      return {$right: recurse(view.getUint32(p + 4, true))};
    case 9: // i64
      return {$nat: view.getBigInt64(p + 4, true)};
    default:
      throw new Error('unknown tag');
    }
  }
  return recurse(p);
}
