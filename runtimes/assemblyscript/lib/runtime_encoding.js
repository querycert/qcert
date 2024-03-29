/*
 * Licensed under the Apache License; Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing; software
 * distributed under the License is distributed on an "AS IS" BASIS;
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND; either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

'use strict';

// Write javascript-world EJson value to wasm runtime.
// Return EjValue-pointer in runtime memory.
function write(module, x) {
  let { __retain } = module.exports;
  let m = module.exports;
  function recurse(x) {
    switch (typeof x) {
      case 'boolean':
        return new m.EjBool(x);
      case 'string':
        let str = __retain(m.__allocString(x));
        return new m.EjString(str);
      case 'number':
        return new m.EjNumber(x);
      case 'object':
        {
          if (x === null) {
            return new m.EjNull();
          }
          if (Array.isArray(x)) {
            let values = x.map(recurse);
            let arr =  __retain(m.__allocArray(m.IdArrayEjValue, values));
            return new m.EjArray(arr);
          }
          let keys = Object.getOwnPropertyNames(x);
          if ( keys.length === 1 ) {
            switch (keys[0]) {
              case '$nat' :
                return m.ejBigInt_of_f64(Number(x.$nat));
            }
          }
          let o = new m.EjObject();
          keys.forEach(function (k) {
            let key = recurse(k);
            let val = recurse(x[k]);
            o.set(key,val);
          });
          return o;
        }
      default:
        throw new Error(`unknown type: ${typeof x}`);
    }
  }
  return recurse(x);
}

// Read from EjValue-pointer in wasm runtime memory.
// Return javascript-world EJson value.
function read(module, x) {
  let { __instanceof } = module.exports;
  let m = module.exports;
  function recurse(x) {
    if (__instanceof(x, m.IdEjNull)) {
      return null;
    }
    if (__instanceof(x, m.IdEjBool)) {
      let v = m.EjBool.wrap(x);
      return v.value ? true : false;
    }
    if (__instanceof(x, m.IdEjNumber)) {
      let v = m.EjNumber.wrap(x);
      return v.value;
    }
    if (__instanceof(x, m.IdEjBigInt)) {
      let v = m.EjNumber.wrap(m.runtimeFloatOfNat(x));
      return { $nat: v.value };
    }
    if (__instanceof(x, m.IdEjString)) {
      let v = m.EjString.wrap(x);
      return m.__getString(v.value);
    }
    if (__instanceof(x, m.IdEjArray)) {
      let v = m.EjArray.wrap(x);
      return m.__getArray(v.values).map(recurse);
    }
    if (__instanceof(x, m.IdEjObject)) {
      let v = m.EjObject.wrap(x);
      let o = new Object();
      m.__getArray(v.keys())
        .forEach(remote_key => {
          let val = recurse(v.get(remote_key));
          let local_key = recurse(remote_key);
          o[local_key] = val;
        });
      return o
    }
    if (__instanceof(x, m.IdEjLeft)) {
      let v = m.EjLeft.wrap(x);
      return {$left: recurse(v.value)};
    }
    if (__instanceof(x, m.IdEjRight)) {
      let v = m.EjRight.wrap(x);
      return {$right: recurse(v.value)};
    }
    throw new Error('encoding.js:read(): cannot read value of unsupported type');
  }
  return recurse(x);
}

module.exports = { write, read };
