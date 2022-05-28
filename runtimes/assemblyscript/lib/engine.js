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

const loader = require("@assemblyscript/loader");
const bin = require('./binary_encoding.js');

function write(mod, value) {
  let { __alloc, __retain, __release, ejson_of_bytes, memory} = mod.exports;
  let value_bin = bin.ejson_to_bytes(value); // ejson --JS--> binary
  let bytes_ptr = __retain(__alloc(value_bin.byteLength)); // alloc runtime memory
  Buffer.from(value_bin).copy(Buffer.from(memory.buffer, bytes_ptr)); // copy binary value
  return bytes_ptr;
}

function read(mod, ptr) {
  let { memory, ejson_to_bytes } = mod.exports;
  let value = bin.ejson_of_bytes(memory.buffer, ptr); // binary --JS--> ejson
  return value;
}

async function invoke(runtime, module, fn_name, arg) {
  let rt = await loader.instantiate(runtime);
  let m = await loader.instantiate(module, { runtime: rt.instance.exports });
  let arg_ptr = write(rt, arg);
  let res_ptr = m.exports[fn_name](arg_ptr);
  let res = read(rt, res_ptr);
  return res;
}

module.exports = { invoke };
