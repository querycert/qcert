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

const _ = require('lodash');
const fs = require('fs');
const engine = require('./lib/engine.js');

async function main(runtime, module, input, expected) {
  let rt = fs.readFileSync(runtime);
  let mod = fs.readFileSync(module);
  let arg = JSON.parse(fs.readFileSync(input));
  let exp = JSON.parse(fs.readFileSync(expected));
  let res;
  let err;
  try {
    res = await engine.invoke(rt, mod, "qcert_main", arg);
  } catch(err) {
    err = err;
    res = { "error": "Eval failed" }
  }
  if (! _.isEqual(res, exp)) {
    console.log("TEST FAILED");
    console.log("arguments:");
    console.log({runtime, module, input, expected});
    console.log("input:");
    console.log(arg);
    console.log("expected output:");
    console.log(JSON.stringify(exp, null, 2));
    if (err) {
      console.log("exception:");
      console.log(err);
      process.exit(2);
    } else {
      console.log("output:");
      console.log(JSON.stringify(res, null, 2));
      process.exit(1)
    }
  }
}

const rt = process.argv[2];
const mod = process.argv[3];
const arg = process.argv[4];
const exp = process.argv[5];

main(rt, mod, arg, exp);
