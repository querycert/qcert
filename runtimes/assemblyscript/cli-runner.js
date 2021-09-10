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
