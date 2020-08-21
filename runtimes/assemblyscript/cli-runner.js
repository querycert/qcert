'use strict';

const fs = require('fs');
const engine = require('./lib/engine.js');

async function main(runtime, module, input, expected) {
  console.log("invoke:");
  console.log({runtime, module, input, expected});
  let rt = fs.readFileSync(runtime);
  let mod = fs.readFileSync(module);
  let arg = JSON.parse(fs.readFileSync(input));
  console.log("input:");
  console.log(arg);
  let exp = JSON.parse(fs.readFileSync(expected));
  console.log("expected:");
  console.log(JSON.stringify(exp, null, 2));
  try {
    let res = await engine.invoke(rt, mod, "qcert_main", arg);
    console.log("output:");
    console.log(JSON.stringify(res, null, 2));
  } catch(err) {
    console.log("output:");
    let res = {
      "error": "Eval failed",
      "message": err.message
    };
    console.log(JSON.stringify(res, null,2));
  }
}

const rt = process.argv[2];
const mod = process.argv[3];
const arg = process.argv[4];
const exp = process.argv[5];

main(rt, mod, arg, exp);