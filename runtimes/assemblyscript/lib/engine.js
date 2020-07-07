'use strict';

const loader = require("@assemblyscript/loader");
const enc = require('./encoding.js');

async function invoke(runtime, module, arg) {
  let rt = await loader.instantiate(runtime);
  let m = await loader.instantiate(module, { runtime: rt.instance.exports });
  let arg_ptr = enc.write(rt, arg);
  let res_ptr = m.exports.main(arg_ptr);
  let res = enc.read(rt, res_ptr);
  return res;
}

module.exports = { invoke };



