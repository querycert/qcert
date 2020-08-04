'use strict';

const loader = require("@assemblyscript/loader");
const enc = require('./encoding.js');

async function invoke(runtime, module, hierarchy, arg) {
  let rt = await loader.instantiate(runtime);
  let m = await loader.instantiate(module, { runtime: rt.instance.exports });
  let hierarchy_ptr = enc.write(rt, hierarchy);
  let arg_ptr = enc.write(rt, arg);
  let res_ptr = m.exports.qcert_main(hierarchy_ptr, arg_ptr);
  let res = enc.read(rt, res_ptr);
  return res;
}

module.exports = { invoke };



