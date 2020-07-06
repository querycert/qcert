import {read, write} from './encoding.js';

async function run(input, wasm) {
  let arg = fetch(input)
    .then(x => x.json());
  let inst =
    WebAssembly.instantiateStreaming(fetch(wasm))
    .then(x => x.instance);
  Promise.all([arg, inst])
    .then(x => {
      let arg = x[0];
      let inst = x[1];
      let arg_p = write(inst.exports.memory, inst.exports.alloc_p, arg);
      let ret_p = inst.exports.main(arg_p);
      let ret = read(inst.exports.memory, ret_p);
      console.log("Contents of: " + input);
      console.log(arg);
      console.log("Running " + wasm + " on " + input + " returns");
      console.log(ret);
    });
};

async function main() {
  await run("tests/oql/wasm.input", "tests/oql/wasm0.wasm");
  await run("tests/oql/wasm.input", "tests/oql/wasm1.wasm");
  await run("tests/oql/wasm.input", "tests/oql/wasm2.wasm");
  await run("tests/oql/wasm.input", "tests/oql/wasm3.wasm");
  await run("tests/oql/wasm.input", "tests/oql/wasm4.wasm");
  await run("tests/oql/wasm.input", "tests/oql/wasm5.wasm");
};

main();
