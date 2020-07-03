const loader = require("@assemblyscript/loader");
const should = require('chai').should();
const fs = require('fs');

function writeString(module, str) {
  return m.exports.__retain(m.exports.__allocString(aStr));
}

describe('AssemblyScript: Ejson operators', function () {
  it('low-level write/read roundtrip', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let t = new m.exports.EjBool(true);
    let f = new m.exports.EjBool(false);
    let pi = new m.exports.EjNumber(Math.PI);
    t.value.should.equal(1);
    f.value.should.equal(0);
    pi.value.should.equal(Math.PI);
    // Strings require some effort.
    let hello_p = m.exports.__retain(m.exports.__allocString("Hello World!"));
    let hello = new m.exports.EjString(hello_p);
    m.exports.__release(hello_p);
    let val_p = hello.value;
    m.exports.__release(hello);
    m.exports.__getString(val_p).should.equal("Hello World!");
    m.exports.__release(val_p);
  });
  it('operator PoC', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let { __release, EjBool, opOr, opNot } = m.exports;
    let t = new EjBool(true);
    let f = new EjBool(false);
    let res = opNot(opOr(t, f));
    __release(t);
    __release(f);
    EjBool.wrap(res).value.should.equal(0);
    __release(res);
  });
});
