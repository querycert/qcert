const loader = require("@assemblyscript/loader");
const should = require('chai').should();
const fs = require('fs');
const enc = require('../lib/encoding.js');

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
  it('Ejson write', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let t = enc.write(m, true);
    let f = enc.write(m, false)
    let pi = enc.write(m, Math.PI);
    t.value.should.equal(1);
    f.value.should.equal(0);
    pi.value.should.equal(Math.PI);
    let hello = enc.write(m, "Hello World!");
    let val_p = hello.value;
    m.exports.__release(hello);
    m.exports.__getString(val_p).should.equal("Hello World!");
    m.exports.__release(val_p);
  });
  it('Ejson read', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let n = new m.exports.EjNull();
    should.equal(enc.read(m, n), null);
    let t = new m.exports.EjBool(true);
    let f = new m.exports.EjBool(false);
    let pi = new m.exports.EjNumber(Math.PI);
    enc.read(m, t).should.equal(true);
    enc.read(m, f).should.equal(false);
    enc.read(m, pi).should.equal(Math.PI);
    // Strings require some effort.
    let hello_p = m.exports.__retain(m.exports.__allocString("Hello World!"));
    let hello = new m.exports.EjString(hello_p);
    m.exports.__release(hello_p);
    enc.read(m, hello).should.equal("Hello World!");
    let val_p = hello.value;
    m.exports.__release(hello);
    m.exports.__getString(val_p).should.equal("Hello World!");
    m.exports.__release(val_p);
  });
  it('Ejson read/write roundtrip', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let t = enc.write(m, true);
    let f = enc.write(m, false)
    let pi = enc.write(m, Math.PI);
    let hello = enc.write(m, "Hello World!");
    enc.read(m, t).should.equal(true);
    enc.read(m, f).should.equal(false);
    enc.read(m, pi).should.equal(Math.PI);
    enc.read(m, hello).should.equal("Hello World!");
    // Arrays
    let a0 = [1,2,3];
    let a1 = [];
    let a2 = ['a', "abc", 1, null];
    enc.read(m, enc.write(m, a0)).should.deep.equal(a0);
    enc.read(m, enc.write(m, a1)).should.deep.equal(a1);
    enc.read(m, enc.write(m, a2)).should.deep.equal(a2);
    // Objects
    let o0 = { a: 'a', b: 'b' };
    let o1 = {};
    let o2 = {'null': null, arr: [a0, a1, a2], pi: Math.PI};
    enc.read(m, enc.write(m, o0)).should.deep.equal(o0);
    enc.read(m, enc.write(m, o1)).should.deep.equal(o1);
    enc.read(m, enc.write(m, o2)).should.deep.equal(o2);
  });
});
