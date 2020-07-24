(** Binary encoding for EJson values.
 *
 * This encoding is used as "interface type" for EJson on compiled Wasm
 * queries.
 *
 * The encoding is similar to MessagePack (msgpack.org) but we use much less
 * tags. Every value is prefixed with a 1-byte tag that describes the type of
 * the value. Values of dynamic length (strings, arrays, objects) are
 * additionally prefixed with the length (4-byte unsigned integer). All numbers
 * are stored little-endian. Strings are UTF8 encoded and not terminated.
 *
 * Null
 * | <u8>0 |
 *
 * False
 * | <u8>1 |
 *
 * True
 * | <u8>2 |
 *
 * Number x
 * | <u8>3 | <f64>x |
 *
 * BigInt x
 * | <u8>4 | <f64>x |
 *
 * String s
 * | <u8>5 | <u32>size(s) | s |
 *
 * Array a
 * | <u8>6 | <u32>size(a) | a[0] | a[1] | ...
 *
 * Object o with keys k
 * | <u8>7 | <u32>size(o) | <u32>size(k[0]) | k[0] | o[k[0]] | ...
 *
 * Left x
 * | <u8>8 | x |
 *
 * Right x
 * | <u8>9 | x |
 *)
open EJson

(** We do not support foreign data yet *)
val cejson_to_bytes: _ cejson -> bytes
val ejson_to_bytes: _ ejson -> bytes
val ejson_of_bytes: bytes -> _ ejson
