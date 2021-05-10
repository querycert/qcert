let string = Stringified.runtime

let wasm_ast =
  lazy (
    let open Wasm in
    let m = Decode.decode "runtime.wasm" string in
    let () = Valid.check_module m in
    m
  )
