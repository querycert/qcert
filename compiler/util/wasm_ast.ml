type t = Wasm.Ast.module_
let eval fe j w env =
  let inst = Wasm_engine.init w in
  match env with
  | [ _, arg ] -> (* There is only one argument *)
    let res = Wasm_engine.invoke inst arg in
    Some res
  | _ -> failwith "Wasm_ast.eval: unexpected number of arguments"

let imp_ejson_to_wasm_ast fe fer i = Wasm_translate.imp i
