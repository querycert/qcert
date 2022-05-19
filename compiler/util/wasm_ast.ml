type t = Wasm.Ast.module_
let eval fe j w env =
  Wasm.Valid.check_module w;
  let inst = Wasm_engine.init w in
  let arg = EJson.Coq_ejobject env in
  let res = Wasm_engine.invoke inst arg in
  Some res

let imp_ejson_to_wasm_ast fe fer i = Wasm_translate.imp i
