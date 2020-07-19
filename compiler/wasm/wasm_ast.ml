type t = Wasm.Ast.module_
let eval j w env =
  Wasm.Valid.check_module w;
  failwith "Evaluation not supported"
  (* let inst = Wasm_engine.init w in *)
  (* let arg = EJson.Coq_ejobject env in *)
  (* let res = Wasm_engine.invoke inst arg in *)
  (* Some res *)

let imp_ejson_to_wasm_ast i = Wasm_translate.imp i
let to_string q =
  let sexpr = Wasm.Arrange.module_ q in
  Wasm.Sexpr.to_string 72 sexpr
