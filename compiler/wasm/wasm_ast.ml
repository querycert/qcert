type t = Wasm.Ast.module_

include Wasm_backend.Make(struct
    include EJson
    include EJsonOperators
    include EJsonRuntimeOperators
    include Imp
    include ImpEJson

    type foreign_model = EnhancedEJson.enhanced_ejson
    type foreign_runtime_op = EnhancedEJson.enhanced_foreign_ejson_runtime_op
  end)

(* Qcert compiles queries. There is only one function per [Imp.lib].
 * We name this single function 'qcert_main'.
 * We patch the generic translate and eval functions accordingly.
 *)

let main = Util.char_list_of_string "qcert_main"

let imp_ejson_to_wasm_ast hierarchy = function
  | [ _, fn ] -> imp_ejson_to_wasm_ast hierarchy [ main, fn ]
  | _ -> failwith "Wasm_ast.imp_ejson_to_wasm_ast: single function expected"

let eval module_ env = eval module_ main env
