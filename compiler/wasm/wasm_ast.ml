type t = Wasm.Ast.module_

include Wasm_backend.Make(struct
    include EJson
    include EJsonOperators
    include EJsonRuntimeOperators
    include Imp
    include ImpEJson
  end)
