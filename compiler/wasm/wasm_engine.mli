open EJson

type instance

val init: Wasm.Ast.module_ -> instance

val invoke: instance -> ejson -> ejson
