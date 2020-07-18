open EJson
open ForeignEJson
open ForeignEJsonRuntime
open ImpEJson

type t = Wasm.Ast.module_
val eval : foreign_ejson -> (char list * char list) list -> t -> jbindings -> ejson option
val imp_ejson_to_wasm_ast : foreign_ejson -> foreign_ejson_runtime -> imp_ejson -> t
val to_string : t -> string
