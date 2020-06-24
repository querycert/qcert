(* XXX This is a placeholder *)

open EJson
open ForeignEJson
open ForeignEJsonRuntime
open ImpEJson

type ast
val eval : foreign_ejson -> (char list * char list) list -> ast -> jbindings -> ejson option
val imp_ejson_to_wasm_ast : foreign_ejson -> foreign_ejson_runtime -> imp_ejson -> ast

