open EJson
open ForeignEJson
open ForeignEJsonRuntime
open ImpEJson

type t = Wasm.Ast.module_
val eval : (char list * char list) list -> t -> 'a jbindings -> ('a ejson) option
val imp_ejson_to_wasm_ast : ('a,'b) imp_ejson -> t
val to_string : t -> string
