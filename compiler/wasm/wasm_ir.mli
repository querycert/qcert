type type_

val i32: type_
val i64: type_
val f32: type_
val f64: type_

type instr

val unreachable : instr
val nop : instr
val i32_const : int32 -> instr
val i32_const' : int -> instr

type cmp_op = Ge | Gt | Le | Lt

val i32s_cmp : cmp_op -> instr
val i32u_cmp : cmp_op -> instr
val i64s_cmp : cmp_op -> instr
val i64u_cmp : cmp_op -> instr
val f32_cmp : cmp_op -> instr
val f64_cmp : cmp_op -> instr

val eq : type_ -> instr
val add : type_ -> instr

val i32_and : instr
val i64_and : instr
val i32_or : instr
val i64_or : instr

(** {2} local variables *)

val local_get : int -> instr
val local_set : int -> instr
val local_tee : int -> instr

(** {2} control structure *)

val if_ :
  ?params: type_ list ->
  ?result: type_ list ->
  instr list -> instr list -> instr

val loop: ?result: type_ list -> instr list -> instr

val br: int -> instr
val br_if: int -> instr

(** {2} functions *)

type func

val func:
  ?params: type_ list ->
  ?result: type_ list ->
  ?locals: type_ list -> instr list -> func

val call: func -> instr

(** {2} tables **)

type table

val table: ?max_size:int -> int -> table
val call_indirect:
  ?params: type_ list ->
  ?result: type_ list -> table -> instr

(** {2} global variables *)

type global

val global: mutable_:bool -> type_ -> instr list -> global

val global_get : global -> instr
val global_set : global -> instr

(** {2} memory *)

type memory

val memory: ?max_size:int -> int -> memory

type pack = S8 | S16 | S32 | U8 | U16 | U32

val load : memory -> ?pack:pack -> ?offset:int -> type_ -> instr

(** {2} module *)

type 'a export = string * 'a

type module_ =
  { start: func option
  ; funcs: func export list
  ; globals: global export list
  ; memories: memory export list
  ; tables: table export list
  ; data: (memory * int * string) list
  ; elems: (table * int * func) list
  }

val module_to_spec: module_ -> Wasm.Ast.module_
