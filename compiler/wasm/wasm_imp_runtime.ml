open Wasm_util
module Ir = Wasm_ir

module type CONTEXT = sig
  val memory : Ir.memory
  val alloc_p : Ir.global
  val table: Ir.table
  val constants : string Table.t
  val elems: (int * Ir.func) list
end

module type RUNTIME = sig
  module Ctx : CONTEXT

  val const : ImpEJson.imp_ejson_constant -> Ir.instr
  val c_true : Ir.instr
  val c_false : Ir.instr

  val dot : Ir.func

  val not : Ir.func
  val or_ : Ir.func
  val and_ : Ir.func

  val compare : Ir.cmp_op -> Ir.func
  val equal: Ir.func
end

module Create () : RUNTIME = struct
  open Ir

  let memory = memory 1
  let alloc_p = global ~mutable_:true i32 [i32_const' 0]
  let table = table 10 (* TODO: make sure that this grows automatically on ir -> spec compilation *)
  let constants = Table.create ~element_size:String.length ~initial_offset:0

  let load = load memory

  let const x : instr =
    let s = Wasm_ejson.encode_const x |> Bytes.to_string in
    let offset = Table.insert constants s in
    i32_const' offset

  let c_null = const (Coq_cejnull)
  let c_true = const (Coq_cejbool true)
  let c_false = const (Coq_cejbool false)

  (* null and false are "falsy".
   * null has tag 0. false has tag 1. *)
  let not =
    func ~params:[i32] ~result:[i32]
      [ local_get 0
      ; load i32
      ; i32_const' 1
      ; i32u_cmp Le
      ; if_ ~result:[i32]
          [ c_true ]
          [ c_false ]
      ]

  let boolean_binary op =
    func ~params:[i32; i32] ~result:[i32]
      [ local_get 0
      ; load i32
      ; i32_const' 1
      ; i32u_cmp Gt
      ; local_get 1
      ; load i32
      ; i32_const' 1
      ; i32u_cmp Gt
      ; op
      ; if_ ~result:[i32]
          [ c_true ]
          [ c_false ]
      ]

  let and_ = boolean_binary i32_and
  let or_ = boolean_binary i32_or

  let cmp_val cmp ty =
    func ~params:[ty; ty] ~result:[i32]
      [ local_get 0
      ; local_get 1
      ; cmp Lt
      ; if_ ~result:[i32]
          [ i32_const' (-1) ]
          [ local_get 0
          ; local_get 1
          ; cmp Gt
          ]
      ]

  let cmp_val_i32u = cmp_val i32u_cmp i32
  let cmp_val_i64s = cmp_val i64s_cmp i64
  let cmp_val_f64 = cmp_val f64_cmp f64

  let cmp_ref ty cmp_val =
    func ~params:[i32; i32] ~result:[i32]
      [ local_get 0
      ; load ty
      ; local_get 1
      ; load ty
      ; call cmp_val
      ]

  let cmp_ref_i32u = cmp_ref i32 cmp_val_i32u
  let cmp_ref_i64s = cmp_ref i64 cmp_val_i64s
  let cmp_ref_f64 = cmp_ref f64 cmp_val_f64

  let cmp_box =
    let a, b, res = 0, 1, 2 in
    func ~params:[i32; i32] ~result:[i32] ~locals:[i32]
      [ (* compare tags *) local_get a; local_get b; call cmp_ref_i32u
      ; (* store result *) local_tee res
      ; (* tag equality *) i32_const' 0; eq i32
      ; if_ ~result:[i32]
         [ (* incr pointer to a *) local_get a; i32_const' 4; add i32
         ; (* incr pointer to b *) local_get b; i32_const' 4; add i32
         ; (* load tag *) local_get a; load i32
         ; call_indirect ~params:[i32; i32] ~result:[i32] table
         ]
         [ local_get res ]
      ]

  let cmp_equal =
    func ~params:[i32; i32] ~result:[i32] [ i32_const' 0 ]

  let cmp_ref =
    func ~params:[i32; i32] ~result:[i32]
      [ local_get 0; load i32
      ; local_get 1; load i32
      ; call cmp_box
      ]

  let cmp_string =
    let a, b, res, end_ = 0, 1, 2, 3 in
    func ~params:[i32; i32] ~result:[i32] ~locals:[i32; i32]
      [ (* compare length *) local_get a; local_get b; call cmp_ref_i32u
      ; (* store result *) local_tee res
      ; (* tag equality *) i32_const' 0; eq i32
      ; if_ ~result:[i32]
         [ (* load length *) local_get a; load i32
         ; (* init char pnt a *) local_get a; i32_const' 3; add i32; local_tee a
         ; (* set end addr *) add i32; local_set end_
         ; (* init char pnt b *) local_get b; i32_const' 3; add i32; local_set b
         ; loop ~result:[i32]
           [ (* break condition *) local_get a; local_get end_; i32u_cmp Ge
           ; if_ ~result:[i32]
             [ (* leave loop with equality *) i32_const' 0 ]
             [ (* incr a pnt, load char *) local_get a ; i32_const' 1
             ; add i32; local_tee a; load ~pack:U8 i32
             ; (* incr b pnt, load char *) local_get b ; i32_const' 1
             ; add i32; local_tee b; load ~pack:U8 i32
             ; (* compare, store result*) call cmp_val_i32u ; local_tee res
             ; (* check equality *) i32_const' 0; eq i32
             ; (* conditional continue at top of loop *) br_if 1
             ; local_get res
             ]
           ]
         ]
         [ local_get res ]
      ]

  let cmp_trap =
    func ~params:[i32; i32] ~result:[i32] [ unreachable ]

  let elems =
    [ cmp_equal (* null *)
    ; cmp_equal (* false *)
    ; cmp_equal (* true *)
    ; cmp_ref_f64 (* number *)
    ; cmp_string (* string *)
    ; cmp_trap (* TODO: array *)
    ; cmp_trap (* TODO: object *)
    ; cmp_ref (* left *)
    ; cmp_ref (* right *)
    ; cmp_ref_i64s (* "bigint" *)
    ]

  let compare op =
    func ~params:[i32; i32] ~result:[i32]
      [ local_get 0
      ; local_get 1
      ; call cmp_box
      ; i32_const' (0)
      ; i32s_cmp op
      ; if_ ~result:[i32]
          [ c_true ]
          [ c_false ]
      ]

  let eq_box =
    func ~params:[i32; i32] ~result:[i32]
      [ local_get 0
      ; local_get 1
      ; call cmp_box
      ; i32_const' (0)
      ; eq i32
      ]

  let equal =
    func ~params:[i32; i32] ~result:[i32]
      [ local_get 0
      ; local_get 1
      ; call eq_box
      ; if_ ~result:[i32]
          [ c_true ]
          [ c_false ]
      ]

  let dot =
    let ptr, key, last_ = 0, 1, 2 in
    func ~params:[i32; i32] ~result:[i32] ~locals:[i32]
      [ local_get ptr
      ; load i32
      ; i32_const' 6 (* object tag *)
      ; eq i32
      ; if_ ~result:[i32]
          [ local_get ptr
          ; load ~offset:4 i32
          ; i32_const' 8
          ; mul i32
          ; local_get ptr
          ; add i32
          ; local_set last_
          ; loop ~result:[i32]
              [ local_get ptr
              ; i32_const' 8
              ; add i32
              ; local_tee ptr
              ; local_get last_
              ; i32u_cmp Le
              ; if_ ~result:[i32]
                  [ local_get ptr
                  ; load i32
                  ; local_get key
                  ; call eq_box
                  ; if_ ~result:[i32]
                      [ local_get ptr
                      ; load ~offset:4 i32
                      ; return
                      ]
                      [ br 2 (* jump top of loop *)]
                  ]
                  [ (* key not found *) c_null ]
              ]
          ]
          [ (* not an object *) unreachable ]
      ]

  module Ctx : CONTEXT = struct
    let memory = memory
    let alloc_p = alloc_p
    let constants = constants
    let table = table
    let elems = List.mapi (fun i e -> (i, e)) elems
  end
end

type t = (module RUNTIME)
let create () : t = (module Create () : RUNTIME)
