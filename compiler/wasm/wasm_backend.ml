open Wasm

(** list of (sub, sup) brand relation *)
type brand_hierarchy = (char list * char list) list

module Make (ImpEJson: Wasm_intf.IMP_EJSON) : sig
  val to_string : Wasm.Ast.module_ -> string

  open ImpEJson

  val runtime: Wasm.Ast.module_

  (** [eval wasm_module fn_name environment *)
  val eval : Wasm.Ast.module_ -> char list -> (char list * 'a ejson) list -> ('a ejson) option

  (* XXX In ('a -> string), string is really ForeignWSON.foreign_wson *)
  val imp_ejson_to_wasm_ast : brand_hierarchy -> ('a -> string) -> ('a,'b) imp_ejson -> Wasm.Ast.module_

  val string_of_operator: imp_ejson_op -> string
  val string_of_runtime_operator: 'a imp_ejson_runtime_op -> string
end = struct
  open ImpEJson
  module Encoding = Wasm_binary_ejson.Make(ImpEJson)

  let runtime = Lazy.force Assemblyscript_runtime.wasm_ast

  let ejson_of_cejson = function
    | Coq_cejnull -> Coq_ejnull
    | Coq_cejbool x -> Coq_ejbool x
    | Coq_cejnumber x -> Coq_ejnumber x
    | Coq_cejbigint x -> Coq_ejbigint x
    | Coq_cejstring x -> Coq_ejstring x
    | Coq_cejforeign x -> Coq_ejforeign x

  let ejson_of_brand_relations h =
    let x =
      List.map (fun (sub, sup) ->
          Coq_ejarray [Coq_ejstring sub; Coq_ejstring sup]
        ) h
    in
    Coq_ejarray x

  module Eval = struct
    exception Wasm_runtime of { msg: string; pos: string }

    (* assemblyscript error handler imported by runtime *)
    let abort mem_ref =
      let read_string ptr =
        let ptr = Int64.of_int32 ptr in
        match !mem_ref with
        | None -> failwith "wasm_backend.ml:abort: invalid mem_ref"
        | Some mem ->
          let size =
            match Memory.load_value mem (Int64.sub ptr (Int64.of_int 4)) Int32.zero I32Type with
            | I32 x -> Int32.to_int x
            | _ -> failwith "wasm_backend.ml:abort: invalid load"
            | exception Wasm.Memory.Bounds ->
              let msg =
                Printf.sprintf
                  "wasm_backend.ml:abort: bounds %Li/%i"
                  ptr
                  (Int64.to_int Memory.page_size * Int32.to_int (Memory.size mem))
              in
              failwith msg
          in
          (* assemblyscript string is utf-16 *)
          let utf16 = Memory.load_bytes mem ptr size in
          (* we abuse that utf16 and utf8 overlap on the least significant byte *)
          let buf = Bytes.create (size / 2) in
          String.iteri (fun i c ->
              if i mod 2 = 0 then
                let c =
                  (* filter for printable characters *)
                  if Char.code c < 32 || Char.code c > 126 then '_' else c
                in
                Bytes.set buf (i / 2) c
            ) utf16;
          Bytes.to_string buf
      in
      let f = function
        | Values.[I32 msg ; I32 _file; I32 line; I32 column] ->
            let msg = read_string msg
            and pos =
              Printf.sprintf "runtime.ts:%s:%s"
                (Int32.to_string line)
                (Int32.to_string column)
            in raise (Wasm_runtime { msg; pos })
        | _ -> failwith "wasm_backend.ml:abort: malformed arguments"
      in
      Func.alloc_host Types.(FuncType ([I32Type; I32Type; I32Type; I32Type], [])) f

    let eval module_ fn env =
      let mem_ref = ref None in
      let rt = Eval.init runtime [ExternFunc (abort mem_ref)] in
      let () = Valid.check_module module_ in
      let mod_ =
        let imports = List.map (fun (import : Ast.import) ->
            if import.it.module_name <> (Utf8.decode "runtime") then
              failwith "cannot satisfy import from unknown module";
            match Instance.export rt import.it.item_name with
            | None -> failwith ("cannot satisfy import of function " ^
                                (Utf8.encode import.it.item_name))
            | Some export ->
              let is = Instance.extern_type_of export
              and should = Ast.import_type module_ import
              in
              if is <> should then failwith "type mismatch on import";
              export
          ) module_.it.imports
        in
        Eval.init module_ imports
      and rt_alloc =
        match Instance.export rt (Utf8.decode "__alloc") with
        | Some (ExternFunc f) -> f
        | _ -> failwith "runtime module should export __alloc function"
      and rt_retain =
        match Instance.export rt (Utf8.decode "__retain") with
        | Some (ExternFunc f) -> f
        | _ -> failwith "runtime module should export __retain function"
      and rt_mem =
        match Instance.export rt (Utf8.decode "memory") with
        | Some (ExternMemory x) ->
            mem_ref := Some x;
            x
        | _ -> failwith "runtime module should export its memory"
      in
      let write_ejson x =
        let bin = Encoding.ejson_to_bytes x in
        let n = Bytes.length bin in
        let x =
          Eval.invoke rt_alloc [I32 (Int32.of_int n); I32 (Int32.zero)]
          |> Eval.invoke rt_retain
        in
        let bin_ptr =
          match x with
          | [I32 x] -> x
          | _ -> failwith "invalid runtime: type of __alloc or __retain"
        in
        let () =
          Memory.store_bytes rt_mem (Int64.of_int32 bin_ptr) (Bytes.to_string bin)
        in
        bin_ptr
      in
      let main =
        let fn = Util.string_of_char_list fn in
        match Instance.export mod_ (Utf8.decode fn) with
        | Some (ExternFunc f) -> f
        | _ ->
          let msg =
            Printf.sprintf
              "module does not export function %s which should be run" fn
          in
          failwith msg
      and argument_ptr = write_ejson (Coq_ejobject env)
      in
      let result_ptr =
        match Eval.invoke main [I32 argument_ptr] with
        | [I32 x] -> x
        | _ -> failwith "invalid module: return value of evaluated function"
      in
      let result =
        let n =
          match Memory.load_value rt_mem Int64.(sub (of_int32 result_ptr) (of_int 4))
                  Int32.zero Types.I32Type with
          | I32 x -> Int32.to_int x
          | _ -> failwith "could not read length of result"
        in
        Memory.load_bytes rt_mem (Int64.of_int32 result_ptr) n
        |> Bytes.of_string
        |> Encoding.ejson_of_bytes
      in
      Some result

    let eval module_ fn env =
      let s = Util.char_list_of_string in
      let error msg =
        Some (Coq_ejobject [s "error", Coq_ejstring (s msg)])
      in
      try eval module_ fn env with
      | Wasm_runtime {msg; pos} ->
        let msg = Printf.sprintf "Assemblyscript Error in %s: %s" pos msg in
        error msg
      | e ->
        let msg = Printexc.to_string e in
        error msg
  end

  module Translate = struct
    open Wasm_util
    module Ir = Wasm_ir

    module ImportSet = Set.Make( struct
        type t = Ir.import
        let compare = Stdlib.compare
      end)

    type 'a module_context =
      { mutable imports : ImportSet.t
      ; memory: Ir.memory
      ; constants: ('a ejson) Table.t
      ; brand_hierarchy : Ir.instr
      }

    type 'a function_context =
      { locals : char list Table.t
      ; ctx: ('a module_context)
      }

    module Constants = struct
      let encode x =
        let raw = Encoding.ejson_to_bytes x in
        let n = Bytes.length raw in
        let b = Bytes.create ((((n + 7) lsr 3) lsl 3) + 8) in
        Bytes.set_int32_le b 0 Int32.zero (* initialize foreign ptr *);
        Bytes.set_int32_le b 4 (Int32.of_int n) (* set length *);
        Bytes.set_int64_le b (Bytes.length b - 8) Int64.zero (* pad with zeroes *);
        Bytes.blit raw 0 b 8 n; (* write actual binary constant *)
        b

      (* Copy constant (bytes) in 8 byte chunks and parse on runtime side. *)
      (* Copies 0-7 bytes too much, thus we pad with zeroes in [encode]. *)
      let alloc_const (ctx: _ module_context) : Ir.func =
        let open Ir in
        let foreign ~params ~result name =
          let f, import = Ir.import_func ~params ~result "runtime" name in
          ctx.imports <- ImportSet.add import ctx.imports;
          f
        in
        (* local_ptr: pointer to start of constant in local memory
         * local_mov: pointer to current position in local memory
         * buf_ptr: pointer to start of buffer in remote memory
         * buf_mov: pointer to current position in remote buffer
         * foreign_ptr: pointer to constant in remote memory
         * n: bytes still to be copied
        *)
        let local_ptr, local_mov, buf_ptr, buf_mov, foreign_ptr, n  = 0, 1, 2, 3, 4, 5 in
        func ~params:[i32] ~result:[i32] ~locals:[i32; i32; i32; i32; i32]
          [ local_get local_ptr
          ; load ctx.memory ~offset:4 i32
          ; local_tee n (* n = byte length of constant *)
          ; call (foreign ~params:[i32] ~result:[i32] "alloc_bytes")
          ; local_set buf_ptr
          ; i32_const' 0 ; local_set buf_mov (* buf_mov = 0 *)
          ; local_get local_ptr ; i32_const' 8 ; add i32
          ; local_set local_mov (* local_mov = local_ptr + 8 *)
          ; loop
              [ local_get n
              ; i32_const' 0
              ; i32s_cmp Gt
              ; if_ (* n > 0 *)
                  [ local_get buf_ptr
                  ; local_get buf_mov
                  ; local_get local_mov
                  ; load ctx.memory i64
                  ; call (foreign ~params:[i32; i32; i64] ~result:[] "bytes_set_i64")
                  ; local_get buf_mov ; i32_const' 8 ; add i32 (* buf_mov += 8 *)
                  ; local_set buf_mov
                  ; local_get local_mov ; i32_const' 8 ; add i32 (* local_mov += 8 *)
                  ; local_set local_mov
                  ; local_get n; i32_const' 8; sub i32 (* n -= 8 *)
                  ; local_set n
                  ; br 1 (* repeat loop *)
                  ]
                  []
              ]
          ; local_get buf_ptr
          ; call (foreign ~params:[i32] ~result:[i32] "ejson_of_bytes")
          ; local_set foreign_ptr
          ; local_get buf_ptr
          ; call (foreign ~params:[i32] ~result:[] "__release")
          ; local_get foreign_ptr
          ]

      let get_const ctx : Ir.func =
        let open Ir in
        let local_ptr, foreign_ptr = 0, 1 in
        func ~params:[i32] ~result:[i32] ~locals:[i32]
          [ local_get local_ptr
          ; load ctx.memory i32
          ; local_tee foreign_ptr
          ; i32_eqz (* foreign_ptr = null: constant not yet allocated in runtime *)
          ; if_
              [ local_get local_ptr
              ; local_get local_ptr
              ; call (alloc_const ctx)
              ; local_tee foreign_ptr
              ; store ctx.memory i32
              ] []
          ; local_get foreign_ptr
          ]
    end

    let const ctx c : Ir.instr =
      let offset = Table.insert ctx.constants c in
      let open Ir in
      block ~result:[i32]
        [ i32_const' offset ; call (Constants.get_const ctx) ]

    (* must align with function names in the runtime module *)
    let string_of_op = function
      | EJsonOpNot -> "opNot"
      | EJsonOpNeg -> "opNeg"
      | EJsonOpAnd -> "opAnd"
      | EJsonOpOr -> "opOr"
      | EJsonOpLt -> "opLt"
      | EJsonOpLe -> "opLe"
      | EJsonOpGt -> "opGt"
      | EJsonOpGe -> "opGe"
      | EJsonOpAddString -> "opAddString"
      | EJsonOpAddNumber -> "opAddNumber"
      | EJsonOpSub -> "opSub"
      | EJsonOpMult -> "opMult"
      | EJsonOpDiv -> "opDiv"
      | EJsonOpStrictEqual -> "opStrictEqual"
      | EJsonOpStrictDisequal -> "opStrictDisequal"
      | EJsonOpArray -> "opArray"
      | EJsonOpArrayLength -> "opArrayLength"
      | EJsonOpArrayPush -> "opArrayPush"
      | EJsonOpArrayAccess -> "opArrayAccess"
      | EJsonOpObject _ -> "opObject"
      | EJsonOpAccess _ -> "opAccess"
      | EJsonOpHasOwnProperty _ -> "opHasOwnProperty"
      | EJsonOpMathMin -> "opMathMin"
      | EJsonOpMathMax -> "opMathMax"
      | EJsonOpMathPow -> "opMathPow"
      | EJsonOpMathExp -> "opMathExp"
      | EJsonOpMathAbs -> "opMathAbs"
      | EJsonOpMathLog -> "opMathLog"
      | EJsonOpMathLog10 -> "opMathLog10"
      | EJsonOpMathSqrt -> "opMathSqrt"
      | EJsonOpMathCeil -> "opMathCeil"
      | EJsonOpMathFloor -> "opMathFloor"
      | EJsonOpMathTrunc -> "opMathTrunc"

    let op_trivial ctx op : Ir.instr =
      let foreign params result =
        let fname = string_of_op op in
        let f, import = Ir.import_func ~params ~result "runtime" fname in
        ctx.imports <- ImportSet.add import ctx.imports;
        Ir.call f
      in
      let open Ir in
      match (op : imp_ejson_op) with
      | EJsonOpNot -> foreign [i32] [i32]
      | EJsonOpNeg -> foreign [i32] [i32]
      | EJsonOpAnd -> foreign [i32; i32] [i32]
      | EJsonOpOr -> foreign [i32; i32] [i32]
      | EJsonOpLt -> foreign [i32; i32] [i32]
      | EJsonOpLe -> foreign [i32; i32] [i32]
      | EJsonOpGt -> foreign [i32; i32] [i32]
      | EJsonOpGe -> foreign [i32; i32] [i32]
      | EJsonOpAddString -> foreign [i32; i32] [i32]
      | EJsonOpAddNumber -> foreign [i32; i32] [i32]
      | EJsonOpSub -> foreign [i32; i32] [i32]
      | EJsonOpMult -> foreign [i32; i32] [i32]
      | EJsonOpDiv -> foreign [i32; i32] [i32]
      | EJsonOpStrictEqual -> foreign [i32; i32] [i32]
      | EJsonOpStrictDisequal -> foreign [i32; i32] [i32]
      | EJsonOpArray -> failwith "n-ary EJsonOpArray is compiled below"
      | EJsonOpArrayLength -> foreign [i32] [i32]
      | EJsonOpArrayPush -> foreign [i32; i32] [i32]
      | EJsonOpArrayAccess -> foreign [i32; i32] [i32]
      | EJsonOpObject _ -> failwith "n-ary EJsonOpObject is compiled below"
      | EJsonOpAccess _ -> foreign [i32; i32] [i32]
      | EJsonOpHasOwnProperty _ -> foreign [i32; i32] [i32]
      | EJsonOpMathMin -> foreign [i32; i32] [i32]
      | EJsonOpMathMax -> foreign [i32; i32] [i32]
      | EJsonOpMathPow -> foreign [i32; i32] [i32]
      | EJsonOpMathExp -> foreign [i32] [i32]
      | EJsonOpMathAbs -> foreign [i32] [i32]
      | EJsonOpMathLog -> foreign [i32] [i32]
      | EJsonOpMathLog10 -> foreign [i32] [i32]
      | EJsonOpMathSqrt -> foreign [i32] [i32]
      | EJsonOpMathCeil -> foreign [i32] [i32]
      | EJsonOpMathFloor -> foreign [i32] [i32]
      | EJsonOpMathTrunc -> foreign [i32] [i32]

    let op_n_ary ctx op args : Ir.instr =
      let foreign params result fname =
        let f, import = Ir.import_func ~params ~result "runtime" fname in
        ctx.ctx.imports <- ImportSet.add import ctx.ctx.imports;
        Ir.call f
      in
      let open Ir in
      match (op : imp_ejson_op) with
      | EJsonOpObject keys ->
        let bindings = List.combine keys args in
        block ~result:[i32] (
          [ i32_const' 0
          ; foreign [i32] [i32] "EjObject#constructor"
          ] @
          ( List.map (fun (k, v) ->
                [ const ctx.ctx (Coq_ejstring k)
                ; v
                ; foreign [i32; i32; i32] [i32] "EjObject#set"
                ]
              ) bindings
            |> List.concat )
        )
      | EJsonOpArray ->
        block ~result:[i32] (
          [ i32_const' 0
          ; i32_const' (List.length args)
          ; foreign [i32; i32] [i32] "EjArrayBuilder#constructor"
          ] @
          ( List.map (fun x ->
                [ x
                ; foreign [i32; i32] [i32] "EjArrayBuilder#put"
                ]
              ) args
            |> List.concat ) @
          [ foreign [i32] [i32] "EjArrayBuilder#finalize" ]
        )
      | EJsonOpAccess key ->
        block ~result:[i32] (
          args @ [ const ctx.ctx (Coq_ejstring key)
                 ; op_trivial ctx.ctx (EJsonOpAccess []) ]
        )
      | EJsonOpHasOwnProperty key ->
        block ~result:[i32] (
          args @ [ const ctx.ctx (Coq_ejstring key)
                 ; op_trivial ctx.ctx (EJsonOpHasOwnProperty []) ]
        )
      | _ -> block ~result:[i32] (args @ [op_trivial ctx.ctx op])

    (* must align with function names in the runtime module *)
    let string_of_runtime_op = function
      (* Generic *)
      | EJsonRuntimeEqual -> "runtimeEqual"
      | EJsonRuntimeCompare -> "runtimeCompare"
      | EJsonRuntimeToString -> "runtimeToString"
      | EJsonRuntimeToText -> "runtimeToText"
      (* Record *)
      | EJsonRuntimeRecConcat -> "runtimeRecConcat"
      | EJsonRuntimeRecMerge -> "runtimeRecMerge"
      | EJsonRuntimeRecRemove-> "runtimeRecRemove"
      | EJsonRuntimeRecProject-> "runtimeRecProject"
      | EJsonRuntimeRecDot -> "runtimeRecDot"
      (* Array *)
      | EJsonRuntimeArray -> "runtimeArray"
      | EJsonRuntimeArrayLength -> "runtimeArrayLength"
      | EJsonRuntimeArrayPush -> "runtimeArrayPush"
      | EJsonRuntimeArrayAccess -> "runtimeArrayAccess"
      (* Sum *)
      | EJsonRuntimeEither -> "runtimeEither"
      | EJsonRuntimeToLeft-> "runtimeToLeft"
      | EJsonRuntimeToRight-> "runtimeToRight"
      (* Brand *)
      | EJsonRuntimeUnbrand -> "runtimeUnbrand"
      | EJsonRuntimeCast -> "runtimeCast"
      (* Collection *)
      | EJsonRuntimeDistinct -> "runtimeDistinct"
      | EJsonRuntimeSingleton -> "runtimeSingleton"
      | EJsonRuntimeFlatten -> "runtimeFlatten"
      | EJsonRuntimeUnion -> "runtimeUnion"
      | EJsonRuntimeMinus -> "runtimeMinus"
      | EJsonRuntimeMin -> "runtimeMin"
      | EJsonRuntimeMax -> "runtimeMax"
      | EJsonRuntimeNth -> "runtimeNth"
      | EJsonRuntimeCount -> "runtimeCount"
      | EJsonRuntimeContains -> "runtimeContains"
      | EJsonRuntimeSort -> "runtimeSort"
      | EJsonRuntimeGroupBy -> "runtimeGroupBy"
      (* String *)
      | EJsonRuntimeLength -> "runtimeLength"
      | EJsonRuntimeSubstring -> "runtimeSubstring"
      | EJsonRuntimeSubstringEnd -> "runtimeSubstringEnd"
      | EJsonRuntimeStringJoin -> "runtimeStringJoin"
      | EJsonRuntimeLike -> "runtimeLike"
      (* Integer *)
      | EJsonRuntimeNatLt -> "runtimeNatLt"
      | EJsonRuntimeNatLe -> "runtimeNatLe"
      | EJsonRuntimeNatPlus -> "runtimeNatPlus"
      | EJsonRuntimeNatMinus -> "runtimeNatMinus"
      | EJsonRuntimeNatMult -> "runtimeNatMult"
      | EJsonRuntimeNatDiv -> "runtimeNatDiv"
      | EJsonRuntimeNatRem -> "runtimeNatRem"
      | EJsonRuntimeNatAbs -> "runtimeNatAbs"
      | EJsonRuntimeNatLog2 -> "runtimeNatLog2"
      | EJsonRuntimeNatSqrt -> "runtimeNatSqrt"
      | EJsonRuntimeNatMinPair -> "runtimeNatMinPair"
      | EJsonRuntimeNatMaxPair -> "runtimeNatMaxPair"
      | EJsonRuntimeNatMin -> "runtimeNatMin"
      | EJsonRuntimeNatMax -> "runtimeNatMax"
      | EJsonRuntimeNatSum -> "runtimeNatSum"
      | EJsonRuntimeNatArithMean -> "runtimeNatArithMean"
      | EJsonRuntimeFloatOfNat -> "runtimeFloatOfNat"
      (* Float *)
      | EJsonRuntimeFloatSum -> "runtimeFloatSum"
      | EJsonRuntimeFloatArithMean -> "runtimeFloatArithMean"
      | EJsonRuntimeFloatMin -> "runtimeFloatMin"
      | EJsonRuntimeFloatMax -> "runtimeFloatMax"
      | EJsonRuntimeNatOfFloat -> "runtimeNatOfFloat"
      (* Foreign *)
      | EJsonRuntimeForeign _fop -> "runtimeForeign"

    let rt_op_trivial ctx op : Ir.instr =
      let foreign params result =
        let fname = string_of_runtime_op op in
        let f, import = Ir.import_func ~params ~result "runtime" fname in
        ctx.imports <- ImportSet.add import ctx.imports;
        Ir.call f
      in
      let open Ir in
      match (op : 'a ejson_runtime_op) with
      | EJsonRuntimeEqual -> foreign [i32; i32] [i32]
      | EJsonRuntimeCompare -> foreign [i32; i32] [i32]
      | EJsonRuntimeToString -> foreign [i32] [i32]
      | EJsonRuntimeToText -> foreign [i32] [i32]
      | EJsonRuntimeRecConcat -> foreign [i32; i32] [i32]
      | EJsonRuntimeRecMerge -> foreign [i32; i32] [i32]
      | EJsonRuntimeRecRemove -> foreign [i32; i32] [i32]
      | EJsonRuntimeRecProject -> foreign [i32; i32] [i32]
      | EJsonRuntimeRecDot -> foreign [i32; i32] [i32]
      | EJsonRuntimeArray -> failwith "n-ary RuntimeArray is compiled below"
      | EJsonRuntimeArrayLength -> foreign [i32] [i32]
      | EJsonRuntimeArrayPush -> foreign [i32; i32] [i32]
      | EJsonRuntimeArrayAccess -> foreign [i32; i32] [i32]
      | EJsonRuntimeEither -> foreign [i32] [i32]
      | EJsonRuntimeToLeft -> foreign [i32] [i32]
      | EJsonRuntimeToRight -> foreign [i32] [i32]
      | EJsonRuntimeUnbrand -> foreign [i32] [i32]
      | EJsonRuntimeCast -> foreign [i32; i32; i32] [i32]
      | EJsonRuntimeDistinct -> foreign [i32] [i32]
      | EJsonRuntimeSingleton -> foreign [i32] [i32]
      | EJsonRuntimeFlatten -> foreign [i32] [i32]
      | EJsonRuntimeUnion -> foreign [i32; i32] [i32]
      | EJsonRuntimeMinus -> foreign [i32; i32] [i32]
      | EJsonRuntimeMin -> foreign [i32; i32] [i32]
      | EJsonRuntimeMax -> foreign [i32; i32] [i32]
      | EJsonRuntimeNth -> foreign [i32; i32] [i32]
      | EJsonRuntimeCount -> foreign [i32] [i32]
      | EJsonRuntimeContains -> foreign [i32; i32] [i32]
      | EJsonRuntimeSort -> foreign [i32; i32] [i32]
      | EJsonRuntimeGroupBy -> foreign [i32; i32; i32] [i32]
      | EJsonRuntimeLength -> foreign [i32] [i32]
      | EJsonRuntimeSubstring -> foreign [i32; i32; i32] [i32]
      | EJsonRuntimeSubstringEnd -> foreign [i32; i32] [i32]
      | EJsonRuntimeStringJoin -> foreign [i32; i32] [i32]
      | EJsonRuntimeLike -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatLt -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatLe -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatPlus -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatMinus -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatMult -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatDiv -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatRem -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatAbs -> foreign [i32] [i32]
      | EJsonRuntimeNatLog2 -> foreign [i32] [i32]
      | EJsonRuntimeNatSqrt -> foreign [i32] [i32]
      | EJsonRuntimeNatMinPair -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatMaxPair -> foreign [i32; i32] [i32]
      | EJsonRuntimeNatSum -> foreign [i32] [i32]
      | EJsonRuntimeNatMin -> foreign [i32] [i32]
      | EJsonRuntimeNatMax -> foreign [i32] [i32]
      | EJsonRuntimeNatArithMean -> foreign [i32] [i32]
      | EJsonRuntimeFloatOfNat -> foreign [i32] [i32]
      | EJsonRuntimeFloatSum -> foreign [i32] [i32]
      | EJsonRuntimeFloatArithMean -> foreign [i32] [i32]
      | EJsonRuntimeFloatMin -> foreign [i32] [i32]
      | EJsonRuntimeFloatMax -> foreign [i32] [i32]
      | EJsonRuntimeNatOfFloat -> foreign [i32] [i32]
      | EJsonRuntimeForeign _fop -> failwith "non-trivial op RuntimeForeign"

    let rt_op ctx op args: Ir.instr =
      let open Ir in
      match (op : 'a ejson_runtime_op) with
      | EJsonRuntimeArray -> op_n_ary ctx EJsonOpArray args
      | EJsonRuntimeCast ->
        (* insert brand hierachy as first argument *)
        block ~result:[i32] (ctx.ctx.brand_hierarchy :: args @ [rt_op_trivial ctx.ctx op])
      | _ ->
        block ~result:[i32] (args @ [rt_op_trivial ctx.ctx op])

    let rec expr ctx expression : Ir.instr list =
      match (expression : ('a,'b) imp_ejson_expr) with
      | ImpExprError err -> unsupported "expr: error"
      | ImpExprVar v -> [Ir.local_get (Table.insert ctx.locals v)]
      | ImpExprConst x -> [const ctx.ctx (ejson_of_cejson x)]
      | ImpExprOp (x, args) ->
        let args = List.map (fun x -> Ir.(block ~result:[i32]) (expr ctx x)) args in
        [ op_n_ary ctx x args ]
      | ImpExprRuntimeCall (x, args) ->
        let args = List.map (fun x -> Ir.(block ~result:[i32]) (expr ctx x)) args in
        [ rt_op ctx x args ]

    let rec statement ctx stmt : Ir.instr list =
      let foreign fname params result =
        let f, import = Ir.import_func ~params ~result "runtime" fname in
        ctx.ctx.imports <- ImportSet.add import ctx.ctx.imports;
        Ir.call f
      in
      match (stmt : ('a,'b) imp_ejson_stmt) with
      | ImpStmtBlock (vars, stmts) ->
        (* TODO: This assumes that variable names are unique which is not true in general. *)
        let defs =
          List.map (fun (var, value) ->
              let id = Table.insert ctx.locals var in
              match value with
              | Some x ->  expr ctx x @ [ Ir.local_set id ]
              | None -> []
            ) vars
        in
        let body = List.map (statement ctx) stmts in
        List.concat (defs @ body)
      | ImpStmtAssign (var, x) ->
        expr ctx x @ [ Ir.local_set (Table.insert ctx.locals var) ]
      | ImpStmtFor (e', arr, body) ->
        let i'   = '$' :: '%' :: 'i' :: '%' :: e' in
        let n' = '$' :: '%' :: 'n' :: '%' :: e' in
        let a' = '$' :: '%' :: 'a' :: '%' :: e' in
        let i = Table.insert ctx.locals i' in
        let e = Table.insert ctx.locals e' in
        let n = Table.insert ctx.locals n' in
        let a = Table.insert ctx.locals a' in
        let low = ImpExprConst (Coq_cejbigint 0)
        and high = ImpExprOp (EJsonOpArrayLength, [ImpExprVar a'])
        in
        let open Ir in
        let get_el =
          [ local_get a
          ; local_get i
          ; op_trivial ctx.ctx EJsonOpArrayAccess
          ; local_set e
          ]
        in
        ( statement ctx (ImpStmtAssign (i', low )) ) @
        ( statement ctx (ImpStmtAssign (a', arr )) ) @
        ( statement ctx (ImpStmtAssign (n', high)) ) @
        [ loop
            [ local_get i
            ; local_get n
            ; rt_op_trivial ctx.ctx EJsonRuntimeNatLt
            ; foreign "EjBool#get:value" [i32] [i32]
            ; if_
                [ block get_el
                ; block (statement ctx body) (* TODO: what if body modifies i? *)
                ; local_get i
                ; const ctx.ctx (Coq_ejbigint 1)
                ; rt_op_trivial ctx.ctx EJsonRuntimeNatPlus
                ; local_set i
                ; br 1
                ] []
            ]
        ]
      | ImpStmtForRange (var, low, high, body) ->
        let i = Table.insert ctx.locals var in
        let max' = '$' :: '%' :: var in
        let max = Table.insert ctx.locals max' in
        let open Ir in
        ( statement ctx (ImpStmtAssign (var, low)) ) @
        ( statement ctx (ImpStmtAssign (max', high)) ) @
        [ loop
            [ local_get i
            ; local_get max
            ; rt_op_trivial ctx.ctx EJsonRuntimeNatLe
            ; foreign "EjBool#get:value" [i32] [i32]
            ; if_
                [ block (statement ctx body) (* TODO: what if body modifies i? *)
                ; local_get i
                ; const ctx.ctx (Coq_ejbigint 1)
                ; rt_op_trivial ctx.ctx EJsonRuntimeNatPlus
                ; local_set i
                ; br 1
                ] []
            ]
        ]
      | ImpStmtIf (condition, then_, else_) ->
        let open Ir in
        (expr ctx condition) @
        [ foreign "EjBool#get:value" [i32] [i32]
        ; if_ (statement ctx then_) (statement ctx else_)
        ]

    let function_  ctx fn : Ir.func =
      let ImpFun (arg, stmt, ret) = fn in
      let locals = Table.create ~element_size:(fun _ -> 1) ~initial_offset:0 in
      let ctx = {locals; ctx } in
      let () = assert (Table.insert locals arg = 0) in
      let raw_body =
        (* the compiled function with argument and result being
         * runtime ejson values *)
        statement ctx stmt @
        Ir.[ local_get (Table.insert locals ret) ]
      in
      let body =
        (* wrap function such that argument and result are binary ejson values *)
        let foreign fname params result =
          let f, import = Ir.import_func ~params ~result "runtime" fname in
          ctx.ctx.imports <- ImportSet.add import ctx.ctx.imports;
          Ir.call f
        in
        let open Ir in
        [ local_get 0 (* arg to __release *)
        ; local_get 0
        ; foreign "ejson_of_bytes" [i32] [i32]
        ; local_set 0
        ; foreign "__release" [i32] [] (* release binary value *)
        ] @ raw_body @
        [ foreign "ejson_to_bytes" [i32] [i32] ]
      in
      let locals =
        (* First local is the function argument. All locals are pointers. *)
        List.init (Table.size ctx.locals - 1) (fun _ -> Ir.i32)
      in
      Ir.(func ~params:[i32] ~result:[i32] ~locals body)

    let imp hierarchy lib : Wasm.Ast.module_ =
      let ctx =
        { imports = ImportSet.empty
        ; memory = Ir.memory 1
        ; constants =
            Table.create ~initial_offset:0 ~element_size:(fun x ->
              Constants.encode x |> Bytes.length)
        ; brand_hierarchy =
            Ir.unreachable (* this will be overwritten on the next lines *)
        }
      in
      let ctx =
        (* compile brand hierarchy as first constant in module *)
        let relations = ejson_of_brand_relations hierarchy in
        { ctx with brand_hierarchy = const ctx relations }
      in
      let funcs = List.map (fun (name, fn) ->
          Util.string_of_char_list name, function_ ctx fn
        ) lib
      in
      let data =
        Table.elements ctx.constants
        |> List.map (fun (i, c) ->
            let s = Constants.encode c
            in ctx.memory, i, Bytes.to_string s)
      in
      Ir.module_to_spec
        { Ir.start = None
        ; globals = []
        ; memories = []
        ; tables = []
        ; funcs
        ; data
        ; elems = []
        ; imports = ImportSet.elements ctx.imports
        }
  end

  (* Satisfy public interface *)

  let eval module_ fn_name arg =
    try Eval.eval module_ fn_name arg
    with _ -> None

  module Imp_scoping = Wasm_imp_scoping.Make(ImpEJson)

  let imp_ejson_to_wasm_ast h foreigndatamap imp = Translate.imp h (Imp_scoping.apply imp)

  let to_string q =
    let sexpr = Arrange.module_ q in
    Sexpr.to_string 72 sexpr

  let string_of_operator = Translate.string_of_op
  let string_of_runtime_operator = Translate.string_of_runtime_op
end
