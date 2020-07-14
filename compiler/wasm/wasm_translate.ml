open Wasm_util
module Ir = Wasm_ir
open ImpEJson

module ImportSet = Set.Make( struct
    type t = Ir.import
    let compare = Stdlib.compare
  end)

type module_context =
  { mutable imports : ImportSet.t
  ; memory: Ir.memory
  ; constants: EJson.cejson Table.t
  }

type function_context =
  { locals : char list Table.t
  ; ctx: module_context
  }

let op_foreign_fn_name : imp_ejson_op -> string = function
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

let op ctx op : Ir.instr =
  let foreign params result =
    let fname = op_foreign_fn_name op in
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
  | EJsonOpArray -> foreign [i32] [i32]
  | EJsonOpArrayLength -> foreign [i32] [i32]
  | EJsonOpArrayPush -> foreign [i32; i32] [i32]
  | EJsonOpArrayAccess -> foreign [i32; i32] [i32]
  (* TODO: (WASM IR in coq) get rid of the following three constructor arguments *)
  | EJsonOpObject _ -> foreign [i32] [i32]
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

let string_of_runtime_op =
  let open EJsonRuntimeOperators in
  function
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
  | EJsonRuntimeBrand -> "runtimeBrand"
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
  | EJsonRuntimeForeign _fop -> "FOREIGN"

let rt_op ctx op : Ir.instr =
  let foreign params result =
    let fname = string_of_runtime_op op in
    let f, import = Ir.import_func ~params ~result "runtime" fname in
    ctx.imports <- ImportSet.add import ctx.imports;
    Ir.call f
  in
  let open Ir in
  match (op : EJsonRuntimeOperators.ejson_runtime_op) with
  | EJsonRuntimeEqual -> foreign [i32; i32] [i32]
  | EJsonRuntimeCompare -> foreign [i32; i32] [i32]
  | EJsonRuntimeRecConcat -> foreign [i32; i32] [i32]
  | EJsonRuntimeRecDot -> foreign [i32; i32] [i32]
  | EJsonRuntimeEither -> foreign [i32] [i32]
  | EJsonRuntimeToLeft -> foreign [i32] [i32]
  | EJsonRuntimeToRight -> foreign [i32] [i32]
  | EJsonRuntimeNatLe -> foreign [i32; i32] [i32]
  | EJsonRuntimeNatLt -> foreign [i32; i32] [i32]
  | EJsonRuntimeNatPlus -> foreign [i32; i32] [i32]
  | _ -> unsupported ("runtime op: " ^ (string_of_runtime_op op))

module Constants = struct
  let encode_const : EJson.cejson -> bytes = function
    | Coq_cejnull ->
      let b = Bytes.create 8 in
      Bytes.set_int32_le b 0 (Int32.of_int 0); (* ptr after allocation *)
      Bytes.set_int32_le b 4 (Int32.of_int 0); (* type: null *)
      b
    | Coq_cejbool false ->
      let b = Bytes.create 8 in
      Bytes.set_int32_le b 0 (Int32.of_int 0); (* ptr after allocation *)
      Bytes.set_int32_le b 4 (Int32.of_int 1); (* type: false *)
      b
    | Coq_cejbool true ->
      let b = Bytes.create 8 in
      Bytes.set_int32_le b 0 (Int32.of_int 0); (* ptr after allocation *)
      Bytes.set_int32_le b 4 (Int32.of_int 2); (* type: true *)
      b
    | Coq_cejnumber x ->
      let b = Bytes.create 16 in
      Bytes.set_int32_le b 0 (Int32.of_int 0); (* ptr after allocation *)
      Bytes.set_int32_le b 4 (Int32.of_int 3); (* type: number *)
      Bytes.set_int64_le b 8 (Int64.bits_of_float x); (* value *)
      b
    | Coq_cejbigint x ->
      let b = Bytes.create 16 in
      Bytes.set_int32_le b 0 (Int32.of_int 0); (* ptr after allocation *)
      Bytes.set_int32_le b 4 (Int32.of_int 4); (* type: bigint *)
      Bytes.set_int64_le b 8 (Int64.bits_of_float (float_of_int x)); (* value *)
      (* TODO: encode BigInt as integer type *)
      b
    | Coq_cejstring s ->
      let s = Util.string_of_char_list s in
      let n = String.length s in
      let b = Bytes.create (12 + n) in
      Bytes.set_int32_le b 0 (Int32.of_int 0); (* ptr after allocation *)
      Bytes.set_int32_le b 4 (Int32.of_int 5); (* type: string *)
      Bytes.set_int32_le b 8 (Int32.of_int n); (* length *)
      Bytes.blit_string s 0 b 12 n; (* value *)
      b
    | Coq_cejforeign _ -> unsupported "ejson encode: foreign"

  let alloc_const ctx : Ir.func =
    let open Ir in
    let foreign ~params ~result name =
      let f, import = Ir.import_func ~params ~result "runtime" name in
      ctx.ctx.imports <- ImportSet.add import ctx.ctx.imports;
      f
    in
    let new_ params class_ =
      let item = class_ ^ "#constructor" in
      call (foreign ~params:(i32 :: params) ~result:[i32] item)
    in
    let local_ptr, tag, n, foreign_ptr = 0, 1, 2, 3 in
    func ~params:[i32] ~result:[i32] ~locals:[i32; i32; i32]
      [ local_get local_ptr
      ; load ctx.ctx.memory ~offset:4 i32
      ; local_tee tag
      ; i32_eqz (* null *)
      ; if_
          [ i32_const' 0
          ; new_ [] "EjNull"
          ; return
          ] []
      ; local_get tag
      ; i32_const' 1 (* false *)
      ; eq i32
      ; if_
          [ i32_const' 0
          ; i32_const' 0
          ; new_ [i32] "EjBool"
          ; return
          ] []
      ; local_get tag
      ; i32_const' 2 (* true *)
      ; eq i32
      ; if_
          [ i32_const' 0
          ; i32_const' 1
          ; new_ [i32] "EjBool"
          ; return
          ] []
      ; local_get tag
      ; i32_const' 3 (* number *)
      ; eq i32
      ; if_
          [ i32_const' 0
          ; local_get local_ptr
          ; load ctx.ctx.memory ~offset:8 f64
          ; new_ [f64] "EjNumber"
          ; return
          ] []
      ; local_get tag
      ; i32_const' 4 (* bigint *)
      ; eq i32
      ; if_
          [ i32_const' 0
          ; local_get local_ptr
          ; load ctx.ctx.memory ~offset:8 f64
          ; new_ [f64] "EjBigInt"
          ; return
          ] []
      ; local_get tag
      ; i32_const' 5 (* string *)
      ; eq i32
      ; if_
          [ (* load length / characters to be processed *)
            local_get local_ptr
          ; load ctx.ctx.memory ~offset:8 i32
          ; local_set n
          (* initialize buffer in runtime *)
          ; i32_const' 0
          ; local_get n
          ; new_ [i32] "EjStringBuilderUTF8"
          ; local_set foreign_ptr
          (* initialize moving pointer *)
          ; local_get local_ptr
          ; i32_const' 12
          ; add i32
          ; local_set local_ptr
          ; loop (* over characters and append *)
            [ local_get n
            ; i32_eqz
            ; if_
              [ local_get foreign_ptr (* for release *)
              ; local_get foreign_ptr (* for finalize *)
              ; call (foreign ~params:[i32] ~result:[i32] "EjStringBuilderUTF8#finalize")
              ; local_set foreign_ptr (* for return *)
              ; call (foreign ~params:[i32] ~result:[] "__release")
              ; local_get foreign_ptr
              ; return
              ] []
            ; local_get n
            ; i32_const' 1
            ; sub i32
            ; local_set n
            ; local_get foreign_ptr
            ; local_get local_ptr
            (* TODO: speed up string constant allocation by copying words. *)
            ; load ctx.ctx.memory ~pack:U8 i32
            ; call (foreign ~params:[i32; i32] ~result:[] "EjStringBuilderUTF8#putByte")
            ; local_get local_ptr
            ; i32_const' 1
            ; add i32
            ; local_set local_ptr
            ; br 0 (* repeat *)
            ]
          ] []
      ; unreachable
      ]

  let get_const ctx : Ir.func =
    let open Ir in
    let local_ptr, foreign_ptr = 0, 1 in
    func ~params:[i32] ~result:[i32] ~locals:[i32]
      [ local_get local_ptr
      ; load ctx.ctx.memory i32
      ; local_tee foreign_ptr
      ; i32_eqz
      ; if_
          [ local_get local_ptr
          ; local_get local_ptr
          ; call (alloc_const ctx)
          ; local_tee foreign_ptr
          ; store ctx.ctx.memory i32
          ] []
      ; local_get foreign_ptr
      ]
end

let const ctx c : Ir.instr =
  let offset = Table.insert ctx.ctx.constants c in
  let open Ir in
  block ~result:[i32]
    [ i32_const' offset ; call (Constants.get_const ctx) ]

let rec expr ctx expression : Ir.instr list =
  match (expression : imp_ejson_expr) with
  | ImpExprError err -> unsupported "expr: error"
  | ImpExprVar v -> [Ir.local_get (Table.insert ctx.locals v)]
  | ImpExprConst x -> [const ctx x]
  | ImpExprOp (x, args) ->
    (* Put arguments on the stack, append operator *)
    (List.map (expr ctx) args |> List.concat) @ [ op ctx.ctx x ]
  | ImpExprRuntimeCall (x, args) ->
    (List.map (expr ctx) args |> List.concat) @ [rt_op ctx.ctx x]

let rec statement ctx stmt : Ir.instr list =
  let foreign fname params result =
    let f, import = Ir.import_func ~params ~result "runtime" fname in
    ctx.ctx.imports <- ImportSet.add import ctx.ctx.imports;
    Ir.call f
  in
  match (stmt : imp_ejson_stmt) with
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
    let low = Imp.ImpExprConst (EJson.Coq_cejbigint 0)
    and high = Imp.ImpExprOp (EJsonOperators.EJsonOpArrayLength, [Imp.ImpExprVar a'])
    in
    let open Ir in
    let get_el =
      [ local_get a
      ; local_get i
      ; op ctx.ctx EJsonOpArrayAccess
      ; local_set e
      ]
    in
    ( statement ctx (ImpStmtAssign (i', low )) ) @
    ( statement ctx (ImpStmtAssign (a', arr )) ) @
    ( statement ctx (ImpStmtAssign (n', high)) ) @
    [ loop
        [ local_get i
        ; local_get n
        ; rt_op ctx.ctx EJsonRuntimeNatLt
        ; foreign "EjBool#get:value" [i32] [i32]
        ; if_
            [ block get_el
            ; block (statement ctx body) (* TODO: what if body modifies i? *)
            ; local_get i
            ; const ctx (Coq_cejbigint 1)
            ; rt_op ctx.ctx EJsonRuntimeNatPlus
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
        ; rt_op ctx.ctx EJsonRuntimeNatLe
        ; foreign "EjBool#get:value" [i32] [i32]
        ; if_
            [ block (statement ctx body) (* TODO: what if body modifies i? *)
            ; local_get i
            ; const ctx (Coq_cejbigint 1)
            ; rt_op ctx.ctx EJsonRuntimeNatPlus
            ; local_set i
            ; br 1
            ] []
        ]
    ]
  | ImpStmtIf (condition, then_, else_) ->
    let open Ir in
    (expr ctx condition) @
    (* TODO: check that expr is a EjBool? *)
    [ foreign "EjBool#get:value" [i32] [i32]
    ; if_ (statement ctx then_) (statement ctx then_)
    ]

let function_  ctx fn : Ir.func =
  let Imp.ImpFun (arg, stmt, ret) = fn in
  let locals = Table.create ~element_size:(fun _ -> 1) ~initial_offset:0 in
  let ctx = {locals; ctx } in
  let l_arg = Table.insert locals arg in
  let () = assert (l_arg = 0) in
  let body =
    statement ctx stmt @
    Ir.[ local_get (Table.insert locals ret) ]
  in
  let locals =
    (* First local is function arguments. All locals are pointers. *)
    List.init (Table.size ctx.locals - 1) (fun _ -> Ir.i32)
  in
  Ir.(func ~params:[i32] ~result:[i32] ~locals body)

let f_start =
  let open Ir in
  func []

let imp functions : Wasm.Ast.module_ =
  let ctx =
    { imports = ImportSet.empty
    ; memory = Ir.memory 1
    ; constants = Table.create ~initial_offset:0 ~element_size:(fun x ->
          Constants.encode_const x |> Bytes.length)
    }
  in
  let funcs =
    match functions with
    | [ _name, fn ] -> ["main", function_ ctx fn]
    | _ -> failwith "Wasm_translate.imp: single function expected"
  in
  let data =
    Table.elements ctx.constants
    |> List.map (fun (i, c) ->
        let s = Constants.encode_const c
        in ctx.memory, i, Bytes.to_string s)
  in
  Ir.module_to_spec
    { Ir.start = Some (f_start)
    ; globals = []
    ; memories = []
    ; tables = []
    ; funcs
    ; data
    ; elems = []
    ; imports = ImportSet.elements ctx.imports
    }
