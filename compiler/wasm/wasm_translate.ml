open Wasm_util
module Ir = Wasm_ir
open ImpEJson

module ImportSet = Set.Make( struct
    type t = Ir.import
    let compare = Stdlib.compare
  end)

type module_context =
  { mutable imports : ImportSet.t
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

let op ctx op : Ir.instr list =
  let foreign params result =
    let fname = op_foreign_fn_name op in
    let f, import = Ir.import_func ~params ~result "runtime" fname in
    ctx.imports <- ImportSet.add import ctx.imports;
    [ Ir.call f ]
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

let rt_op ctx op : Ir.instr list =
  let foreign params result =
    let fname = string_of_runtime_op op in
    let f, import = Ir.import_func ~params ~result "runtime" fname in
    ctx.imports <- ImportSet.add import ctx.imports;
    [ Ir.call f ]
  in
  let open Ir in
  match (op : EJsonRuntimeOperators.ejson_runtime_op) with
  | EJsonRuntimeRecDot -> foreign [i32; i32] [i32]
  | _ -> unsupported ("runtime op: " ^ (string_of_runtime_op op))

let const ctx c : Ir.instr list =
  (* This generates new AssemblyScript objects for each use of the constant.
   * TODO: Come up with a mechanism for reusing constants. *)
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
  match (c : EJson.cejson) with
  | Coq_cejnull  ->
    [ i32_const' 0
    ; new_ [] "EjNull"
    ]
  | Coq_cejbool x ->
    [ i32_const' 0
    ; i32_const' (if x then 1 else 0)
    ; new_ [i32] "EjBool"
    ]
  | Coq_cejnumber x ->
    [ i32_const' 0
    ; f64_const x
    ; new_ [f64] "EjNumber"
    ]
  | Coq_cejbigint x ->
    [ i32_const' 0
    ; i64_const (Int64.of_int x)
    ; new_ [i64] "EjBigInt"
    ]
  | Coq_cejstring x ->
      [ i32_const' 0
      ; new_ [] "EjStringBuilder"
      ]
      @ List.concat (List.map (fun c ->
        [ i32_const' (int_of_char c)
        ; call (foreign ~params:[i32; i32] ~result:[i32] "EjStringBuilder#append")
        ]
        ) x
      )
      @ [ call (foreign ~params:[i32] ~result:[i32] "EjStringBuilder#finalize") ]
      (* TODO: I think we have to release the EjStringBuilder here? *)
  | Coq_cejforeign _ -> unsupported "const: foreign"

let rec expr ctx expression : Ir.instr list =
  match (expression : imp_ejson_expr) with
  | ImpExprError err -> unsupported "expr: error"
  | ImpExprVar v -> [Ir.local_get (Table.insert ctx.locals v)]
  | ImpExprConst x -> const ctx x
  | ImpExprOp (x, args) ->
    (* Put arguments on the stack, append operator *)
    (List.map (expr ctx) args |> List.concat) @ (op ctx.ctx x)
  | ImpExprRuntimeCall (x, args) ->
    (List.map (expr ctx) args |> List.concat) @ (rt_op ctx.ctx x)

let rec statement ctx stmt : Ir.instr list =
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
  | ImpStmtFor _ -> unsupported "statement: for"
  | ImpStmtForRange _ -> unsupported "statement: for range"
  | ImpStmtIf _ -> unsupported "statement: if"

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
  let locals = List.init (Table.size locals - 1) (fun _ -> Ir.i32) in
  Ir.(func ~params:[i32] ~result:[i32] ~locals body)

let f_start =
  let open Ir in
  func []

let imp functions : Wasm.Ast.module_ =
  let ctx = { imports = ImportSet.empty } in
  let funcs =
    match functions with
    | [ _name, fn ] -> ["main", function_ ctx fn]
    | _ -> failwith "Wasm_translate.imp: single function expected"
  in
  Ir.module_to_spec
    { Ir.start = Some (f_start)
    ; globals = []
    ; memories = []
    ; tables = []
    ; funcs
    ; data = []
    ; elems = []
    ; imports = ImportSet.elements ctx.imports
    }