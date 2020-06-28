open Wasm_util
module Ir = Wasm_ir
open ImpEJson

type function_context =
  { locals : char list Table.t
  ; runtime : Wasm_imp_runtime.t
  }

let op (module R : Wasm_imp_runtime.RUNTIME) op : Ir.instr list =
  match (op : imp_ejson_op) with
  | EJsonOpNot -> [Ir.call R.not]
  | EJsonOpNeg -> unsupported "op: neg"
  | EJsonOpAnd -> [Ir.call R.and_]
  | EJsonOpOr -> [Ir.call R.or_]
  | EJsonOpLt -> Ir.[call (R.compare Lt)]
  | EJsonOpLe -> Ir.[call (R.compare Le)]
  | EJsonOpGt -> Ir.[call (R.compare Gt)]
  | EJsonOpGe -> Ir.[call (R.compare Ge)]
  | EJsonOpAddString
  | EJsonOpAddNumber
  | EJsonOpSub
  | EJsonOpMult
  | EJsonOpDiv
  | EJsonOpStrictEqual
  | EJsonOpStrictDisequal
  | EJsonOpArray
  | EJsonOpArrayLength
  | EJsonOpArrayPush
  | EJsonOpArrayAccess
  | EJsonOpObject _
  | EJsonOpAccess _
  | EJsonOpHasOwnProperty _
  | EJsonOpMathMin
  | EJsonOpMathMax
  | EJsonOpMathPow
  | EJsonOpMathExp
  | EJsonOpMathAbs
  | EJsonOpMathLog
  | EJsonOpMathLog10
  | EJsonOpMathSqrt
  | EJsonOpMathCeil
  | EJsonOpMathFloor
  | EJsonOpMathTrunc -> unsupported "op"

let rec expr ctx expression : Ir.instr list =
  let module R = (val ctx.runtime) in
  match (expression : imp_ejson_expr) with
  | ImpExprError err -> unsupported "expr: error"
  | ImpExprVar v -> [Ir.local_get (Table.offset ctx.locals v)]
  | ImpExprConst x -> [R.const x]
  | ImpExprOp (x, args) ->
    (* Put arguments on the stack, append operator *)
    (List.map (expr ctx) args |> List.concat) @ (op ctx.runtime x)
  | ImpExprRuntimeCall (op, args) -> unsupported "expr: runtime call"

let rec statement ctx stmt : Ir.instr list =
  match (stmt : imp_ejson_stmt) with
  | ImpStmtBlock (vars, stmts) ->
    (* TODO: This assumes that variable names are unique which is not true in general. *)
    let defs =
      List.map (fun (var, value) ->
          let id = Table.offset ctx.locals var in
          match value with
          | Some x ->  expr ctx x @ [ Ir.local_set id ]
          | None -> []
        ) vars
    in
    let body = List.map (statement ctx) stmts in
    List.concat (defs @ body)
  | ImpStmtAssign (var, x) ->
    expr ctx x @ [ Ir.local_set (Table.offset ctx.locals var) ]
  | ImpStmtFor _ -> unsupported "statement: for"
  | ImpStmtForRange _ -> unsupported "statement: for range"
  | ImpStmtIf _ -> unsupported "statement: if"

let function_  runtime fn : Ir.func =
  let Imp.ImpFun (arg, stmt, ret) = fn in
  let locals = Table.create ~element_size:(fun _ -> 1) in
  let ctx = {locals; runtime } in
  let l_arg = Table.offset locals arg in
  let () = assert (l_arg = 0) in
  let body =
    statement ctx stmt @
    Ir.[ local_get (Table.offset locals ret) ]
  in
  let locals = List.init (Table.size locals - 1) (fun _ -> Ir.i32) in
  Ir.(func ~params:[i32] ~result:[i32] ~locals body)

let f_start (module R : Wasm_imp_runtime.RUNTIME) =
  let size = Table.size R.Ctx.constants in
  let open Ir in
  func [ i32_const' size; global_set R.Ctx.alloc_p ]

let imp functions : Wasm.Ast.module_ =
  let runtime = Wasm_imp_runtime.create () in
  let funcs =
    match functions with
    | [ _name, fn ] -> ["main", function_ runtime fn]
    | _ -> failwith "Wasm_translate.imp: single function expected"
  and f_start = f_start runtime
  in
  let module R = (val runtime) in
  let data =
    List.fold_left (fun acc (_, el) -> acc ^ el) "" (Table.elements R.Ctx.constants)
  in
  Ir.module_to_spec
    { Ir.start = Some (f_start)
    ; globals = ["alloc_p", R.Ctx.alloc_p]
    ; memories = ["memory", R.Ctx.memory]
    ; tables = []
    ; funcs
    ; data = [ R.Ctx.memory, 0, data ]
    ; elems = List.map (fun (a,b) -> R.Ctx.table, a, b) R.Ctx.elems
    }
