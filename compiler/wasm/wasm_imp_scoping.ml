module Make (ImpEJson: Wasm_intf.IMP_EJSON) : sig
  open ImpEJson
  val apply: ('a, 'b) imp_ejson -> ('a, 'b) imp_ejson
end = struct
  open ImpEJson
  type var_name = string

  type scope =
    { map: (var_name * var_name) list
    ; size: int
    }

  let empty_scope = { map = []; size = 0 }

  let fresh_var scope name =
    let name' = "var" ^ Int.to_string scope.size in
    { map = (name, name') :: scope.map
    ; size = scope.size + 1
    }, name'

  let var scope name =
    match List.assoc_opt name scope.map with
    | Some name' -> name'
    | None -> failwith "wasm_imp_scoping: undeclared variable"

  let rec expression scope = function
    | ImpExprVar name -> ImpExprVar (var scope name)
    | ImpExprOp (op, exprs) ->
      let exprs = List.map (expression scope) exprs in
      ImpExprOp (op, exprs)
    | ImpExprRuntimeCall (op, exprs) ->
      let exprs = List.map (expression scope) exprs in
      ImpExprRuntimeCall (op, exprs)
    | ImpExprError _ as x -> x
    | ImpExprConst _ as x -> x

  let declaration scope (name, init) =
    let scope, name = fresh_var scope name in
    match init with
    | None -> scope, (name, None)
    | Some expr ->
      let expr = expression scope expr in
      scope, (name, Some expr)

  let map_update_scope f scope l =
    let scope, l_rev = List.fold_left (fun (scope, acc) x ->
          let scope, x = f scope x in
          scope, x :: acc
      ) (scope, []) l
    in scope, List.rev l_rev

  let rec statement scope = function
    | ImpStmtBlock (decls, stmts) ->
      let scope, decls = map_update_scope declaration scope decls in
      let stmts = List.map (statement scope) stmts in
      ImpStmtBlock (decls, stmts)
    | ImpStmtAssign (name, expr) ->
      let name = var scope name in
      let expr = expression scope expr in
      ImpStmtAssign (name, expr)
    | ImpStmtFor (name, expr, stmt) ->
      let scope, name = fresh_var scope name in
      let expr = expression scope expr in
      let stmt = statement scope stmt in
      ImpStmtFor (name, expr, stmt)
    | ImpStmtForRange (name, expr0, expr1, stmt) ->
      let scope, name = fresh_var scope name in
      let expr0 = expression scope expr0 in
      let expr1 = expression scope expr1 in
      let stmt = statement scope stmt in
      ImpStmtForRange (name, expr0, expr1, stmt)
    | ImpStmtIf (expr, stmt0, stmt1) ->
      let expr = expression scope expr in
      let stmt0 = statement scope stmt0 in
      let stmt1 = statement scope stmt1 in
      ImpStmtIf (expr, stmt0, stmt1)

  let function_ = function
    | ImpFun (arg, stmt, res) ->
      let scope = empty_scope in
      let scope, arg, res =
        if arg = res then (
          let scope, arg = fresh_var scope arg in
          scope, arg, res
        ) else (
          let scope, arg = fresh_var scope arg in
          let scope, res = fresh_var scope res in
          scope, arg, res
        )
      in
      let stmt = statement scope stmt in
      ImpFun (arg, stmt, res)

  let lib l = List.map (fun (name, func) -> name, function_ func) l

  let apply = lib
end
