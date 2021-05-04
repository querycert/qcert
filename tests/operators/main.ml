open Qcert_lib

module ImpEJson = struct
  include Imp
  include EJson
  include EJsonOperators
  include EJsonRuntimeOperators
  include ImpEJson
end
open ImpEJson

let imp_eval (imp_ejson : _ imp_ejson) ?(brands=[]) env : _ ejson option =
  let open ImpEJsonEval in
  let open EnhancedEJson in
  imp_ejson_eval_top_on_ejson
    enhanced_foreign_ejson
    enhanced_foreign_ejson_runtime
    brands env imp_ejson

module Wasm_backend = Wasm_backend.Make(ImpEJson)

let wasm_eval (imp_ejson : _ imp_ejson) ?(brands=[]) env : _ ejson option =
  let wasm_ast =
    Wasm_backend.imp_ejson_to_wasm_ast brands imp_ejson
  in
  Wasm_backend.eval wasm_ast ['f'] env

open ImpEJson

let ejson_to_string ejson =
  let open EnhancedEJson in
  let open EnhancedEJsonToJSON in
  let json =
    EJsonToJSON.ejson_to_json
      enhanced_foreign_ejson
      enhanced_foreign_to_json
      ejson
  in
  JSON.jsonStringify [] json
  |> Util.string

let test_fn fn =
  let env = [['x'], Coq_ejnumber 42. ]
  and imp_ejson : _ imp_ejson = [['f'], fn]
  in
  let imp = match imp_eval imp_ejson env with
    | Some x -> x
    | None -> failwith "imp eval failed"
  in
  let wasm = match wasm_eval imp_ejson env with
    | Some x -> x
    | None -> failwith "wasm eval failed"
  in
  if (wasm <> imp) then (
    print_string ("imp:  ");
    print_endline (ejson_to_string imp);
    print_string ("wasm: ");
    print_endline (ejson_to_string wasm);
    failwith "wasm and imp differ"
  )

let test_op_1 op args =
  let x = ['x'] and y = ['y'] in
  let stmt =
    ImpStmtAssign(y, ImpExprOp (op, args))
  in
  test_fn (ImpFun (x, stmt, y))

let test_op op args =
  List.iter (fun args -> test_op_1 op args) args

let test_rtop_1 op args =
  let x = ['x'] and y = ['y'] in
  let stmt =
    ImpStmtAssign(y, ImpExprRuntimeCall (op, args))
  in
  test_fn (ImpFun (x, stmt, y))

let test_rtop op args =
  List.iter (fun args -> test_rtop_1 op args) args

module Const = struct
  let number x = ImpExprConst (Coq_cejnumber x)
  let bigint x = ImpExprConst (Coq_cejbigint x)
end

let _ =
  let open Const in
  test_op
    EJsonOpAddNumber
    [ [number 41.; number 1.]
    ; [number (-1.); number 1e32]
    ; [number (-1.); number Float.infinity]
    ];
  test_rtop
    EJsonRuntimeNatPlus
    [ [bigint 41; bigint 1]
    ; [bigint 43; bigint (-1)]
    ]
