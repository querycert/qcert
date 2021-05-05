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

let ejson_eq =
  ejson_eq_dec EnhancedEJson.enhanced_foreign_ejson

let failed = ref false

let test_fn fail env fn =
  let imp_ejson : _ imp_ejson = [['f'], fn] in
  let fail message =
    print_endline "";
    fail ();
    print_string ("FAILED: ");
    print_endline message;
    failed := true
  in
  match imp_eval imp_ejson env, wasm_eval imp_ejson env with
  | None, _ -> fail "imp eval failed"
  | Some _, None -> fail "wasm eval failed"
  | Some imp, Some wasm ->
    if (not (ejson_eq wasm imp)) then (
      fail "wasm and imp differ";
      print_string ("imp:  ");
      print_endline (ejson_to_string imp);
      print_string ("wasm: ");
      print_endline (ejson_to_string wasm);
    )

let test_expr_1 fail expr op args =
  let varname i =  Util.char_list_of_string ("arg" ^ (string_of_int i))
  and fail () =
    fail ();
    print_endline "arguments: ";
    List.iter (fun arg ->
        print_string "  ";
        print_endline (ejson_to_string arg)) args
  in
  let return = Util.char_list_of_string "return"
  and env = List.mapi (fun i ejson -> varname i, ejson) args
  and args = List.mapi (fun i _ ->
      ImpExprRuntimeCall (
        EJsonRuntimeRecDot,
        [ ImpExprVar ['x']
        ; ImpExprConst (Coq_cejstring (varname i))
        ])) args
  in
  let stmt =
    ImpStmtAssign(return, expr op args)
  in
  test_fn fail env (ImpFun (['x'], stmt, return))

let test_expr fail expr op args =
  List.iter (fun args -> test_expr_1 fail expr op args) args

let test_op op =
  test_expr
    (fun () ->
       print_string "operator: ";
       print_endline (Wasm_backend.string_of_operator op)
    )
    (fun op args -> ImpExprOp (op, args))
    op

let test_rtop op =
  test_expr
    (fun () ->
       print_string "operator: ";
       print_endline (Wasm_backend.string_of_runtime_operator op);
    )
    (fun op args -> ImpExprRuntimeCall (op, args))
    op

module Arg = struct
  let null = Coq_ejnull
  let bool x = Coq_ejbool x
  let num x = Coq_ejnumber x
  let int x = Coq_ejbigint x
  let str x = Coq_ejstring (Util.char_list_of_string x)
  let arr x = Coq_ejarray x
  let obj x =
    Coq_ejobject (List.map (fun (k, v) -> Util.char_list_of_string k, v) x)
end

let _ =
  let open Arg in
  test_op
    EJsonOpAddNumber
    [ [num 41.; num 1.]
    ; [num (-1.); num 1e32]
    ; [num (-1.); num Float.infinity]
    ];
  test_rtop
    EJsonRuntimeEqual
    [ [ bool false; bool true ]
    ; [ bool true; bool true]
    ];
  test_rtop
    EJsonRuntimeRecConcat
    [ [ obj [ "a", null ] ; obj [ "b", null ] ]
    ; [ obj [ "b", null ; "a", null ] ; obj [] ]
    ; [ obj [ "b", null ] ; obj [ "a", null ] ]
    ; [ obj [ "a", null; "c", null ] ; obj [ "b", null; "d", null ] ]
    ; [ obj [ "a", bool false ] ; obj [ "a", bool true ] ]
    ; [ obj [] ; obj [ "a", null ] ]
    ; [ obj [ "a", null ] ; obj [] ]
    ; [ obj [] ; obj [] ]
    ];
  test_rtop
    EJsonRuntimeRecMerge
    [ [ obj [ "a", null ] ; obj [ "b", null ] ]
    ; [ obj [ "b", null ; "a", null ] ; obj [] ]
    ; [ obj [ "b", null ] ; obj [ "a", null ] ]
    ; [ obj [ "a", null; "c", null ] ; obj [ "b", null; "d", null ] ]
    ; [ obj [ "a", bool false; "c", null ] ; obj [ "a", bool true; "d", null ] ]
    ; [ obj [ "a", bool false ] ; obj [ "a", bool true ] ]
    ; [ obj [ "a", bool true ] ; obj [ "a", bool true ] ]
    ; [ obj [] ; obj [ "a", null ] ]
    ; [ obj [ "a", null ] ; obj [] ]
    ; [ obj [] ; obj [] ]
    ];
  test_rtop
    EJsonRuntimeRecRemove
    [ [ obj ["a", null]; str "a" ]
    ; [ obj ["b", null; "a", bool false]; str "a" ]
    ; [ obj ["b", null; "a", bool false]; str "c" ]
    ; [ obj []; str "c" ]
    ];
  test_rtop
    EJsonRuntimeRecProject
    [ [ obj ["a", null]; arr [str "a"] ]
    ; [ obj ["a", null]; arr [str "a"; str "b"] ]
    ; [ obj ["a", null]; arr [str "b"] ]
    ; [ obj ["a", null; "b", null; "c", null]; arr [str "b"; str "a"] ]
    ; [ obj ["b", null; "c", null; "a", null]; arr [str "a"; str "b"] ]
    ; [ obj []; arr [] ]
    ; [ obj ["a", null]; arr [] ]
    ; [ obj []; arr [str "b"] ]
    ];
  test_rtop
    EJsonRuntimeSingleton
    [ [ arr [null] ]
    ; [ arr [null; null] ]
    ; [ arr [] ]
    ];
  test_rtop
    EJsonRuntimeUnion
    [ [ arr [null]; arr [null; bool true] ]
    ; [ arr []; arr [null] ]
    ; [ arr [null]; arr [] ]
    ; [ arr []; arr [] ]
    ];
  test_rtop
    EJsonRuntimeMinus
    [ [ arr [null]; arr [null; bool true] ]
    ; [ arr [bool true; bool false]; arr [bool true; bool false] ]
    ; [ arr [bool true; bool false]; arr [bool true] ]
    ; [ arr [bool true; bool false]; arr [bool false] ]
    ; [ arr [bool true; bool false]; arr [] ]
    ; [ arr []; arr [null] ]
    ; [ arr [null]; arr [] ]
    ; [ arr []; arr [] ]
    ];
  test_rtop
    EJsonRuntimeNatPlus
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ]

let _ =
  if !failed then exit 1
