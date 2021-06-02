open Qcert_lib

module ImpEJson = struct
  include Imp
  include EJson
  include EJsonOperators
  include EJsonRuntimeOperators
  include ImpEJson
end
open ImpEJson

let brands = ref []
let add_brand_relation sub sup =
  brands := ( Util.char_list_of_string sub
            , Util.char_list_of_string sup
            ) :: !brands

let imp_eval (imp_ejson : _ imp_ejson) env : _ ejson option =
  let open ImpEJsonEval in
  let open EnhancedEJson in
  imp_ejson_eval_top_on_ejson
    enhanced_foreign_ejson
    enhanced_foreign_ejson_runtime
    !brands env imp_ejson

module Wasm_backend = Wasm_backend.Make(ImpEJson)

let foreign_ejson_to_wson ej =
  failwith ("This should convert foreign data to WASM")
let wasm_eval (imp_ejson : _ imp_ejson) env : _ ejson option =
  let wasm_ast =
    Wasm_backend.imp_ejson_to_wasm_ast !brands foreign_ejson_to_wson imp_ejson
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

let test_fn ?(fixup=fun x -> x) ?(verbose=false) info env fn =
  let imp_ejson : _ imp_ejson = [['f'], fn] in
  let fail message =
    print_endline "";
    info ();
    print_string ("FAILED: ");
    print_endline message;
    failed := true
  in
  match imp_eval imp_ejson env, wasm_eval imp_ejson env with
  | None, _ -> fail "imp eval failed"
  | Some _, None -> fail "wasm eval failed"
  | Some imp, Some wasm ->
    if (not (ejson_eq (fixup wasm) (fixup imp))) then (
      fail "wasm and imp differ";
      print_string ("imp:  ");
      print_endline (ejson_to_string imp);
      print_string ("wasm: ");
      print_endline (ejson_to_string wasm);
    ) else if verbose then (
      print_endline "";
      info ();
      print_string "result: ";
      print_endline (ejson_to_string imp)
    )

let test_expr_1 ?fixup ?verbose info expr op args =
  let varname i =  Util.char_list_of_string ("arg" ^ (string_of_int i))
  and info () =
    info ();
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
  test_fn ?fixup ?verbose info env (ImpFun (['x'], stmt, return))

let test_expr ?fixup ?verbose info expr op args =
  List.iter (fun args -> test_expr_1 ?fixup ?verbose info expr op args) args

let test_op ?verbose op =
  test_expr ?verbose
    (fun () ->
       print_string "operator: ";
       print_endline (Wasm_backend.string_of_operator op)
    )
    (fun op args -> ImpExprOp (op, args))
    op

let test_rtop ?fixup ?verbose op =
  test_expr ?fixup ?verbose
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

let sort_array (x : _ ejson) =
  match x with
  | Coq_ejarray z -> Coq_ejarray (List.sort compare z)
  | z -> z

let _ =
  let open Arg in
  test_op
    EJsonOpAddNumber
    [ [num 41.; num 1.]
    ; [num (-1.); num 1e32]
    ; [num (-1.); num Float.infinity]
    ];
  test_op
    EJsonOpArray
    [ []
    ; [null]
    ; [null; null; null]
    ];
  test_op
    EJsonOpArrayLength
    [ [ arr [bool true; bool false] ]
    ; [ arr [null] ]
    ; [ arr [] ]
    ];
  test_op
    EJsonOpArrayPush
    [ [ arr []; null ]
    ; [ arr [int 0]; int 1 ]
    ];
  test_op
    EJsonOpArrayAccess
    [ [ arr [null]; int 0 ]
    ; [ arr [int 0; int 1; int 2]; int 0 ]
    ; [ arr [int 0; int 1; int 2]; int 1 ]
    ; [ arr [int 0; int 1; int 2]; int 2 ]
    (* ; [ arr [null]; int 1 ] invalid / out of bounds *)
    ];
  test_op
    (EJsonOpObject [])
    [ []
    ];
  test_op
    (EJsonOpObject [['a']])
    [ [null]
    ];
  test_op
    (EJsonOpObject [['a']; ['b']])
    [ [null; null]
    ; [int 1; bool true]
    ];
  test_op
    (EJsonOpAccess ['a'])
    [ [ obj ["a", null] ]
    ; [ obj ["a", int 0; "b", int 1; "c", int 2] ]
    ; [ obj ["b", int 0; "a", int 1; "c", int 2] ]
    (* ; [ obj []] invalid / missing key *)
    ];
  test_op
    (EJsonOpHasOwnProperty ['a'])
    [ [ obj ["a", null] ]
    ; [ obj ["a", int 0; "b", int 1; "c", int 2] ]
    ; [ obj ["b", int 0; "a", int 1; "c", int 2] ]
    ; [ obj ["b", int 0; "c", int 2] ]
    ; [ obj []]
    ];
  List.iter (fun op ->
      test_op op
        [ [ num 42.; num 0. ]
        ; [ num 0.; num 42. ]
        ; [ num (-1.); num 1. ]
        (* ; [ num Float.nan; num Float.nan ] nan <> nan *)
        ; [ num 2.; num 1024. ]
        ; [ num 1e32; num 43. ]
        ; [ num Float.infinity; num Float.neg_infinity ]
        ])
    [ EJsonOpMathMin
    ; EJsonOpMathMax
    ; EJsonOpMathPow
    ];
  List.iter (fun op ->
      test_op op
        [ [ num 42. ]
        ; [ num 0.2 ]
        ; [ num 1. ]
        (* ; [ num Float.nan ] (* nan <> nan *) *)
        ; [ num 3.14 ]
        ; [ num 1e32 ]
        ; [ num Float.infinity ]
        ])
    [ EJsonOpMathExp
    ; EJsonOpMathAbs
    ; EJsonOpMathLog
    ; EJsonOpMathLog10
    ; EJsonOpMathCeil
    ; EJsonOpMathFloor
    ];
  List.iter (fun op ->
      test_op op
        [ [ num (-42.) ]
        ; [ num (-0.2) ]
        ; [ num (-1.) ]
        ; [ num (-3.14) ]
        ; [ num 1e32 ]
        ; [ num Float.neg_infinity ]
        ])
    [ EJsonOpMathExp
    ; EJsonOpMathAbs
    ; EJsonOpMathCeil
    ; EJsonOpMathFloor
    ];
  test_op
    EJsonOpMathTrunc
    [ [ num 1.1 ]
    ; [ num 10000.7 ]
    ; [ num (-1.) ]
    ; [ num (-3.14) ]
    ; [ num (-3.94) ]
    ; [ num (-1000000.94) ]
    ];
  let compare_values =
    [ null
    ; bool false
    ; int 1
    ; num 1.
    ; str "hello world"
    ; arr [bool false]
    ; obj [ "a" , bool true ]
    ]
  in
  let compare_pairs =
    List.map (fun a ->
        List.map (fun b ->
            [ a; b ]
          ) compare_values
      ) compare_values
    |> List.concat
  in
  test_rtop EJsonRuntimeEqual compare_pairs;
  test_rtop EJsonRuntimeEqual
    [ [ bool true; bool false ]
    ; [ int 0; int 1 ]
    ; [ num 0.; num 1. ]
    ; [ str "abc"; str "abC" ]
    ; [ obj [ "a", bool true; "b", bool false ]
      ; obj [ "b", bool false; "a", bool true ] ]
    ; [ arr [int 0; int 1]; arr [int 1; int 0] ]
    ];
  test_rtop
    EJsonRuntimeCompare (* Wasm and JS compare support arguments of different
                           type.  This is used to speed up set operations.
                           Coq/Imp implements set operations naively and only
                           compares integers and numbers. *)
    [ [ int 0; int 1]
    ; [ int 1; int 0]
    ; [ int 1; int 1]
    ; [ num 0.; num 1.]
    ; [ num 1.; num 0.]
    ; [ num 1.; num 1.]
    ];
  test_rtop ~fixup:sort_array
    EJsonRuntimeMax (* ... we trigger the wasm compare on heterogeneous types
                       using set union. *)
    (List.map (fun x -> [arr x; arr (List.rev x)]) compare_pairs)
  ;
  test_rtop
    EJsonRuntimeToString
    [ [ null ]
    ; [ bool true ]
    ; [ bool false ]
    ; [ num 3.14 ]
    ; [ int 42 ]
    ; [ str "hello world" ]
    ; [ str "utf8: α ☻ works" ]
    ; [ arr []]
    ; [ arr [null]]
    ; [ arr [null; null]]
    ; [ arr (List.init 42 (fun _ -> null))]
    ; [ obj [] ]
    ; [ obj ["a", null] ]
    ; [ obj ["a", null; "b", null] ]
    ; [ obj (List.init 21 (fun i -> ("v" ^ (string_of_int i), null))) ]
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
    EJsonRuntimeRecDot
    [ [ obj ["a", null]; str "a" ]
    ; [ obj ["a", int 0; "b", int 1; "c", int 2]; str "a" ]
    ; [ obj ["b", int 0; "a", int 1; "c", int 2]; str "a" ]
      (* ; [ obj []; str "a"] invalid / missing key *)
    ];
  test_rtop
    EJsonRuntimeArray
    [ [ int 1; null; int 3 ]
    ; []
    ; [ null ]
    ];
  test_rtop
    EJsonRuntimeArrayLength
    [ [ arr [bool true; bool false] ]
    ; [ arr [null] ]
    ; [ arr [] ]
    ];
  test_rtop
    EJsonRuntimeArrayPush
    [ [ arr []; null ]
    ; [ arr [int 0]; int 1 ]
    ];
  test_rtop
    EJsonRuntimeArrayAccess
    [ [ arr [null]; int 0 ]
    ; [ arr [int 0; int 1; int 2]; int 0 ]
    ; [ arr [int 0; int 1; int 2]; int 1 ]
    ; [ arr [int 0; int 1; int 2]; int 2 ]
      (* ; [ arr [null]; int 1 ] (* invalid / out of bounds *) *)
    ];
  test_rtop
    EJsonRuntimeUnbrand
    [ [ obj ["$class", arr [str "brand0"]; "$data", int 42 ] ]
    ];
  add_brand_relation "/a" "/";
  add_brand_relation "/a/a" "/a";
  add_brand_relation "/a/a" "/";
  add_brand_relation "/b" "/";
  add_brand_relation "/b/b" "/b";
  add_brand_relation "/b/b" "/";
  test_rtop (* ~verbose:true *)
    EJsonRuntimeCast
    [ [ arr [ str "/" ] (* target brand *)
      ; obj [ "$class", arr [str "/"] (* brands *)
            ; "$data", int 42 ]
      ]
    ; [ arr [ str "/" ] (* target brand *)
      ; obj [ "$class", arr [str "/a"] (* brands *)
            ; "$data", int 42 ]
      ]
    ; [ arr [ str "/" ] (* target brand *)
      ; obj [ "$class", arr [str "/a/a"] (* brands *)
            ; "$data", int 42 ]
      ]
    ; [ arr [ str "/a"; str "/b" ] (* target brand *)
      ; obj [ "$class", arr [str "/a/a"; str "/b/b"] (* brands *)
            ; "$data", int 42 ]
      ]
    ; [ arr [ str "/a"; str "/b" ] (* target brand *)
      ; obj [ "$class", arr [str "/"; str "/b/b"] (* brands *)
            ; "$data", int 42 ]
      ]
    ];
  test_rtop
    EJsonRuntimeSingleton
    [ [ arr [null] ]
    ; [ arr [null; null] ]
    ; [ arr [] ]
    ];
  test_rtop
    EJsonRuntimeUnion (* Array Concatenation *)
    [ [ arr [null]; arr [null; bool true] ]
    ; [ arr []; arr [null] ]
    ; [ arr [null]; arr [] ]
    ; [ arr []; arr [] ]
    ];
  test_rtop
    EJsonRuntimeMinus (* Set Minus *)
    [ [ arr [null]; arr [null; bool true] ]
    ; [ arr [bool true; bool false]; arr [bool true; bool false] ]
    ; [ arr [bool true; bool false]; arr [bool true] ]
    ; [ arr [bool true; bool false]; arr [bool false] ]
    ; [ arr [bool true; bool false]; arr [] ]
    ; [ arr []; arr [null] ]
    ; [ arr [null]; arr [] ]
    ; [ arr []; arr [] ]
    ];
  (* ImpEJson eval does not sort the arrays.
   * JS runtime and WASM runtime do sort the arrays. *)
  test_rtop ~fixup:sort_array
    EJsonRuntimeMin (* Set Intersection *)
    [ [arr []; arr []]
    ; [arr [bool true]; arr [bool true]]
    ; [arr [bool true]; arr [bool false]]
    ; [arr [bool false]; arr [bool true]]
    ; [arr [bool true]; arr [bool true; bool false]]
    ; [arr [bool true; bool false]; arr [bool true; null]]
    ; [arr [int 1; int 2]; arr [int 1; int 2]]
    ];
  (* ImpEJson eval does not sort the arrays.
   * JS runtime and WASM runtime do sort the arrays. *)
  test_rtop ~fixup:sort_array
    EJsonRuntimeMax (* Set Union *)
    [ [arr []; arr []]
    ; [arr [bool true]; arr [bool true]]
    ; [arr [bool true]; arr [bool false]]
    ; [arr [bool false]; arr [bool true]]
    ; [arr [bool true]; arr [bool true; bool false]]
    ; [arr [bool true; bool false]; arr [bool true]]
    ; [arr [bool true; bool false]; arr [bool true; null]]
    ; [arr [int 3; int 2; int 1]; arr [int 6; int 2; int 1; int 0]]
    ; [arr [ obj [ "a", bool true; "b", bool false ] ]
      (* Imp does not recognize these two objects as equal! *)
      ;arr [ obj [ "b", bool false; "a", bool true ] ] ]
    ];
  test_rtop
    EJsonRuntimeNth
    [ [ arr [bool true]; int 0 ]
    ; [ arr [bool true]; int (-1) ]
    ; [ arr [bool true]; int 1 ]
    ];
  test_rtop
    EJsonRuntimeCount
    [ [ arr [bool true; bool false] ]
    ; [ arr [null] ]
    ; [ arr [] ]
    ];
  test_rtop
    EJsonRuntimeContains
    [ [ null; arr [] ]
    ; [ null; arr [null] ]
    ; [ null; arr [bool true] ]
    ; [ bool true; arr [bool true; bool false] ]
    ; [ bool false; arr [bool true; null] ]
    ; [ int 0; arr [int 0; int 1; int 2] ]
    ; [ int 1; arr [int 0; int 1; int 2] ]
    ; [ int 2; arr [int 0; int 1; int 2] ]
    ; [ int 3; arr [int 0; int 1; int 2] ]
    ];
  test_rtop
    EJsonRuntimeLength
    [ [ str "" ]
    ; [ str "a" ]
    ; [ str "abcc" ]
      (* ; [ str "abccᵤ" ] *) (* Coq uses char list, JS/Wasm use UTF16. *)
    ];
  test_rtop
    EJsonRuntimeSubstring (* string, start, target length *)
    [ [ str "" ; int 0; int 0 ]
    ; [ str "" ; int 1; int 1 ]
    ; [ str "" ; int 1; int (-1) ]
    ; [ str "0" ; int 0; int 1 ]
    ; [ str "0" ; int 0; int 0 ]
    ; [ str "0" ; int 0; int (-1) ]
    ; [ str "012345" ; int 0; int 3 ]
    ; [ str "012345" ; int 2; int 3 ]
    ; [ str "012345" ; int 0; int 6 ]
    ];
  test_rtop
    EJsonRuntimeSubstringEnd
    [ [ str "" ; int 0]
    ; [ str "" ; int 1]
    ; [ str "0" ; int 0]
    ; [ str "012345" ; int 0]
    ; [ str "012345" ; int 2]
    ; [ str "012345" ; int 5]
    ; [ str "012345" ; int 6]
    ];
  test_rtop
    EJsonRuntimeStringJoin (* sep, string array *)
    [ [ str ""; arr [] ]
    ; [ str "_"; arr [] ]
    ; [ str "_"; arr [str "-"] ]
    ; [ str "_"; arr [str "-"; str "-"] ]
    ; [ str "/"; arr [str "a"; str "b"; str "c"] ]
    ];
  test_rtop
    EJsonRuntimeLike
    [ [ str "abc"; str "abc" ]
    ; [ str "b"; str "abc" ]
    ; [ str "%b%"; str "abc" ]
    ; [ str "_b_"; str "abc" ]
    ; [ str "_"; str "abc" ]
    ; [ str "%"; str "abc" ]
    ; [ str ".*"; str "abc" ]
    ];
  test_rtop
    EJsonRuntimeNatLt
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ];
  test_rtop
    EJsonRuntimeNatLe
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ];
  test_rtop
    EJsonRuntimeNatPlus
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ];
  test_rtop
    EJsonRuntimeNatMinus
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ];
  test_rtop
    EJsonRuntimeNatMult
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ; [int (-43); int (-1)]
    ; [int (-43); int 2]
    ];
  test_rtop
    EJsonRuntimeNatDiv
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ; [int 43; int 0]
    ; [int 43; int 2]
    ; [int 64; int 16]
    ];
  test_rtop
    EJsonRuntimeNatRem
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ; [int 43; int 0]
    ; [int 43; int 2]
    ; [int 64; int 16]
    ];
  test_rtop
    EJsonRuntimeNatAbs
    [ [int (-41)]
    ; [int 1]
    ; [int 43]
    ; [int (-1)]
    ];
  test_rtop
    EJsonRuntimeNatLog2
    [ [int 1]
    ; [int 0]
    (* ; [int (-41)] (* Imp returns 0 *) *)
    ; [int 43]
    ; [int (1 lsl 20)]
    ; [int (1 lsl 61)]
      (* ; [int (-1)] (* Imp returns 0 *) *)
      (* ; [int max_int] (* Wasm off by one *) *)
      (* ; [int min_int] (* Imp returns 0 *) *)
    ];
  test_rtop
    EJsonRuntimeNatSqrt
    [ [int (-41)]
    ; [int 1]
    ; [int 0]
    ; [int 43]
    ; [int (-1)]
    ; [int 16]
    ; [int (-49)]
    (* ; [int max_int] (* wasm and imp differ slightly *) *)
    ; [int (max_int / 2)]
    ; [int min_int]
    ];
  test_rtop
    EJsonRuntimeNatMinPair
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ; [int 43; int 0]
    ; [int 43; int 2]
    ; [int 64; int 16]
    ];
  test_rtop
    EJsonRuntimeNatMaxPair
    [ [int 41; int 1]
    ; [int 43; int (-1)]
    ; [int 43; int 0]
    ; [int 43; int 2]
    ; [int 64; int 16]
    ];
  test_rtop
    EJsonRuntimeNatSum
    [ [arr [int 0]]
    ; [arr []]
    ; [arr (List.init 42 (fun i -> int i))]
    ; [arr (List.init 42 (fun i -> int (-i)))]
    ; [arr [int min_int; int max_int]]
    ; [arr [int min_int; int (-1)]]
    ; [arr [int max_int; int 1]]
    ];
  test_rtop
    EJsonRuntimeNatMin
    [ [arr [int 0]]
    ; [arr []]
    ; [arr (List.init 42 (fun i -> int i))]
    ; [arr (List.init 42 (fun i -> int (-i)))]
    ; [arr [int min_int; int max_int]]
    ; [arr [int min_int; int (-1)]]
    ; [arr [int max_int; int 1]]
    ];
  test_rtop
    EJsonRuntimeNatMax
    [ [arr [int 0]]
    ; [arr []]
    ; [arr (List.init 42 (fun i -> int i))]
    ; [arr (List.init 42 (fun i -> int (-i)))]
    ; [arr [int min_int; int max_int]]
    ; [arr [int min_int; int (-1)]]
    ; [arr [int max_int; int 1]]
    ];
  test_rtop
    EJsonRuntimeNatArithMean
    [ [arr [int 0]]
    ; [arr []]
    ; [arr [int 1; int 1]]
    ; [arr [int 1; int 2]]
    ; [arr [int 1; int 3]]
    ; [arr (List.init 42 (fun i -> int i))]
    ; [arr (List.init 42 (fun i -> int (-i)))]
    ; [arr [int min_int; int max_int]]
    ; [arr [int min_int]]
    ; [arr [int max_int]]
    ];
  test_rtop
    EJsonRuntimeFloatOfNat
    [ [int 42]
    ; [int 0]
    ; [int (-1)]
    ; [int max_int]
    ; [int min_int]
    ; [int (min_int + 1)]
    ];
  test_rtop
    EJsonRuntimeFloatSum
    [ [arr [num 0.]]
    ; [arr []]
    ; [arr [num 1.; num 1.]]
    ; [arr [num 1.; num 2.]]
    ; [arr [num 1.; num 3.]]
    ; [arr (List.init 42 (fun i -> num (float_of_int i)))]
    ; [arr (List.init 42 (fun i -> num (1. /. (float_of_int (-i)))))]
    ; [arr [num min_float; num max_float]]
    ; [arr [num min_float; num (-1.)]]
    ; [arr [num max_float; num 1.]]
    ];
  test_rtop
    EJsonRuntimeFloatArithMean
    [ [arr [num 0.]]
    ; [arr []]
    ; [arr [num 1.; num 1.]]
    ; [arr [num 1.; num 2.]]
    ; [arr [num 1.; num 3.]]
    ; [arr (List.init 42 (fun i -> num (float_of_int i)))]
    ; [arr (List.init 42 (fun i -> num (1. /. (float_of_int (-i)))))]
    ; [arr [num min_float; num max_float]]
    ; [arr [num min_float; num (-1.)]]
    ; [arr [num max_float; num 1.]]
    ];
  test_rtop
    EJsonRuntimeFloatMin
    [ [arr [num 0.]]
    ; [arr []]
    ; [arr [num 1.; num 1.]]
    ; [arr [num 1.; num 2.]]
    ; [arr [num 1.; num 3.]]
    ; [arr (List.init 42 (fun i -> num (float_of_int i)))]
    ; [arr (List.init 42 (fun i -> num (1. /. (float_of_int (-i)))))]
    ; [arr [num min_float; num max_float]]
    ; [arr [num min_float; num (-1.)]]
    ; [arr [num max_float; num 1.]]
    ];
  test_rtop
    EJsonRuntimeFloatMax
    [ [arr [num 0.]]
    ; [arr []]
    ; [arr [num 1.; num 1.]]
    ; [arr [num 1.; num 2.]]
    ; [arr [num 1.; num 3.]]
    ; [arr (List.init 42 (fun i -> num (float_of_int i)))]
    ; [arr (List.init 42 (fun i -> num (1. /. (float_of_int (-i)))))]
    ; [arr [num min_float; num max_float]]
    ; [arr [num min_float; num (-1.)]]
    ; [arr [num max_float; num 1.]]
    ];
  test_rtop
    EJsonRuntimeNatOfFloat
    [ [num 42.]
    ; [num 0.]
    ; [num (-0.5)]
    ; [num 0.5]
    ; [num 0.9]
    ; [num max_float]
    ; [num min_float]
    ];
  ()

let _ =
  if !failed then exit 1
