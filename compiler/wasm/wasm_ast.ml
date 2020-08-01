open Wasm

type t = Ast.module_

(* assemblyscript error handler imported by runtime *)
let abort =
  let f = function
    | Values.[I32 _msg; I32 _file; I32 line; I32 column] ->
      failwith (
        (* TODO read strings from runtime memory *)
        Printf.sprintf "Runtime error in Assemblyscript position %s:%s"
                (Int32.to_string line) (Int32.to_string column)
      )
    | _ -> assert false
  in
  Func.alloc_host Types.(FuncType ([I32Type; I32Type; I32Type; I32Type], [])) f

(* load Wasm runtime from file specified in WASM_RUNTIME env *)
let runtime () =
  match Sys.getenv_opt "WASM_RUNTIME" with
  | Some rt when Sys.file_exists rt ->
    let ic = open_in rt in
    let bs =
      let rec read acc =
        match input_line ic with
        | l -> read (l :: acc)
        | exception End_of_file ->
          List.rev acc |> String.concat "\n"
      in
      read []
    in
    let m = Decode.decode rt bs in
    let () =
      try Valid.check_module m
      with _ -> failwith "WASM_RUNTIME does not pass validation"
    in
    m
  | None ->
    failwith "WASM_RUNTIME environment variable is missing"
  | Some rt ->
    failwith (Printf.sprintf "WASM_RUNTIME=%s is not a file" rt)

let eval brand_relations module_ env =
  let rt = Eval.init (runtime ()) [ExternFunc abort] in
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
  and rt_ejson_to_bytes =
    match Instance.export rt (Utf8.decode "ejson_to_bytes") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "runtime module should export ejson_to_bytes function"
  and rt_ejson_of_bytes =
    match Instance.export rt (Utf8.decode "ejson_of_bytes") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "runtime module should export ejson_of_bytes function"
  and rt_mem =
    match Instance.export rt (Utf8.decode "memory") with
    | Some (ExternMemory x) -> x
    | _ -> failwith "runtime module should export its memory"
  in
  let write_ejson x =
    let bin = Wasm_binary_ejson.ejson_to_bytes x in
    let n = Bytes.length bin in
    let bin_ptr =
      let x =
        Eval.invoke rt_alloc [I32 (Int32.of_int n); I32 (Int32.zero)]
        |> Eval.invoke rt_retain
      in
      match x with
      | [I32 x] -> x
      | _ -> failwith "invalid runtime: type of __alloc or __retain"
    in
    let () =
      Memory.store_bytes rt_mem (Int64.of_int32 bin_ptr) (Bytes.to_string bin)
    in
    match Eval.invoke rt_ejson_of_bytes [I32 bin_ptr] with
    | [I32 x] -> x
    | _ -> failwith "invalid runtime: type of ejson_of_bytes"
  in
  let main =
    match Instance.export mod_ (Utf8.decode "main") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "module should export main function"
  and argument_ptr = write_ejson (EJson.Coq_ejobject env)
  and relatations_ptr =
    let x = List.map (fun (a, b) -> a, EJson.Coq_ejstring b) brand_relations in
    write_ejson (EJson.Coq_ejobject x)
  in
  let result_ptr =
    match Eval.invoke main [I32 relatations_ptr; I32 argument_ptr] with
    | [I32 x] -> x
    | _ -> failwith "invalid module: return value of main"
  in
  let result =
    let bin_ptr =
      match Eval.invoke rt_ejson_to_bytes [I32 result_ptr] with
      | [I32 x] -> x
      | _ -> failwith "invalid runtime: type of ejson_to_bytes"
    in
    let n =
      match Memory.load_value rt_mem Int64.(sub (of_int32 bin_ptr) (of_int 4))
              Int32.zero Types.I32Type with
      | I32 x -> Int32.to_int x
      | _ -> failwith "could not read length of result"
    in
    Memory.load_bytes rt_mem (Int64.of_int32 bin_ptr) n
    |> Bytes.of_string
    |> Wasm_binary_ejson.ejson_of_bytes
  in
  Some result

let imp_ejson_to_wasm_ast i = Wasm_translate.imp i
let to_string q =
  let sexpr = Arrange.module_ q in
  Sexpr.to_string 72 sexpr
