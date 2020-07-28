type t = Wasm.Ast.module_

let abort =
  let open Wasm in
  Func.alloc_host Types.(FuncType ([I32Type; I32Type; I32Type; I32Type], []))
    ( function
    | [I32 _msg; I32 _file; I32 line; I32 column] ->
      failwith ("Runtime error in Assemblyscript position " ^
                (Int32.to_string line) ^ ":" ^ (Int32.to_string column))
    | _ -> assert false
    )

let runtime () =
  match Sys.getenv_opt "WASM_RUNTIME" with
  | None -> failwith "WASM_RUNTIME environment variable is missing"
  | Some rt ->
    if Sys.file_exists rt then (
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
      let m = Wasm.Decode.decode rt bs in
      let () =
        try Wasm.Valid.check_module m
        with _ -> failwith "WASM_RUNTIME does not pass validation"
      in
      m
    )
    else failwith "WASM_RUNTIME does not point to file"

let eval j module_ env =
  let rt = Wasm.Eval.init (runtime ()) [ExternFunc abort] in
  let () = Wasm.Valid.check_module module_ in
  let instance =
    let imports = List.map (fun (import : Wasm.Ast.import) ->
        if import.it.module_name <> (Wasm.Utf8.decode "runtime") then
          failwith "cannot satisfy import from unknown module";
        match Wasm.Instance.export rt import.it.item_name with
        | None -> failwith ("cannot satisfy import of function " ^
                            (Wasm.Utf8.encode import.it.item_name))
        | Some export ->
          let is = Wasm.Instance.extern_type_of export
          and should = Wasm.Ast.import_type module_ import
          in
          if is <> should then failwith "type mismatch on import";
          export
      ) module_.it.imports
    in
    Wasm.Eval.init module_ imports
  and rt_alloc =
    match Wasm.Instance.export rt (Wasm.Utf8.decode "__alloc") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "runtime module should export __alloc function"
  and rt_retain =
    match Wasm.Instance.export rt (Wasm.Utf8.decode "__retain") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "runtime module should export __retain function"
  and rt_ejson_to_bytes =
    match Wasm.Instance.export rt (Wasm.Utf8.decode "ejson_to_bytes") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "runtime module should export ejson_to_bytes function"
  and rt_ejson_of_bytes =
    match Wasm.Instance.export rt (Wasm.Utf8.decode "ejson_of_bytes") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "runtime module should export ejson_of_bytes function"
  and rt_mem =
    match rt.memories with
    | [x] -> x
    | _ -> failwith "runtime module should have a single memory"
  in
  let main =
    match Wasm.Instance.export instance (Wasm.Utf8.decode "main") with
    | Some (ExternFunc f) -> f
    | _ -> failwith "module should export main function"
  and argument_ptr =
    let bin = Wasm_binary_ejson.ejson_to_bytes (EJson.Coq_ejobject env) in
    let n = Bytes.length bin in
    let bin_ptr =
      let x =
        Wasm.Eval.invoke rt_alloc [I32 (Int32.of_int n); I32 (Int32.zero)]
        |> Wasm.Eval.invoke rt_retain
      in
      match x with
      | [I32 x] -> x
      | _ -> failwith "invalid runtime: type of __alloc or __retain"
    in
    let () =
      Wasm.Memory.store_bytes rt_mem (Int64.of_int32 bin_ptr) (Bytes.to_string bin)
    in
    match Wasm.Eval.invoke rt_ejson_of_bytes [I32 bin_ptr] with
    | [I32 x] -> x
    | _ -> failwith "invalid runtime: type of ejson_of_bytes"
  in
  let result_ptr =
    match Wasm.Eval.invoke main [I32 argument_ptr] with
    | [I32 x] -> x
    | _ -> failwith "invalid module: return value of main"
  in
  let result =
    let bin_ptr =
      match Wasm.Eval.invoke rt_ejson_to_bytes [I32 result_ptr] with
      | [I32 x] -> x
      | _ -> failwith "invalid runtime: type of ejson_to_bytes"
    in
    let n =
      match Wasm.Memory.load_value rt_mem Int64.(sub (of_int32 bin_ptr) (of_int 4))
              Int32.zero Wasm.Types.I32Type with
      | I32 x -> Int32.to_int x
      | _ -> failwith "could not read length of result"
    in
    Wasm.Memory.load_bytes rt_mem (Int64.of_int32 bin_ptr) n
    |> Bytes.of_string
    |> Wasm_binary_ejson.ejson_of_bytes
  in
  Some result

let imp_ejson_to_wasm_ast i = Wasm_translate.imp i
let to_string q =
  let sexpr = Wasm.Arrange.module_ q in
  Wasm.Sexpr.to_string 72 sexpr
