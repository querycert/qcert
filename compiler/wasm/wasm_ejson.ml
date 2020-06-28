open Wasm_util
open EJson

let encode_const : cejson -> bytes = function
  | Coq_cejnull ->
    let b = Bytes.create 4 in
    Bytes.set_int32_le b 0 (Int32.of_int 0);
    b
  | Coq_cejbool false ->
    let b = Bytes.create 4 in
    Bytes.set_int32_le b 0 (Int32.of_int 1);
    b
  | Coq_cejbool true ->
    let b = Bytes.create 4 in
    Bytes.set_int32_le b 0 (Int32.of_int 2);
    b
  | Coq_cejnumber x ->
    let b = Bytes.create 12 in
    Bytes.set_int32_le b 0 (Int32.of_int 3);
    Bytes.set_int64_le b 4 (Int64.bits_of_float x);
    b
  | Coq_cejstring s ->
    let n = List.length s in
    let b = Bytes.create (8 + n) in
    Bytes.set_int32_le b 0 (Int32.of_int 4);
    Bytes.set_int32_le b 4 (Int32.of_int n);
    List.iteri (fun i c -> Bytes.set b (8 + i) c) s;
    b
  | Coq_cejbigint x -> unsupported "ejson encode: bigint"
  | Coq_cejforeign _ -> unsupported "ejson encode: foreign"

let encode : ejson -> bytes = function
  | Coq_ejnull -> encode_const (Coq_cejnull)
  | Coq_ejbool x -> encode_const (Coq_cejbool x)
  | Coq_ejnumber x -> encode_const (Coq_cejnumber x)
  | Coq_ejstring x -> encode_const (Coq_cejstring x)
  | Coq_ejarray _ -> unsupported "ejson encode: array"
  | Coq_ejobject _ -> unsupported "ejson encode: object"
  | Coq_ejforeign x -> encode_const (Coq_cejforeign x)
  | Coq_ejbigint x -> encode_const (Coq_cejbigint x)

let write mem alloc_p x =
  let data = encode x |> Bytes.to_string in
  let addr =
    match Wasm.Global.load alloc_p with
    | I32 x -> x
    | _ -> failwith "incompatible module (type of alloc_p)"
  and n =
    String.length data |> Int32.of_int
  in
  let open Wasm.Memory in
  store_bytes mem (Int64.of_int32 addr) data;
  Wasm.Global.store alloc_p (I32 (Int32.add n  addr));
  addr

let read mem addr : ejson =
  let open Wasm.Values in
  let open Wasm.Types in
  let open Wasm.Memory in
  let i32 addr offset =
    match load_value mem (Int64.of_int32 addr) (Int32.of_int offset) I32Type with
    | I32 x -> x
    | _ -> assert false
  and double addr offset =
    match load_value mem (Int64.of_int32 addr) (Int32.of_int offset) I64Type with
    | I64 x -> Int64.float_of_bits x
    | _ -> assert false
  in
  let rec r addr : ejson =
    match Int32.to_int (i32 addr 0) with
    | 0 -> Coq_ejnull
    | 1 -> Coq_ejbool false
    | 2 -> Coq_ejbool true
    | 3 -> Coq_ejnumber (double addr 4)
    | 4 ->
      let n = i32 addr 4 |> Int32.to_int in
      let addr = Int32.add addr (Int32.of_int 8) |> Int64.of_int32 in
      Coq_ejstring (load_bytes mem addr n |> Util.char_list_of_string)
    | _ -> unsupported "ejson read"
  in
  r addr
