open Wasm_util
open EJson

let cejson_to_bytes : _ cejson -> bytes =
  let open Bytes in
  function
  | Coq_cejnull ->
    let b = create 1 in
    set_uint8 b 0 0;
    b
  | Coq_cejbool false ->
    let b = create 1 in
    set_uint8 b 0 1;
    b
  | Coq_cejbool true ->
    let b = create 1 in
    set_uint8 b 0 2;
    b
  | Coq_cejnumber x ->
    let b = create 9 in
    set_uint8 b 0 3;
    set_int64_le b 1 (Int64.bits_of_float x);
    b
  | Coq_cejbigint x ->
    let b = create 9 in
    set_uint8 b 0 4;
    set_int64_le b 1 (Int64.bits_of_float (float_of_int x));
    b
  | Coq_cejstring s ->
    let s = Util.string_of_char_list s in
    let n = String.length s in
    let b = create (5 + n) in
    set_uint8 b 0 5;
    set_int32_le b 1 (Int32.of_int n);
    blit_string s 0 b 5 n;
    b
  | Coq_cejforeign _ -> unsupported "ejson encode: foreign"

let ejson_to_bytes x =
  (* collect byte segments in reverse order and track the overall length *)
  let segments, size = ref [], ref 0 in
  let append x =
    segments := x :: !segments;
    size := Bytes.length x + !size
  in
  let rec f = function
  | Coq_ejnull -> append (cejson_to_bytes Coq_cejnull)
  | Coq_ejbool x -> append (cejson_to_bytes (Coq_cejbool x))
  | Coq_ejnumber x -> append (cejson_to_bytes (Coq_cejnumber x))
  | Coq_ejbigint x -> append (cejson_to_bytes (Coq_cejbigint x))
  | Coq_ejstring x -> append (cejson_to_bytes (Coq_cejstring x))
  | Coq_ejforeign x -> append (cejson_to_bytes (Coq_cejforeign x))
  | _ -> failwith "ejson not supported" (* TODO *)
  in
  f x;
  (* create to-be-returned bytes and "fill" in reverse order. *)
  let b = Bytes.create !size in
  let rec f = function
    | [] -> assert (!size = 0)
    | s :: tl ->
      let n = Bytes.length s in
      size := !size - n;
      Bytes.blit s 0 b !size n;
      f tl
  in
  f !segments;
  b

let ejson_of_bytes b = Coq_ejnull (* TODO *)
