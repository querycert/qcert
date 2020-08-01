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
    set_int64_le b 1 (Int64.of_int x);
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
  (* collect byte segments in reverse order and track the overall length. *)
  let segments, size = ref [], ref 0 in
  let open Bytes in
  let append x =
    segments := x :: !segments;
    size := length x + !size
  in
  let rec f = function
  | Coq_ejnull -> append (cejson_to_bytes Coq_cejnull)
  | Coq_ejbool x -> append (cejson_to_bytes (Coq_cejbool x))
  | Coq_ejnumber x -> append (cejson_to_bytes (Coq_cejnumber x))
  | Coq_ejbigint x -> append (cejson_to_bytes (Coq_cejbigint x))
  | Coq_ejstring x -> append (cejson_to_bytes (Coq_cejstring x))
  | Coq_ejforeign x -> append (cejson_to_bytes (Coq_cejforeign x))
  | Coq_ejarray x ->
    let b = create 5 in
    set_uint8 b 0 6;
    set_int32_le b 1 (List.length x |> Int32.of_int);
    append b;
    List.iter f x
  | Coq_ejobject x ->
    ( (* scope b *)
      let b = create 5 in
      set_uint8 b 0 7;
      set_int32_le b 1 (List.length x |> Int32.of_int);
      append b
    );
    List.iter (fun (k, v) ->
        let k = Util.string_of_char_list k in
        let n = String.length k in
        let b = create (n + 4) in
        set_int32_le b 0 (Int32.of_int n);
        blit_string k 0 b 4 n;
        append b;
        f v
      ) x
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

let ejson_of_bytes b =
  let p =
    let pointer = ref 0 in
    fun increment_by ->
      let r = !pointer in
      pointer := !pointer + increment_by;
      r
  in
  let open Bytes in
  let rec f () =
    match get_int8 b (p 1) with
    | 0 -> Coq_ejnull
    | 1 -> Coq_ejbool false
    | 2 -> Coq_ejbool true
    | 3 ->
      let x = get_int64_le b (p 8) |> Int64.float_of_bits in
      Coq_ejnumber x
    | 4 ->
      let x = get_int64_le b (p 8) |> Int64.to_int in
      Coq_ejbigint x
    | 5 ->
      let n = get_int32_le b (p 4) |> Int32.to_int in
      Coq_ejstring (sub_string b (p n) n |> Util.char_list_of_string)
    | 6 ->
      let n =
        get_int32_le b (p 4)
        |> Int32.to_int
      in
      Coq_ejarray (List.init n (fun _ -> f ()))
    | 7 ->
      let n =
        get_int32_le b (p 4)
        |> Int32.to_int
      in
      Coq_ejobject (List.init n (fun _ ->
          let n = get_int32_le b (p 4) |> Int32.to_int in
          let key = sub_string b (p n) n |> Util.char_list_of_string in
          key, f ()
        ))
    | _ -> failwith "ejson_of_bytes: unknown tag"
  in
  f ()
