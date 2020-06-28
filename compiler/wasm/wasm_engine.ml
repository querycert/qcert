type instance =
  { module_: Wasm.Instance.module_inst
  ; memory : Wasm.Instance.memory_inst
  ; alloc_p : Wasm.Instance.global_inst
  }

let init m =
  let module_ = Wasm.Eval.init m [] in
  let memory =
    match List.assoc_opt (Wasm.Utf8.decode "memory") module_.exports with
    | Some (ExternMemory m) -> m
    | _ -> failwith "incompatible module (memory)"
  and alloc_p =
    match List.assoc_opt (Wasm.Utf8.decode "alloc_p") module_.exports with
    | Some (ExternGlobal m) -> m
    | _ -> failwith "incompatible module (alloc_p)"
  in
  { module_; alloc_p; memory }

let invoke inst arg =
  let func =
    match List.assoc_opt (Wasm.Utf8.decode "main") inst.module_.exports with
    | Some (ExternFunc f) -> f
    | _ -> raise Not_found
  in
  let arg = Wasm_ejson.write inst.memory inst.alloc_p arg in
  let ret =
    match Wasm.Eval.invoke func [I32 arg] with
    | [I32 x] -> x
    | _ -> failwith "incompatible module (return type)"
  in
  Wasm_ejson.read inst.memory ret
