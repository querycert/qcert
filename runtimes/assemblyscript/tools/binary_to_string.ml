let arg =
  match Sys.argv with
  | [| _; x |] -> x
  | _ -> failwith "binary_to_string: provide file as single argument"

let rt =
  if Sys.file_exists arg then arg
  else failwith (Printf.sprintf "%s does not exist" arg)

let bin =
  let ic = open_in rt in
  let rec read acc =
    match input_line ic with
    | l -> read (l :: acc)
    | exception End_of_file ->
      List.rev acc |> String.concat "\n"
  in
  read []

let () = String.iter (fun c -> Printf.printf "\\x%02x" (int_of_char c)) bin
