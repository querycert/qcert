let () =
  let objs = ref [] in
  for i = Array.length Sys.argv - 1 downto 1 do
    let json = Yojson.Safe.from_file Sys.argv.(i) in
    objs := json :: !objs
  done;
  Format.printf "%s@." (Yojson.Safe.pretty_to_string (`List !objs))
