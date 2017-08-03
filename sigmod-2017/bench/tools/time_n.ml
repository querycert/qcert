let time cmd =
  let start = Unix.gettimeofday () in
  let _ = Sys.command cmd in
  let stop = Unix.gettimeofday () in
  (stop -. start)

let time_n n cmd =
  let rec time_n n tmin tmax total =
    if n <= 0 then (tmin, tmax, total)
    else
      let t = time cmd in
      time_n (n - 1) (min tmin t) (max tmax t) (t +. total)
  in
  let t = time cmd in
  let tmin, tmax, total = time_n (n - 1) t t t in
  (tmin, tmax, total /. (float n))

let () =
  if Array.length Sys.argv < 3 then begin
    Format.eprintf "Usage: %s n cmd@." Sys.argv.(0);
    exit 1
  end;
  let n = int_of_string Sys.argv.(1) in
  let cmd =
    let s = ref "" in
    for i = 2 to Array.length Sys.argv - 1 do
      s := !s^Sys.argv.(i)^" "
    done;
    !s
  in
  let tmin, tmax, tavg = time_n n cmd in
  Format.printf "%f, %f, %f@." tmin tmax tavg

