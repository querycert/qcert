type nnrc_stat =
    { nnrc_no_optim : nnrc_stat_body;
      nnrc_optim : nnrc_stat_body; }
and nnrc_stat_body =
    { nnrc_size : int; }

type nra_stat =
    { nra_no_optim : nra_stat_body;
      nra_optim : nra_stat_body; }
and nra_stat_body =
    { nra_size : int;
      nra_depth : int;
      nra_to_nnrc : nnrc_stat; }

type nraenv_stat =
    { nraenv_no_optim : nraenv_stat_body;
      nraenv_optim : nraenv_stat_body; }
and nraenv_stat_body =
    { nraenv_size : int;
      nraenv_depth : int;
      nraenv_to_nnrc : nnrc_stat;
      nraenv_to_nra : nra_stat; }

type camp_stat =
    { camp_size : int;
      camp_to_nraenv : nraenv_stat;
      camp_to_nra : nra_stat; }

type rule_stat =
    { rule_size : int;
      rule_to_nraenv : nraenv_stat;
      rule_to_nra : nra_stat; }

type oql_stat =
    { oql_size : int;
      oql_to_nraenv : nraenv_stat; }

type stat =
  | Stat_rule of string * rule_stat
  | Stat_camp of string * camp_stat
  | Stat_oql of string * oql_stat


(* type source_path = *)
(*   | Psource of stat *)
(*   | Psource_rule of rule_path *)
(*   | Psource_pat of pat_path *)
(*   | Psource_oql of oql_path *)
(* and rule_path = *)
(*   | Prule of rule_stat *)
(*   | Prule_to_nraenv of nraenv_path *)
(*   | Prule_to_nra of nra_path *)
(* and pat_path = *)
(*   | Ppat of pat_stat *)
(*   | Ppat_to_nraenv of nraenv_path *)
(*   | Ppat_to_nra of nra_path *)
(* and oql_oqlh = *)
(*   | Poql of oql_stat *)
(*   | Poql_to_nraenv of nraenv_path *)
(* and nraenv_path = *)
(*   | Pnraenv_no_optim of nraenv_stat_body *)
(*   | Pnraenv_optim of nraenv_stat_body *)

(**s Parse json *)

let list_assoc x l =
  begin try
    List.assoc x l
  with Not_found ->
    Format.eprintf "Unbound field %s@." x;
    raise Not_found
  end

let string_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `String s -> s
  | _ -> failwith ("string_of_json: "^(Yojson.Safe.to_string j))
  end

let int_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Int n -> n
  | _ -> failwith ("int_of_json: "^(Yojson.Safe.to_string j))
  end

let nnrc_stat_body_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { nnrc_size = int_of_json (list_assoc "nnrc_size" fields); }
      with Not_found -> failwith ("nnrc_stat_body_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("nnrc_stat_body_of_json: "^(Yojson.Safe.to_string j))
  end

let nnrc_stat_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { nnrc_no_optim = nnrc_stat_body_of_json (list_assoc "nnrc_no_optim" fields);
          nnrc_optim = nnrc_stat_body_of_json (list_assoc "nnrc_optim" fields); }
      with Not_found -> failwith ("nnrc_stat_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("nnrc_stat_of_json: "^(Yojson.Safe.to_string j))
  end

let nra_stat_body_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { nra_size = int_of_json (list_assoc "nra_size" fields);
          nra_depth = int_of_json (list_assoc "nra_depth" fields);
          nra_to_nnrc = nnrc_stat_of_json (list_assoc "nra_to_nnrc" fields) }
      with Not_found -> failwith ("nra_stat_body_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("nra_stat_body_of_json: "^(Yojson.Safe.to_string j))
  end

let nra_stat_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { nra_no_optim = nra_stat_body_of_json (list_assoc "nra_no_optim" fields);
          nra_optim = nra_stat_body_of_json (list_assoc "nra_optim" fields); }
      with Not_found -> failwith ("nra_stat_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("nra_stat_of_json: "^(Yojson.Safe.to_string j))
  end

let nraenv_stat_body_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { nraenv_size = int_of_json (list_assoc "nraenv_size" fields);
          nraenv_depth = int_of_json (list_assoc "nraenv_depth" fields);
          nraenv_to_nnrc = nnrc_stat_of_json (list_assoc "nraenv_to_nnrc" fields);
          nraenv_to_nra = nra_stat_of_json (list_assoc "nraenv_to_nra" fields); }
      with Not_found -> failwith ("nraenv_stat_body_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("nraenv_stat_body_of_json: "^(Yojson.Safe.to_string j))
  end

let nraenv_stat_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { nraenv_no_optim = nraenv_stat_body_of_json (list_assoc "nraenv_no_optim" fields);
          nraenv_optim = nraenv_stat_body_of_json (list_assoc "nraenv_optim" fields); }
      with Not_found -> failwith ("nraenv_stat_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("nraenv_stat_of_json: "^(Yojson.Safe.to_string j))
  end

let camp_stat_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { camp_size = int_of_json (list_assoc "camp_size" fields);
          camp_to_nraenv = nraenv_stat_of_json (list_assoc "camp_to_nraenv" fields);
          camp_to_nra = nra_stat_of_json (list_assoc "camp_to_nra" fields); }
      with Not_found -> failwith ("camp_stat_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("camp_stat_of_json: "^(Yojson.Safe.to_string j))
  end

let rule_stat_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { rule_size = int_of_json (list_assoc "rule_size" fields);
          rule_to_nraenv = nraenv_stat_of_json (list_assoc "rule_to_nraenv" fields);
          rule_to_nra = nra_stat_of_json (list_assoc "rule_to_nra" fields); }
      with Not_found -> failwith ("ruel_stat_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("rule_stat_of_json: "^(Yojson.Safe.to_string j))
  end

let oql_stat_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        { oql_size = int_of_json (list_assoc "oql_size" fields);
          oql_to_nraenv = nraenv_stat_of_json (list_assoc "oql_to_nraenv" fields); }
      with Not_found -> failwith ("nraenv_stat_of_json: "^(Yojson.Safe.to_string j))
      end
  | _ -> failwith ("oql_stat_of_json: "^(Yojson.Safe.to_string j))
  end


let stat_of_json (j: Yojson.Safe.json) =
  begin match j with
  | `Assoc fields ->
      begin try
        Stat_rule (string_of_json (list_assoc "name" fields), rule_stat_of_json (list_assoc "stats" fields))
      with _ ->
        begin try
          Stat_camp (string_of_json (list_assoc "name" fields), camp_stat_of_json (list_assoc "stats" fields))
        with _ ->
          Stat_oql (string_of_json (list_assoc "name" fields), oql_stat_of_json (list_assoc "stats" fields))
        end
      end
  | _ -> failwith ("stat_of_json: "^(Yojson.Safe.to_string j))
  end

let stat_from_file f =
  stat_of_json (Yojson.Safe.from_file f)

(**s Check properties *)

let check_nnrc_stat ff prefix s =
  if s.nnrc_no_optim.nnrc_size < s.nnrc_optim.nnrc_size then
    Format.fprintf ff "%s: nnrc_size < nnrc_optim_size (%d < %d)@."
      prefix
      s.nnrc_no_optim.nnrc_size s.nnrc_optim.nnrc_size

let check_nra_stat_body ff prefix s =
  check_nnrc_stat ff (prefix^"->NNRC") s.nra_to_nnrc

let check_nra_stat ff prefix s =
  if s.nra_no_optim.nra_size < s.nra_optim.nra_size then
    Format.fprintf ff "%s: nra_no_optim.nra_size < nra_optim.nra_size (%d < %d)@."
      prefix
      s.nra_no_optim.nra_size s.nra_optim.nra_size;
  if s.nra_no_optim.nra_depth < s.nra_optim.nra_depth then
    Format.fprintf ff "%s: nra_no_optim.nra_depth < nra_optim.nra_depth (%d < %d)@."
      prefix
      s.nra_no_optim.nra_depth s.nra_optim.nra_depth;
  check_nra_stat_body ff prefix s.nra_no_optim;
  check_nra_stat_body ff (prefix^"->optim") s.nra_optim

let check_nraenv_stat_body ff prefix s =
  check_nnrc_stat ff (prefix^"->NNRC") s.nraenv_to_nnrc;
  check_nra_stat ff (prefix^"->NRA") s.nraenv_to_nra

let check_nraenv_stat ff prefix s =
  if s.nraenv_no_optim.nraenv_size < s.nraenv_optim.nraenv_size then
    Format.fprintf ff "%s: nraenv_no_optim.nraenv_size < nraenv_optim.nraenv_size (%d < %d)@."
      prefix
      s.nraenv_no_optim.nraenv_size s.nraenv_optim.nraenv_size;
  if s.nraenv_no_optim.nraenv_depth < s.nraenv_optim.nraenv_depth then
    Format.fprintf ff "%s: nraenv_no_optim.nraenv_depth < nraenv_optim.nraenv_depth (%d < %d)@."
      prefix
      s.nraenv_no_optim.nraenv_depth s.nraenv_optim.nraenv_depth;
  check_nraenv_stat_body ff prefix s.nraenv_no_optim;
  check_nraenv_stat_body ff (prefix^"->optim") s.nraenv_optim

let check_camp ff prefix s =
  check_nraenv_stat ff (prefix^"->NRAEnv") s.camp_to_nraenv;
  check_nra_stat ff (prefix^"->NRA") s.camp_to_nra

let check_rule ff prefix s =
  check_nraenv_stat ff (prefix^"->NRAEnv") s.rule_to_nraenv;
  check_nra_stat ff (prefix^"->NRA") s.rule_to_nra

let check_oql ff prefix s =
  check_nraenv_stat ff (prefix^"->NRAEnv") s.oql_to_nraenv

let check_stat ff s =
  match s with
  | Stat_rule (name, s) -> check_rule ff (name^".rule") s
  | Stat_camp (name, s) -> check_camp ff (name^".camp") s
  | Stat_oql (name, s) -> check_oql ff (name^".oql") s


(**s main *)

let main () =
  for i = 1 to Array.length Sys.argv - 1 do
    let stat = stat_from_file Sys.argv.(i) in
    Format.printf "%a@." check_stat stat
  done

let () =
  main ()
