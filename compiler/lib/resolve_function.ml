open Util
open EnhancedCompiler.EnhancedCompiler

let static_int unwrap_const e =
  begin match unwrap_const e with
  | Some (Data.Coq_dnat i) -> i
  | _ -> raise Not_found
  end

let static_string unwrap_const e =
  begin match unwrap_const e with
  | Some (Data.Coq_dstring s) -> s
  | _ -> raise Not_found
  end

let resolve_call unary_wrap binary_wrap unwrap_const fname el =
  begin match fname,el with
  (* Built-in unary *)
  | "not", [e] ->
	    unary_wrap QOps.Unary.opneg e
  | "flatten", [e] ->
	    unary_wrap QOps.Unary.opflatten e
  | "count", [e] ->
	    unary_wrap QOps.Unary.opcount e
  | "toString", [e] ->
	    unary_wrap QOps.Unary.optostring e
  | "length", [e] ->
	    unary_wrap QOps.Unary.oplength e
  | "substring", [e1;e2] ->
	    let start =
	      begin try static_int unwrap_const e2 with
	      | Not_found ->
	          raise (Qcert_Error
		                 ("Second parameter of substring should be an integer constant"))
	      end
	    in
	    unary_wrap (QOps.Unary.opsubstring start None) e1
  | "substring", [e1;e2;e3] ->
	    let start =
	      begin try static_int unwrap_const e2 with
	      | Not_found ->
	          raise (Qcert_Error
		                 ("Second parameter of substring should be an integer constant"))
	      end
	    in
	    let len =
	      begin try static_int unwrap_const e3 with
	      | Not_found ->
	          raise (Qcert_Error
		                 ("Third parameter of substring should be an integer constant"))
	      end
	    in
	    unary_wrap (QOps.Unary.opsubstring start (Some len)) e1
  | "like", [e1;e2] ->
	    let pat =
	      begin try static_string unwrap_const e1 with
	      | Not_found ->
	          raise (Qcert_Error
		                 ("First parameter of like should be a string constant"))
	      end
	    in
	    unary_wrap (QOps.Unary.oplike pat) e2
  | "sum", [e] ->
	    unary_wrap QOps.Unary.opnatsum e
  | "min", [e] ->
	    unary_wrap QOps.Unary.opnatmin e
  | "max", [e] ->
	    unary_wrap QOps.Unary.opnatmax e
  | "avg", [e] ->
	    unary_wrap QOps.Unary.opnatmean e
  | "fsum", [e] ->
	    unary_wrap QOps.Unary.opfloatsum e
  | "favg", [e] ->
	    unary_wrap QOps.Unary.opfloatmean e
  | "fmin", [e] ->
	    unary_wrap QOps.Unary.opfloatmin e
  | "fmax", [e] ->
	    unary_wrap QOps.Unary.opfloatmax e
  (* Built-in binary *)
  | "nth", [e1;e2] ->
	    binary_wrap QOps.Binary.opbagnth e1 e2
  | "stringJoin", [e1;e2] ->
	    binary_wrap QOps.Binary.opstringjoin e1 e2
  (* Foreign *)
  | "date", [e] ->
      unary_wrap Enhanced.Ops.Unary.sql_date_from_string e
  | "getYear", [e] ->
      unary_wrap (Enhanced.Ops.Unary.sql_date_get_component Coq_sql_date_YEAR) e
  | "encode", [e] ->
      unary_wrap Enhanced.Ops.Unary.uri_encode e
  | "decode", [e] ->
      unary_wrap Enhanced.Ops.Unary.uri_decode e
  | _, _ ->
	    raise (Qcert_Error
		           ("Function " ^ fname ^ " with arity " ^ (string_of_int (List.length el)) ^ " unkonwn"))
  end
