(*
 * Copyright 2016 Joshua Auerbach
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(* This module contains process management to invoke a separate Java
   utility.  The utility has an expandable set of functions, such as
	 converting SQL source to an s-expression form of SQL that can be consumed by the next phase.
	 Also, parsing JRules, converting SQL schemas to JSON, and data loading using Apache commons-csv.
*)

open QcertExtracted
open Util

let get_qcert_home () =
  try Sys.getenv "QCERT_HOME"
  with Not_found -> StaticConfig.qcert_home

let main (verb: string) (s: string) =
	(*
	Format.printf "Input for verb %s: %s" verb s;
	Format.print_newline ();
	*)
  begin try
    let cmd =
      Format.sprintf "java -jar %s/bin/javaService.jar %s" (get_qcert_home ()) verb
    in
    let fromProcess, toProcess = Unix.open_process cmd in
    output_string toProcess s;
    close_out toProcess;
    let result = input_line fromProcess in
    close_in fromProcess;
  	(*
		Format.printf "Output for verb %s: %s" verb result;
		Format.print_newline ();
		*)
    result
  with exn ->
    raise (Qcert_Error ("Java Service: "^(Printexc.to_string exn)))
  end
