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
   utility.  The utility converts SQL source to * an s-expression form of
   SQL that can be consumed by the next phase.
*)

open Util

let get_qcert_home () =
  try Sys.getenv "QCERT_HOME"
  with Not_found -> StaticConfig.qcert_home

let main (s : string) =
  begin try
    let cmd =
      Format.sprintf "java -jar %s/bin/sqlparser.jar -single" (get_qcert_home ())
    in
    let fromProcess, toProcess = Unix.open_process cmd in
    output_string toProcess s;
    close_out toProcess;
    let result = input_line fromProcess in
    close_in fromProcess;
    result
  with exn ->
    raise (Qcert_Error ("SQL parser: "^(Printexc.to_string exn)))
  end
