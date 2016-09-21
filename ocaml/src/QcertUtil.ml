(*
 * Copyright 2015-2016 IBM Corporation
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

open Util
open Compiler.EnhancedCompiler

let language_of_name name =
  let name =
    char_list_of_string (String.lowercase name)
  in
  begin match CompDriver.language_of_name_case_sensitive name with
  | CompDriver.L_error err -> raise (CACo_Error ("Unknown language: "^(string err)))
  | lang -> lang
  end

let name_of_language lang =
  let name = CompDriver.name_of_language lang in
  string name


let name_of_query (q: CompDriver.query) =
  let name = CompDriver.name_of_query (RType.empty_brand_model ()) q in
  string name

let driver_no_error dv =
  begin match dv with
  | CompDriver.Dv_error err -> raise (CACo_Error (string err))
  | _ -> ()
  end

let language_no_error lang =
  begin match lang with
  | CompDriver.L_error err -> raise (CACo_Error (string err))
  | _ -> ()
  end

let query_no_error q =
  begin match q with
  | CompDriver.Q_error err -> raise (CACo_Error (string err))
  | _ -> ()
  end
