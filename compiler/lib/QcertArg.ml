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

open QcertUtils.Util
open QcertUtil
open QcertConfig

let set_qname gconf s = gconf.gconf_qname <- Some s
let set_source gconf s = gconf.gconf_source <- language_of_name s
let set_target gconf s = gconf.gconf_target <- language_of_name s
let add_path gconf s = gconf.gconf_path <- gconf.gconf_path @ [ language_of_name s ]
let set_exact_path gconf () = gconf.gconf_exact_path <- true
let set_dir gconf s = gconf.gconf_dir <- Some s
let set_dir_target gconf s = gconf.gconf_dir_target <- Some s
let set_schema_content gconf file_content =
  begin match gconf.gconf_io with
  | None -> gconf.gconf_io <- Some (IO_components (None,None,Some file_content))
  | Some (IO_components (c1,c2,c3)) -> gconf.gconf_io <- Some (IO_components (c1,c2,Some file_content))
  | Some (IO_file _) -> raise (Qcert_Error "Should not use -io with -schema/-input/-output")
  end
let set_input_content gconf file_content =
  begin match gconf.gconf_io with
  | None -> gconf.gconf_io <- Some (IO_components (Some file_content,None,None))
  | Some (IO_components (c1,c2,c3)) -> gconf.gconf_io <- Some (IO_components (Some file_content,c2,c3))
  | Some (IO_file _) -> raise (Qcert_Error "Should not use -io with -schema/-input/-output")
  end
let set_output_content gconf file_content =
  begin match gconf.gconf_io with
  | None -> gconf.gconf_io <- Some (IO_components (None,Some file_content,None))
  | Some (IO_components (c1,c2,c3)) -> gconf.gconf_io <- Some (IO_components (c1,Some file_content,c3))
  | Some (IO_file _) -> raise (Qcert_Error "Should not use -io with -schema/-input/-output")
  end
let set_schema_file gconf file_name =
  set_schema_content gconf (string_of_file file_name)
let set_input_file gconf file_name =
  set_input_content gconf (string_of_file file_name)
let set_output_file gconf file_name =
  set_output_content gconf (string_of_file file_name)
let set_io_file gconf file_name =
  begin match gconf.gconf_io with
  | None -> gconf.gconf_io <- Some (IO_file (Some file_name))
  | Some (IO_file f) -> gconf.gconf_io <- Some (IO_file (Some (string_of_file file_name)))
  | Some (IO_components _) -> raise (Qcert_Error "Should not use -io with -schema/-input/-output")
  end
let set_emit_all gconf () = gconf.gconf_emit_all <- true
let set_emit_sexp gconf () = gconf.gconf_emit_sexp <- true
let set_emit_sexp_all gconf () = gconf.gconf_emit_sexp_all <- true
let set_eval gconf () = gconf.gconf_eval <- true
let set_eval_all gconf () = gconf.gconf_eval_all <- true
let set_eval_debug gconf () = gconf.gconf_eval_debug <- true
let set_eval_validate gconf () = gconf.gconf_eval_validate <- true
let set_source_sexp gconf () = gconf.gconf_source_sexp <- true
let set_java_imports gconf s = gconf.gconf_java_imports <- s
let set_vinit gconf x = gconf.gconf_mr_vinit <- x
let set_stat gconf () = gconf.gconf_stat <- true
let set_stat_all gconf () = gconf.gconf_stat_all <- true
let set_stat_tree gconf () = gconf.gconf_stat_tree <- true
let set_optim_config_file gconf file = gconf.gconf_optim_config_file <- Some file
let set_emit_optim_config gconf () = gconf.gconf_emit_optim_config <- true
let set_optims gconf optims = gconf.gconf_optim_config <- optims

let set_link_js_runtime gconf () = PrettyCommon.set_link_js_runtime gconf.gconf_pretty_config ()
let set_prefix gconf prefix = gconf.gconf_prefix <- prefix

