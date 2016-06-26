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

module Ocamlbuild_compat = struct
  let mark_tag_used = ignore
  include Ocamlbuild_plugin
end

let mark_tags () =
  let open Ocamlbuild_compat in
  pdep ["java-package"] "java-package" (fun param -> [param]);
  mark_tag_used "java-package(org.qcert.calib)";
  mark_tag_used "java-package(org.qcert.caco)";
  mark_tag_used "java-package(org.qcert.caev)";
  mark_tag_used "java-package(org.qcert.cada)";
  mark_tag_used "java-package(org.qcert.calib)"

let _ =
  mark_tags ()
