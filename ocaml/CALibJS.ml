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

(* This is main for the JS variant of the Camp Library *)

open CALib


let _ =
  let camp_to_js = Js.wrap_callback (fun s -> Js.string (compile_nraenv_to_js (camp_to_nraenv (Js.to_string s)))) in
  let open Js.Unsafe in
  global##calibjs <-
    obj [|("camp_to_js", inject camp_to_js);|];

