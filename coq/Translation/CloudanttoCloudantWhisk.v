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

Require Import List.
Require Import String.
Require Import Utils.
Require Import BasicRuntime.
Require Import ForeignToJavaScript.
Require Import ForeignCloudant.
Require Import CloudantRuntime.
Require Import CloudantWhiskRuntime.

Local Open Scope string_scope.

Section CloudanttoCloudantWhisk.

  Context {fruntime:foreign_runtime}.
  Context {ftojavascript:foreign_to_javascript}.
  Context {fcloudant:foreign_cloudant}.

  Definition cloudant_design_to_view_action
             (action_name:string)
             (design:cloudant_design) : whisk_action :=
    let design_inputdb := cloudant_design_inputdb design in
    let design_name := cloudant_design_name design in
    let design_doc := cloudant_design_doc design in
    let action_name := action_name ++ "_view_" ++ design_name in
    (action_name,"// VIEW ACTION TO BE DONE").
  
  Definition cloudant_design_to_compute_action
             (action_name:string)
             (final_expr:string)
             (effective_parameters:list string) : whisk_action :=
    let action_name := action_name ++ "_compute" in
    (action_name,"// COMPUTE ACTION TO BE DONE").

 
  Definition cloudant_to_cloudant_whisk (action_name:string) (q:cloudant) : cloudant_whisk :=
    (cloudant_design_to_compute_action
       action_name
       (cloudant_final_expr q)
       (cloudant_effective_parameters q))
      :: (map (cloudant_design_to_view_action action_name)
              (cloudant_designs q)).

End CloudanttoCloudantWhisk.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
