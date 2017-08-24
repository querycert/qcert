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

(** Cloudant is a representation for the emitted cloudant code. It is
composed of a list of Cloudant design documents, a final expression,
and a list of effective
parameters.
- The list of Cloudant design document describes map-reduce views evaluated on the server side. Those design documents are in JSON serialized form.
- The final expression is used to compute the final result from the output of the views, and evaluated on the client side.
- The list of effective parameters are the names of the databases where the result of the views are stored
*)

(** Summary:
- Language: CloudantWhisk (Emitted code for Cloudant deployed on openWhisk)
- Based on: Cloudant openWhisk documentation
- URL: https://console.ng.bluemix.net/docs/services/Cloudant/api/creating_views.html#views-mapreduce-
- URL: http://openwhisk.incubator.apache.org
- Languages translating to CloudantWhisk: Cloudant
- Languages translating from CloudantWhisk: 
*)

Require Import JavaScript.

Section CloudantWhisk.
  Require Import String.

  (** The underlying structure for Cloudant targetting openWhisk is a set of actions containing JavaScript.

      The actions fall into two classes:
- Actions which deploy a Cloudant view
- The action which compute the final result from the views *)

  Definition whisk_action_name := string.
  Definition whisk_action_code := javascript.

  Definition whisk_action : Set := whisk_action_name * whisk_action_code.

  Definition cloudant_whisk : Set := list whisk_action.
  
End CloudantWhisk.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
