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

Section Cloudant.
  Require Import String.

  Record cloudant_design := mkCloudantDesign
                              { cloudant_design_inputdb : string;
                                cloudant_design_doc : string; }.
  
  Record cloudant := mkCloudant
                       { cloudant_designs: list cloudant_design;
                         cloudant_final_expr : string;
                         cloudant_effective_parameters : list string; }.
  
End Cloudant.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
