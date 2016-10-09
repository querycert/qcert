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

Section RWorld.

  Require Import String.
  Require Import RData.
  
  Local Open Scope string.

  Require Import ForeignData.

  Context {fdata:foreign_data}.

  Definition mkWorld (world:list data) : list (string*data)
    := ("WORLD",(dcoll world))::nil.

  (* Used in CLDMR load - JS *)
  Definition mkWorldColl (world:list data) : list (string*list data)
    := ("WORLD",world)::nil.

End RWorld.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
