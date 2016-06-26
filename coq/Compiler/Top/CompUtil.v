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

Section CompUtil.

  Require Import String List String EquivDec.
  
  Require Import BasicRuntime.
  Require Import Pattern Rule.

  (*********
   * Utils *
   *********)

  (* Initial variables for the input and environment *)
  (* Java equivalents: in NnrcToNrcmr as static fields *)
  Definition init_vid := "id"%string.
  Definition init_venv := "env"%string.
  Definition init_vinit := "init"%string.

  Require Import LData.
  
  (* Java equivalent: NnrcToNrcmr.localize_names *)
  Definition localize_names (names: list string) : list (string * localization) :=
    map (fun x => (x, Vdistributed)) names.

  Definition localize_bindings {A} (cenv: list (string * A)) : list (string * localization) :=
    localize_names (map fst cenv).

  Context {fdata:foreign_data}.
  
  Definition unwrap_result res :=
    match res with
    | None => None
    | Some (dcoll l) => Some l
    | Some _ => None
    end.

  Require Import DData.
  Definition mkDistLoc : list (string*dlocalization)
    := ("CONST$WORLD"%string, Vdistr)::nil.

End CompUtil.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
