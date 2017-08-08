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

Section DConstants.

  Require Import String.
  Require Import List.
  Require Import EquivDec.
  Require Import RList RLift RAssoc.
  Require Import RData DData RRelation.

  Require Import RConstants.
  
  Local Open Scope string.

  Require Import ForeignData.

  Context {fdata:foreign_data}.

  (* Java equivalent: NnrcToNrcmr.localize_names *)
  Definition mkDistNames (names: list string) : list (string * dlocalization) :=
    map (fun x => (x, Vdistr)) names.

  Definition mkDistLocs {A} (cenv: list (string * A)) : list (string * dlocalization) :=
    mkDistNames (map fst cenv).

  Definition mkDistConstant (loc:dlocalization) (d:data) :=
    match loc with
    | Vlocal => Some (Dlocal d)
    | Vdistributed =>
      match d with
      | dcoll coll => Some (Ddistr coll)
      | _ => None
      end
    end.
  
  Definition mkDistConstants
             (vars_loc: list (string * dlocalization)) (env: list (string*data))
    : option (list (string*ddata)) :=
    let one (x_loc: string * dlocalization) :=
        let (x, loc) := x_loc in
        olift (fun d => lift (fun dd => (x, dd)) (mkDistConstant loc d))
              (lookup equiv_dec env x)
    in
    rmap one vars_loc.

  Section World.
    (* Declares single *distributed* input collection containing world *)
    Definition mkDistWorld (world:list data) : list (string*ddata)
      := (WORLD, Ddistr world)::nil.

    (* Declares single *distributed* input collection containing world *)
    Definition mkDistLoc : list (string*dlocalization)
      := (WORLD, Vdistr)::nil.
  End World.

  Definition unlocalize_constants (env:list (string*ddata)) : list (string*data) :=
    map (fun xy => (fst xy, unlocalize_data (snd xy))) env.

  Lemma unlocalize_constants_cons v d (denv:dbindings) :
    unlocalize_constants ((v,Dlocal d) :: denv) = (v,d) :: unlocalize_constants denv.
  Proof.
    reflexivity.
  Qed.

End DConstants.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)

