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

Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.

Section LambdaNRASugar.

  Require Import Utils BasicSystem.
  Require Import LambdaNRA.

  Context {fruntime:foreign_runtime}.

  Definition LNRAStruct (el:list (string * lnra)) :=
    match el with
    | nil => LNRAConst (drec nil)
    | (s0,x) :: rest =>
      let init_rec := LNRAUnop (ARec s0) x in
      let proc_one (e:string * lnra) acc :=
          LNRABinop AConcat (LNRAUnop (ARec (fst e)) (snd e)) acc
      in
      fold_right proc_one init_rec rest
    end.

  Definition LNRADot (s:string) (e:lnra) := LNRAUnop (ADot s) e.
  Definition LNRAArrow (s:string) (e:lnra) := LNRAUnop (ADot s) (LNRAUnop AUnbrand e).
  
  (* replaces free variables by table lookups -- used in parser *)
  Definition la_tableify_one_var (e:lnra) (v:string) : lnra :=
    lnra_subst e v (LNRATable v).

  Definition la_tableify (e:lnra) : lnra :=
    let free_vars := lnra_free_vars e in
    fold_left la_tableify_one_var free_vars e.
  
End LambdaNRASugar.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
