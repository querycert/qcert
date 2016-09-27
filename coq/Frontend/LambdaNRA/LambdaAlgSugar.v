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

Section LambdaAlgSugar.

  Require Import Utils BasicSystem.
  Require Import LambdaAlg.

  Context {fruntime:foreign_runtime}.

  Definition LAStruct (el:list (string * lalg)) :=
    match el with
    | nil => LAConst (drec nil)
    | (s0,x) :: rest =>
      let init_rec := LAUnop (ARec s0) x in
      let proc_one (e:string * lalg) acc :=
          LABinop AConcat (LAUnop (ARec (fst e)) (snd e)) acc
      in
      fold_right proc_one init_rec rest
    end.

  Definition LADot (s:string) (e:lalg) := LAUnop (ADot s) e.
  Definition LAArrow (s:string) (e:lalg) := LAUnop (ADot s) (LAUnop AUnbrand e).
  
  (* replaces free variables by table lookups -- used in parser *)
  Definition la_tableify_one_var (e:lalg) (v:string) : lalg :=
    lalg_subst e v (LATable v).

  Definition la_tableify (e:lalg) : lalg :=
    let free_vars := lalg_free_vars e in
    fold_left la_tableify_one_var free_vars e.
  
End LambdaAlgSugar.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
