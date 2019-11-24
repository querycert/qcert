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
Require Import Utils.
Require Import CommonSystem.
Require Import OQL.

Section OQLSugar.
  Context {fruntime:foreign_runtime}.

  Definition OStruct (el:list (string * oql_expr)) :=
    match el with
    | nil => OConst (drec nil)
    | (s0,x) :: rest =>
      let init_rec := OUnop (OpRec s0) x in
      let proc_one (e:string * oql_expr) acc :=
          OBinop OpRecConcat (OUnop (OpRec (fst e)) (snd e)) acc
      in
      fold_right proc_one init_rec rest
    end.

  Definition ONew (class:string) (el:list (string * oql_expr)) :=
    OUnop (OpBrand (class::nil)) (OStruct el).
  
  Definition ODot (s:string) (e:oql_expr) := OUnop (OpDot s) e.
  Definition OArrow (s:string) (e:oql_expr) := OUnop (OpDot s) (OUnop OpUnbrand e).
  
  (* replaces free variables by table lookups -- used in parser *)
  Definition tableify_one_var (e:oql_expr) (v:string) : oql_expr :=
    oql_subst e v (OTable v).

  Definition tableify (e:oql_expr) : oql_expr :=
    let free_vars := oql_free_vars e in
    fold_left tableify_one_var free_vars e.
  
End OQLSugar.

