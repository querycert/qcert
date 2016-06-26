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

Section OQLSize.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import OQL.

  Context {fruntime:foreign_runtime}.

  Fixpoint oql_size (e:oql_expr) : nat 
    := match e with
         | OConst d => 1
         | OVar v => 1
         | OTable v => 1
         | OBinop op n₁ n₂ => S (oql_size n₁ + oql_size n₂)
         | OUnop op n₁ => S (oql_size n₁)
         | OSFW se el we =>
           let from_size :=
               fold_left (fun x => fun e => x+oql_in_size e) el 0
           in
           S (oql_select_size se + from_size + oql_where_size we)
       end
  with oql_select_size (se:oql_select_expr) :=
    match se with
    | OSelect e => oql_size e
    | OSelectDistinct e => oql_size e
    end
  with oql_in_size (ie:oql_in_expr) :=
    match ie with
    | OIn v e => oql_size e
    end
  with oql_where_size (we:oql_where_expr) :=
    match we with
    | OTrue => 0
    | OWhere e => oql_size e
    end.
  
End OQLSize.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
