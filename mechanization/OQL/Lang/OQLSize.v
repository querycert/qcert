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
Require Import CommonRuntime.
Require Import OQL.

Section OQLSize.
  Context {fruntime:foreign_runtime}.

  Fixpoint oql_expr_size (e:oql_expr) : nat 
    := match e with
         | OConst d => 1
         | OVar v => 1
         | OTable v => 1
         | OBinop op n₁ n₂ => S (oql_expr_size n₁ + oql_expr_size n₂)
         | OUnop op n₁ => S (oql_expr_size n₁)
         | OSFW se el we oe =>
           let from_size :=
               fold_left (fun x => fun e => x+oql_in_size e) el 0
           in
           S (oql_select_size se + from_size + oql_where_size we + oql_order_size oe)
       end
  with oql_select_size (se:oql_select_expr) :=
    match se with
    | OSelect e => oql_expr_size e
    | OSelectDistinct e => oql_expr_size e
    end
  with oql_in_size (ie:oql_in_expr) :=
    match ie with
    | OIn v e => oql_expr_size e
    | OInCast v brand_names e => oql_expr_size e
    end
  with oql_where_size (we:oql_where_expr) :=
    match we with
    | OTrue => 0
    | OWhere e => oql_expr_size e
    end
  with oql_order_size (oe:oql_order_by_expr) :=
    match oe with
    | ONoOrder => 0
    | OOrderBy e _ => oql_expr_size e
    end.

  Fixpoint oql_query_program_size (oq:oql_query_program) : nat
    := match oq with
      | ODefineQuery s e rest => S (oql_expr_size e + oql_query_program_size rest)
      | OUndefineQuery s rest => S (oql_query_program_size rest)
      | OQuery e => S (oql_expr_size e)
      end.

  Definition oql_size (q:oql) : nat
    := oql_query_program_size q.
  
End OQLSize.

