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

Section TOQL.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicSystem.

  Require Import OQL.
  
  (** Typing for CAMP *)

  Section typ.
  
    Context {m:basic_model}.
    Hint Resolve bindings_type_has_type.

    Inductive oql_expr_type : tbindings -> oql_expr -> rtype -> Prop :=
    | OTConst {τ} tenv c :
        data_type (normalize_data brand_relation_brands c) τ ->
        oql_expr_type tenv (OConst c) τ
    | OTVar {τ} tenv v :
        lookup equiv_dec tenv v = Some τ -> oql_expr_type tenv (OVar v) τ
    .

  
End TOQL.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
