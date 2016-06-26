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

Require Import CompilerRuntime.
Module CompOQL(runtime:CompilerRuntime).
  Require String.
  Require CompData CompOperators.
  Require OQL OQLSugar.

  Module Data := CompData.CompData runtime.
  Module Ops := CompOperators.CompOperators runtime.

  Definition expr : Set
    := OQL.oql_expr.
  Definition t : Set
    := expr.
  Definition var : Set
    := String.string.
  
  Definition select_expr : Set
    := OQL.oql_select_expr.
  Definition in_expr : Set
    := OQL.oql_in_expr.
  Definition where_expr : Set
    := OQL.oql_where_expr.
  
  Definition ovar : var -> expr
    := OQL.OVar.
  Definition oconst : Data.data -> expr
    := OQL.OConst.
  Definition otable  : String.string -> expr
    := OQL.OTable.
  Definition obinop : Ops.Binary.op -> expr ->expr -> expr 
    := OQL.OBinop.
  Definition ounop : Ops.Unary.op -> expr -> expr 
    := OQL.OUnop.
  Definition osfw : select_expr -> list in_expr -> where_expr -> expr 
    := OQL.OSFW.
  Definition oselect : expr -> select_expr 
    := OQL.OSelect.
  Definition oselectdistinct : expr -> select_expr 
    := OQL.OSelectDistinct.
  Definition oin : String.string -> expr -> in_expr 
    := OQL.OIn.
  Definition otrue : where_expr 
    := OQL.OTrue.
  Definition owhere : expr -> where_expr 
    := OQL.OWhere.
  
  Definition odot : String.string -> expr -> expr 
    := OQLSugar.ODot.
  Definition oarrow : String.string -> expr -> expr 
    := OQLSugar.OArrow.
  Definition ostruct : list (String.string * expr) -> expr 
    := OQLSugar.OStruct.

  Definition tableify : expr -> expr
    := OQLSugar.tableify.

End CompOQL.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
