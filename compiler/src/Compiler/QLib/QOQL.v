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
Require String.
Require QData.
Require QOperators.
Require OQL.
Require OQLSugar.

Module QOQL(runtime:CompilerRuntime).

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.

  Definition expr : Set
    := OQL.oql_expr.
  Definition program : Set
    := OQL.oql.
  Definition t : Set
    := program.
  Definition var : Set
    := String.string.
  
  Definition select_expr : Set
    := OQL.oql_select_expr.
  Definition in_expr : Set
    := OQL.oql_in_expr.
  Definition where_expr : Set
    := OQL.oql_where_expr.
  Definition order_by_expr : Set
    := OQL.oql_order_by_expr.
  
  Definition ovar : var -> expr
    := OQL.OVar.
  Definition oconst : Data.qdata -> expr
    := OQL.OConst.
  Definition otable  : String.string -> expr
    := OQL.OTable.
  Definition obinop : Ops.Binary.op -> expr ->expr -> expr 
    := OQL.OBinop.
  Definition ounop : Ops.Unary.op -> expr -> expr 
    := OQL.OUnop.
  Definition osfw : select_expr -> list in_expr -> where_expr -> order_by_expr -> expr 
    := OQL.OSFW.
  Definition oselect : expr -> select_expr 
    := OQL.OSelect.
  Definition oselectdistinct : expr -> select_expr 
    := OQL.OSelectDistinct.
  Definition oin : String.string -> expr -> in_expr 
    := OQL.OIn.
  Definition oincast : String.string -> String.string -> expr -> in_expr 
    := OQL.OInCast.
  Definition otrue : where_expr 
    := OQL.OTrue.
  Definition owhere : expr -> where_expr 
    := OQL.OWhere.
  Definition onoorder : order_by_expr 
    := OQL.ONoOrder.
  Definition oorder_by : expr -> DataSort.SortDesc -> order_by_expr 
    := OQL.OOrderBy.
  
  Definition odot : String.string -> expr -> expr 
    := OQLSugar.ODot.
  Definition oarrow : String.string -> expr -> expr 
    := OQLSugar.OArrow.
  Definition ostruct : list (String.string * expr) -> expr 
    := OQLSugar.OStruct.
  Definition onew : String.string -> list (String.string * expr) -> expr 
    := OQLSugar.ONew.

  Definition tableify : expr -> expr
    := OQLSugar.tableify.

  Definition define : String.string -> expr -> program -> program
    := OQL.ODefineQuery.

  Definition undefine : String.string -> program -> program
    := OQL.OUndefineQuery.

  Definition query : expr -> program
    := OQL.OQuery.
  
End QOQL.

