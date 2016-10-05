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
Module QSQL(runtime:CompilerRuntime).
  Require String.
  Require QData QOperators.
  Require SQL.

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.

  Definition expr : Set
    := SQL.sql_expr.
  Definition t : Set
    := expr.
  Definition var : Set
    := String.string.
  
  Definition select_expr : Set
    := SQL.sql_select_expr.
  Definition in_expr : Set
    := SQL.sql_in_expr.
  Definition where_expr : Set
    := SQL.sql_where_expr.
  Definition order_by_expr : Set
    := SQL.sql_order_by_expr.
  
  Definition ovar : var -> expr
    := SQL.OVar.
  Definition oconst : Data.data -> expr
    := SQL.OConst.
  Definition otable  : String.string -> expr
    := SQL.OTable.
  Definition obinop : Ops.Binary.op -> expr ->expr -> expr 
    := SQL.OBinop.
  Definition ounop : Ops.Unary.op -> expr -> expr 
    := SQL.OUnop.
  Definition osfw : select_expr -> list in_expr -> where_expr -> order_by_expr -> expr 
    := SQL.OSFW.
  Definition oselect : expr -> select_expr 
    := SQL.OSelect.
  Definition oselectdistinct : expr -> select_expr 
    := SQL.OSelectDistinct.
  Definition oin : String.string -> expr -> in_expr 
    := SQL.OIn.
  Definition oincast : String.string -> String.string -> expr -> in_expr 
    := SQL.OInCast.
  Definition otrue : where_expr 
    := SQL.OTrue.
  Definition owhere : expr -> where_expr 
    := SQL.OWhere.
  Definition onoorder : order_by_expr 
    := SQL.ONoOrder.
  Definition oorder_by : expr -> RUnaryOps.SortDesc -> order_by_expr 
    := SQL.OOrderBy.
  
  Definition odot : String.string -> expr -> expr 
    := SQLSugar.ODot.
  Definition oarrow : String.string -> expr -> expr 
    := SQLSugar.OArrow.
  Definition ostruct : list (String.string * expr) -> expr 
    := SQLSugar.OStruct.

  Definition tableify : expr -> expr
    := SQLSugar.tableify.

End QSQL.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
