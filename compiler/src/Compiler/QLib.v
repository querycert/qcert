(*
 * Copyright 2015-2017 IBM Corporation
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
Require QData QOperators.
Require QOQL QSQL QSQLPP QLambdaNRA QCAMP QCAMPRule.
Require QUtil QType QEval.
Require QLang QDriver QStat. 

Module QLib(runtime:CompilerRuntime).

  Module QType := QType.QType runtime.
  Module QData := QData.QData runtime.
  Module QOps := QOperators.QOperators runtime.

  Module QOQL := QOQL.QOQL runtime.
  Module QSQL := QSQL.QSQL runtime.
  Module QSQLPP := QSQLPP.QSQLPP runtime.
  Module QLambdaNRA := QLambdaNRA.QLambdaNRA runtime.
  Module QCAMP := QCAMP.QCAMP runtime.
  Module QCAMPRule := QCAMPRule.QCAMPRule runtime.

  Module QLang := QLang.QLang runtime.
  Module QDriver := QDriver.QDriver runtime.
  Module QStat := QStat.QStat runtime.
  Module QUtil := QUtil.QUtil runtime.

  Module QEval := QEval.QEval runtime.

End QLib.

