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

(* This module contains the implementation for the optimization logger *)

open SExp
open AstsToSExp

let logger_nra_to_sexp exp
  = nraenv_to_sexp (Obj.magic exp)
  
let logger_nrc_to_sexp exp
  = nnrc_to_sexp (Obj.magic exp)

let logger_nnrs_imp_expr_to_sexp exp
  = nnrs_imp_expr_to_sexp (Obj.magic exp)

let logger_nnrs_imp_stmt_to_sexp exp
  = nnrs_imp_stmt_to_sexp (Obj.magic exp)

let logger_nnrs_imp_to_sexp exp
  = nnrs_imp_to_sexp (Obj.magic exp)

let logger_dnrc_to_sexp exp
  = SString "DNRC->SEXP not yet implemented"
