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

open Util
open SExp

val nra_log_startPass : string -> 'a -> nra_logger_token_type
val nra_log_step : nra_logger_token_type -> string -> 'a -> 'a -> nra_logger_token_type
val nra_log_endPass : nra_logger_token_type -> 'a -> nra_logger_token_type

val nra_set_trace : (Obj.t->sexp) -> string -> unit

val nrc_log_startPass : string -> 'a -> nrc_logger_token_type
val nrc_log_step : nrc_logger_token_type -> string -> 'a -> 'a -> nrc_logger_token_type
val nrc_log_endPass : nrc_logger_token_type -> 'a -> nrc_logger_token_type

val nrc_set_trace : (Obj.t->sexp) -> string -> unit

val nnrs_imp_expr_log_startPass : string -> 'a -> nnrs_imp_expr_logger_token_type
val nnrs_imp_expr_log_step : nnrs_imp_expr_logger_token_type -> string -> 'a -> 'a -> nnrs_imp_expr_logger_token_type
val nnrs_imp_expr_log_endPass : nnrs_imp_expr_logger_token_type -> 'a -> nnrs_imp_expr_logger_token_type

val nnrs_imp_expr_set_trace : (Obj.t->sexp) -> string -> unit

val nnrs_imp_stmt_log_startPass : string -> 'a -> nnrs_imp_stmt_logger_token_type
val nnrs_imp_stmt_log_step : nnrs_imp_stmt_logger_token_type -> string -> 'a -> 'a -> nnrs_imp_stmt_logger_token_type
val nnrs_imp_stmt_log_endPass : nnrs_imp_stmt_logger_token_type -> 'a -> nnrs_imp_stmt_logger_token_type

val nnrs_imp_stmt_set_trace : (Obj.t->sexp) -> string -> unit

val nnrs_imp_log_startPass : string -> 'a -> nnrs_imp_logger_token_type
val nnrs_imp_log_step : nnrs_imp_logger_token_type -> string -> 'a -> 'a -> nnrs_imp_logger_token_type
val nnrs_imp_log_endPass : nnrs_imp_logger_token_type -> 'a -> nnrs_imp_logger_token_type

val nnrs_imp_set_trace : (Obj.t->sexp) -> string -> unit

val nnrs_imp_all_set_trace : (Obj.t->sexp) -> (Obj.t->sexp) -> (Obj.t->sexp) -> string -> unit

  
val dnrc_log_startPass : string -> 'a -> dnrc_logger_token_type
val dnrc_log_step : dnrc_logger_token_type -> string -> 'a -> 'a -> dnrc_logger_token_type
val dnrc_log_endPass : dnrc_logger_token_type -> 'a -> dnrc_logger_token_type

val dnrc_set_trace : (Obj.t->sexp) -> string -> unit
