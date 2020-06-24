(*
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
open Sexp

val nraenv_log_startPass : string -> 'a -> nraenv_logger_token_type
val nraenv_log_step : nraenv_logger_token_type -> string -> 'a -> 'a -> nraenv_logger_token_type
val nraenv_log_endPass : nraenv_logger_token_type -> 'a -> nraenv_logger_token_type

val nraenv_set_trace : (Obj.t->sexp) -> string -> unit

val nnrc_log_startPass : string -> 'a -> nnrc_logger_token_type
val nnrc_log_step : nnrc_logger_token_type -> string -> 'a -> 'a -> nnrc_logger_token_type
val nnrc_log_endPass : nnrc_logger_token_type -> 'a -> nnrc_logger_token_type

val nnrc_set_trace : (Obj.t->sexp) -> string -> unit

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

  
val dnnrc_log_startPass : string -> 'a -> dnnrc_logger_token_type
val dnnrc_log_step : dnnrc_logger_token_type -> string -> 'a -> 'a -> dnnrc_logger_token_type
val dnnrc_log_endPass : dnnrc_logger_token_type -> 'a -> dnnrc_logger_token_type

val dnnrc_set_trace : (Obj.t->sexp) -> string -> unit
