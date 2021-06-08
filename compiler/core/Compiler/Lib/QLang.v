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

Require Import String.
Require Import CompLang.
Require Import DataSystem.
Require Import CompilerRuntime.

Module QLang(runtime:CompilerRuntime).

  Local Open Scope list_scope.

  (* Languages *)

  Section QL.
    Context {bm:brand_model}.
    Context {ftyping: foreign_typing}.

    Definition camp_rule := camp_rule.
    Definition tech_rule := tech_rule.
    Definition designer_rule := designer_rule.
    Definition camp := camp.
    Definition oql := oql.
    Definition sql := sql.
    Definition sqlpp := sqlpp.
    Definition lambda_nra := lambda_nra.
    Definition nra := nra.
    Definition nraenv_core := nraenv_core.
    Definition nraenv := nraenv.
    Definition nnrc_core := nnrc_core.
    Definition nnrc := nnrc.
    Definition nnrs_core := nnrs_core.
    Definition nnrs := nnrs.
    Definition nnrs_imp_expr := nnrs_imp_expr.
    Definition nnrs_imp_stmt := nnrs_imp_stmt.
    Definition nnrs_imp := nnrs_imp.
    Definition imp_data := imp_data.
    Definition imp_ejson := @imp_ejson runtime.compiler_foreign_ejson_model runtime.compiler_foreign_ejson_runtime_op.
    Definition nnrcmr := nnrcmr.
    Definition dnnrc := dnnrc.
    Definition dnnrc_typed {bm:brand_model} := dnnrc_typed.
    Definition js_ast := js_ast.
    Definition javascript := javascript.
    Definition java := java.
    Definition spark_df := spark_df.
    Definition wasm_ast := wasm_ast.
    Definition wasm := wasm.

    Definition language : Set := language.

    Definition query : Set
      := @query
           runtime.compiler_foreign_type
           bm
           runtime.compiler_foreign_runtime
           runtime.compiler_foreign_ejson_model
           runtime.compiler_foreign_ejson_runtime_op
           runtime.compiler_foreign_reduce_op.

    Definition language_of_name_case_sensitive : string -> language :=
      language_of_name_case_sensitive.
    Definition name_of_language : language -> string :=
      name_of_language.
    Definition language_of_query : query -> language := language_of_query.
    Definition name_of_query : query -> string := name_of_query.

    Definition export_desc : Set := export_desc.
    Definition export_language_descriptions : export_desc := export_language_descriptions.

    Definition vdistr := Vdistr.
    Definition vlocal := Vlocal.
    Definition vdbindings := vdbindings.
    Definition tdbindings := tdbindings.
  End QL.
End QLang.

