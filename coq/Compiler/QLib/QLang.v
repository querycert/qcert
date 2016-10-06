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
Require Import CompLang.

Require Import CompilerRuntime.
Module QLang(runtime:CompilerRuntime).

  Require Import BasicSystem.

  Local Open Scope list_scope.

  Definition vdbindings := vdbindings.

  (* Languages *)

  Section QL.
    Context {bm:brand_model}.
    Context {ftyping: foreign_typing}.

    Definition rule := rule.
    Definition camp := camp.
    Definition oql := oql.
    Definition lambda_nra := lambda_nra.
    Definition nra := nra.
    Definition nraenv := nraenv.
    Definition nnrc := nnrc.
    Definition nnrcmr := nnrcmr.
    Definition cldmr := cldmr.
    Definition dnnrc_dataset := dnnrc_dataset.
    Definition dnnrc_typed_dataset {bm:brand_model} := dnnrc_typed_dataset.
    Definition javascript := javascript.
    Definition java := java.
    Definition spark := spark.
    Definition spark2 := spark2.
    Definition cloudant := cloudant.

    Definition language : Set := language.

    Definition query : Set := query.

    Definition language_of_name_case_sensitive : string -> language :=
      language_of_name_case_sensitive.
    Definition name_of_language : language -> string :=
      name_of_language.
    Definition language_of_query : query -> language := language_of_query.
    Definition name_of_query : query -> string := name_of_query.

  End QL.
End QLang.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
