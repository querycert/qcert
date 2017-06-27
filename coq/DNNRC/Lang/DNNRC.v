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

Section DNNRC.

  Require Import Utils BasicSystem.

  Require Import DNNRCBase.
  Require Import Dataframe.

  Context {fruntime:foreign_runtime}.
  Context {ftype: ForeignType.foreign_type}.

  Definition dnnrc_dataframe := @dnnrc _ unit dataframe.

  Section Top.
    Context (h:brand_relation_t).
    Definition dnnrc_dataframe_eval_top (q:dnnrc_dataframe) (cenv:dbindings) : option ddata :=
      dnnrc_eval h (rec_sort cenv) nil q.
  End Top.
End DNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
