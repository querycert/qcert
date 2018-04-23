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

Require Import DNNRCSystem.
Require Import tDNNRCSystem.

Section DNNRCtotDNNRC.

  Section Top.
    Context {ftype: ForeignType.foreign_type}.
    Context {fr:foreign_runtime}.
    Context {bm:brand_model}.
    Context {ftyping: foreign_typing}.

    Definition dnnrc_to_dnnrc_typed_top (tdenv: tdbindings) (q:dnnrc) : option dnnrc_typed :=
      infer_dnnrc_base_type tdenv nil q.

  End Top.
  
End DNNRCtotDNNRC.

