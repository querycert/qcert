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

Require Import Utils.
Require Import CommonSystem.
Require Import DNNRCSystem.
  
Section tDNNRC.
  Context {fruntime:foreign_runtime}.
  Context {ftype: ForeignType.foreign_type}.
  Context {br:brand_relation}.

  Record type_annotation {A:Set} : Set :=
    mkType_annotation {
        ta_base:A
        (* the inferred (actual most general) type of the expression *)
        ; ta_inferred:drtype
        (* the type as it is used by the context.
           it should always be the case that
           drtype_sub ta_inferred ta_required (proof obligation)
         *)
        ; ta_required:drtype
                        
      }.

  Global Arguments type_annotation : clear implicits. 
  Global Arguments mkType_annotation {A} ta_base ta_inferred ta_required.
  
  Definition dnnrc_typed := @dnnrc_base _ (type_annotation unit) dataframe.

  Section Top.
    Context (h:brand_relation_t).

    Definition dnnrc_typed_eval_top
               (q:dnnrc_typed) (cenv:dbindings) : option data :=
      lift unlocalize_data (@dnnrc_base_eval _ _ _ h (rec_sort cenv) SparkIRPlug nil q).
  End Top.
  
End tDNNRC.

