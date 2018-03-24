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

open Util
open DataUtil

open QcertCompiler.EnhancedCompiler

(* Data utils for the Camp evaluator and compiler *)

type schema = {
    sch_brand_model : QType.brand_model;
    sch_foreign_typing : QcertCompiler.foreign_typing;
    sch_io_schema : content_schema option;
    sch_globals : QDriver.constants_config;
  }

val empty_schema : schema
val schema_of_io_json : QData.json -> schema
val inheritance_of_schema : schema -> (char list * char list) list
val raw_inheritance_of_schema : schema -> QData.json

val brand_relation_of_brand_model : QType.brand_model -> QcertCompiler.brand_relation

type content_sdata = (char list * char list) list
val content_sdata_of_data : schema -> DataUtil.content_input -> content_sdata

