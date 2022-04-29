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

open EnhancedCompiler.EnhancedCompiler

open Data_util

(* Data utils for the Camp evaluator and compiler *)

type schema = {
    sch_brand_model : QType.brand_model;
    sch_foreign_typing : ForeignTyping.foreign_typing;
    sch_io_schema : content_schema option;
    sch_globals : QDriver.constants_config;
  }

val empty_schema : schema
val schema_of_io_json : QData.json -> schema
val inheritance_of_schema : schema -> (string * string) list
val raw_inheritance_of_schema : schema -> QData.json

type content_sdata = (string * string) list
val content_sdata_of_data : schema -> content_input -> content_sdata

