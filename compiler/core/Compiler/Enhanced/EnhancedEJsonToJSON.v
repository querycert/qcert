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

Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import String.
Require Import Utils.
Require Import EJsonSystem.
Require Import JSONSystem.
Require Import ForeignDataToEJson.
Require Import ForeignEJsonToJSON.
Require Import ForeignToEJsonRuntime.

Require Import SqlDateComponent.

Require Import EnhancedData.
Require Import EnhancedEJson.

Import ListNotations.
Local Open Scope list_scope.

Definition enhanced_foreign_json_to_ejson (j:json) : option enhanced_ejson :=
  match j with
  | jobject
      (("$date"%string,jobject
                         (("day"%string,jnumber day)
                            ::("month"%string,jnumber month)
                            ::("year"%string, jnumber year)
                            ::nil))::nil)
  | jobject
      (("$date"%string,jobject
                         (("year"%string, jnumber year)
                            ::("month"%string,jnumber month)
                            ::("day"%string,jnumber day)
                            ::nil))::nil) =>
    Some (enhancedsqldate (SQL_DATE_from_parts
                             (float_truncate year)
                             (float_truncate month)
                             (float_truncate day)))
  | jobject (("$period"%string,jstring s)::nil) =>
    Some (enhancedsqldateperiod (SQL_DATE_PERIOD_from_string s))
  | _ => None
  end.

Definition enhanced_foreign_ejson_to_json (ej:enhanced_ejson) : json :=
  match ej with
  | enhancedsqldate fd =>
    jobject
      (("$date"%string,
        jstring (SQL_DATE_to_string fd))::nil)
  | enhancedsqldateperiod fd =>
    jobject
      (("$period"%string,
        jstring (SQL_DATE_PERIOD_to_string fd))::nil)
  end.

Global Program Instance enhanced_foreign_to_json : foreign_to_json
  := mk_foreign_to_json enhanced_ejson enhanced_foreign_ejson _ _.
Next Obligation.
  exact (enhanced_foreign_json_to_ejson fd).
Defined.
Next Obligation.
  exact (enhanced_foreign_ejson_to_json j).
Defined.

