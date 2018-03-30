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
Require Import Result.
Require Import ForeignData.
Require Import Data.

Section QResult.
  Context {fdata:foreign_data}.

  Inductive qerror : Set :=
  | CompilationError : string -> qerror
  | TypeError : string -> qerror
  | UserError : data -> qerror.

  Definition qresult (A:Set) := Result A qerror.
  Definition qsuccess {A:Set} (a:A) : qresult A :=
    Success A qerror a.
  Definition qfailure {A:Set} (e:qerror) : qresult A :=
    Failure A qerror e.
  Definition qolift {A B:Set} (f:A -> qresult B) (a:qresult A) : qresult B :=
    lift_failure f a.
  Definition qlift {A B:Set} (f:A -> B) (a:qresult A) : qresult B :=
    lift_failure_in f a.
  Definition qlift2 {A B C:Set} (f:A -> B -> C) (a:qresult A) (b:qresult B) : qresult C :=
    lift_failure_in_two f a b.
  Definition qlift3 {A B C D:Set} (f:A -> B -> C ->D)
             (a:qresult A) (b:qresult B) (c:qresult C) : qresult D :=
    lift_failure_in_three f a b c.
  Definition qmaplift {A B:Set} (f:A -> qresult B) (al:list A) : qresult (list B) :=
    lift_failure_map f al.
  Definition qresult_of_option {A:Set} (a:option A) (e:qerror) :=
    result_of_option a e.
  Definition option_of_qresult {A:Set} (a:qresult A) : option A :=
    option_of_result a.
End QResult.

