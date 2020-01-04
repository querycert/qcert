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
Require Import List.
Require Import Data.
Require Import ForeignData.

Section Constants.
  
  Context {fdata:foreign_data}.

  Definition WORLD:string := "WORLD"%string.
    
  (* Declares single input collection containing world *)
  Definition mkWorld (world:list data) : list (string*data)
    := (WORLD,(dcoll world))::nil.

  (* bindings that may or may not be initialized (defined) *)
  Definition pd_bindings := list (string*option data).
End Constants.

