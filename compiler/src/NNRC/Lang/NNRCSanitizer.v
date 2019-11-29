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
Require Import Ascii.
Require Import Utils.
Require Import cNNRCShadow.
Require Import NNRC.
Require Import NNRCShadow.
Require Import CommonRuntime.

Local Open Scope string_scope.

Section NNRCSanitizer.
  (* Java equivalent: JavaScriptBackend.unshadow_js *)
  Context {fruntime:foreign_runtime}.

  Definition unshadow_js {fruntime:foreign_runtime} (avoid:list var) (e:nnrc) : nnrc
    := unshadow jsSafeSeparator jsIdentifierSanitize (avoid++jsAvoidList) e.

  Definition jsSanitizeNNRC {fruntime:foreign_runtime} (e:nnrc) : nnrc
    := unshadow_js nil e.

End NNRCSanitizer.
