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

Require Import CompilerRuntime.
Module CompBack(runtime:CompilerRuntime).

  Require Import String List String EquivDec.

  Require Import BasicSystem.

  Require Import CompUtil.

  (* Compilation from DNNRC to Scala *)

  Require Import NNRC.
  Require Import DNNRC.
  Require Import DNNRCtoScala SparkIR.
  Require Import TypingRuntime.
  Require Import TDNRCInfer.

  Definition dnrc_to_scala_code_gen
             {bm:brand_model}
             {ftyping: foreign_typing}
             (inputType:rtype) (name:string) (e:dnrc (type_annotation unit) dataset) : string :=
    @dnrcToSpark2Top _ _ bm _ unit inputType name e.

End CompBack.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
