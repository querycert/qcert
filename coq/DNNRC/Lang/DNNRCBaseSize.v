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

Require Import List.
Require Import Omega.
Require Import CommonRuntime.
Require Import DNNRCBase.

Section size.
  Context {fruntime:foreign_runtime}.
  Context {A plug_type:Set}.

  Context (plug_size:plug_type->nat).
  
  Fixpoint dnnrc_base_size (d:@dnnrc_base _ A plug_type)
    := match d with
       | DNNRCGetConstant _ _ => 1
       | DNNRCVar _ _ => 1
       | DNNRCConst _ _ => 1
       | DNNRCBinop _ _ d1 d2 => S (dnnrc_base_size d1 + dnnrc_base_size d2)
       | DNNRCUnop _ _ d0 => S (dnnrc_base_size d0)
       | DNNRCLet _ _ d1 d2 => S (dnnrc_base_size d1 + dnnrc_base_size d2)
       | DNNRCFor _ _ d1 d2 => S (dnnrc_base_size d1 + dnnrc_base_size d2)
       | DNNRCIf _ d1 d2 d3 => S (dnnrc_base_size d1 + dnnrc_base_size d2 + dnnrc_base_size d3)
       | DNNRCEither _ d1 _ d2 _ d3 =>
         S (dnnrc_base_size d1 + dnnrc_base_size d2 + dnnrc_base_size d3)
       | DNNRCGroupBy _ _ _ d0 => S (dnnrc_base_size d0)
       | DNNRCCollect _ d0 => S (dnnrc_base_size d0)
       | DNNRCDispatch _ d0 => S (dnnrc_base_size d0)
       | DNNRCAlg _ pt sdl => S ((* plug_size pt + *) 0) (* (fold_left (fun acc sc => dnnrc_base_size (snd sc) + acc) sdl 0)) *)
       end.

  Lemma dnnrc_base_size_nzero (d:@dnnrc_base _ A plug_type) : dnnrc_base_size d <> 0.
  Proof.
    induction d; simpl; omega.
  Qed.

End size.

