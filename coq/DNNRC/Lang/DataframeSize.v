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
Require Import CommonSystem.
Require Import Dataframe.

Section DataframeSize.
  Context {fruntime:foreign_runtime}.
  Context {ftype: foreign_type}.

  Fixpoint column_size (c:column)
    := match c with
       | CCol _ => 1
       | CDot _ c0 => S (column_size c0)
       | CLit _ => 1
       | CPlus c1 c2 => S (column_size c1 + column_size c2)
       | CEq c1 c2 => S (column_size c1 + column_size c2)
       | CLessThan  c1 c2 => S (column_size c1 + column_size c2)
       | CNeg c0 => S (column_size c0)
       (* NOTE we actually codegen to a UDF for this, not Spark's printing *)
       | CToString c0 => S (column_size c0)
       | CSConcat c1 c2 => S (column_size c1 + column_size c2)
       | CUDFCast _ c0 => S (column_size c0)
       | CUDFUnbrand _ c0 => S (column_size c0)
       end.

  Fixpoint dataframe_size (d:dataframe)
    := match d with
       | DSVar _ => 1
       | DSSelect scl d0 => S ( 
                                (fold_left (fun acc sc => column_size (snd sc) + acc) scl 0)
                                  + dataframe_size d0)
       | DSFilter c0 d0 => S (column_size c0 + dataframe_size d0)
       | DSCartesian d1 d2 => S (dataframe_size d1 + dataframe_size d2)
       | DSExplode _ d0 => S (dataframe_size d0)
       end.


  Lemma column_size_nzero (c:column) : column_size c <> 0.
  Proof.
    induction c; simpl; omega.
  Qed.

    Lemma dataframe_size_nzero (d:dataframe) : dataframe_size d <> 0.
  Proof.
    induction d; simpl; omega.
  Qed.

End DataframeSize.

