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

Require Import Orders.
Require Import Equivalence.
Require Import EquivDec.
Require Import Compare_dec.
Require Import String.
Require Import List.
Require Import StringAdd.

Section SortingDesc.
  Inductive SortDesc : Set := | Descending | Ascending.
  Definition SortCriteria : Set := string * SortDesc.
  Definition SortCriterias : Set := list SortCriteria.

  Lemma sort_desc_eq_dec : forall x y:SortDesc, {x=y}+{x<>y}.
  Proof.
    decide equality.
  Defined.
  
  (* begin hide *)
  Global Instance sort_desc_eqdec : EqDec SortDesc eq := sort_desc_eq_dec.
  (* begin hide *)

End SortingDesc.
