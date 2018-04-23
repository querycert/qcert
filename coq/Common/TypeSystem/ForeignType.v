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

Require Import EquivDec.
Require Import Lattice.

Section ForeignType.
  
  Class foreign_type : Type
    := mk_foreign_type {
           foreign_type_type : Set
(* TODO: #35 is needed before we can generalize this
  ; foreign_type_equiv (a b : foreign_type_type) : Prop
  ; foreign_type_equiv_equiv :> Equivalence foreign_type_equiv
 *) 
           ; foreign_type_dec :> EqDec foreign_type_type eq
           ; foreign_type_lattice :> Lattice foreign_type_type eq
           ; foreign_type_sub (a b : foreign_type_type) : Prop
           ; foreign_type_sub_dec (a b : foreign_type_type) :
               { foreign_type_sub a b} + {~ foreign_type_sub a b}
           ; foreign_type_sub_pre :> PreOrder foreign_type_sub
           ; foreign_type_sub_part :> PartialOrder eq foreign_type_sub
           ; foreign_type_olattice :> OLattice eq foreign_type_sub
      }.
  
End ForeignType.

