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
Require Import Bool.
Require Import RelationClasses.
Require Import EquivDec.
Require Import Utils.
Require Import ForeignType.
Require Import RType.
Require Import RSubtypeProp.
Require Import RTypeMeetJoin.
Require Import RConsistentSubtype.
Require Import BrandRelation.
Require Import Lattice.

Section RTypeLattice.

  Context {ftype:foreign_type}.
  Context {br:brand_relation}.
  
  Global Instance rtype_lattice : Lattice rtype eq
    := { meet:=rtype_meet;
         join:=rtype_join;
         meet_commutative := rtype_meet_commutative;
         meet_associative := rtype_meet_associative;
         meet_idempotent := rtype_meet_idempotent;
         join_commutative := rtype_join_commutative;
         join_associative := rtype_join_associative;
         join_idempotent := rtype_join_idempotent;
         meet_absorptive := rtype_meet_absorptive;
         join_absorptive := rtype_join_absorptive
       }.

  Global Instance rtype_olattice :
    OLattice eq subtype
    := { consistent_meet := consistent_rtype_meet }.

  Global Instance rtype_blattice :
    BLattice eq 
    := { top := Top;
         bottom := Bottom;
         join_bottom_r := rtype_join_Bottom_r;
         meet_top_r := rtype_meet_Top_r
       }.
  
End RTypeLattice.

