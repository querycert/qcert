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

(* Top-level grammar from ODMG:

   <interface> ::= <interface_dcl>
                | <interface_forward_dcl>
   <interface_dcl> ::= <interface_header> { [ <interface_body> ] }
   <interface_forward_dcl> ::= interface <identifier>
   <interface_header> ::= interface <identifier> [ <inheritance_spec> ]
   <class> ::= <class_dcl> | <class_forward_dcl>
   <class_dcl> ::= <class_header> { <interface_body> }
   <class_forward_dcl> ::= class <identifier>
   <class_header> ::= class <identifier>
                        [ extends <scopedName> ] [ <inheritance_spec> ]
                        [ <type_property_list> ]

 *)

Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.

Section ODL.
  Inductive odl_export : Set :=
  | OTypeDcl : odl_type_dcl -> odl_interface_body
  | 

  Definition odl_interface_body : Set := list odl_export.
  
  Inductive odl_decl : Set :=
  | OClass : string -> 
    
End ODL.

