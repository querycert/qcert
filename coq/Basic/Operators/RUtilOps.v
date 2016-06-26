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

(* Utilities methods used for defining the semantics of the operators *)

Section RUtilOps.

  Require Import String List.
  Require Import Utils.
  Require Import ZArith.

  Require Import RData.
  Require Import BrandRelation.
  Require Import ForeignData.

  Import ListNotations.

  Context {fdata:foreign_data}.

  Definition boolToString (b:bool) : string
    := if b then "TRUE"%string else "FALSE"%string.

  Definition bracketString (open s close:string)
    := append open (append s close).

  Definition stringToString (s:string) : string
(*    := bracketString "'"%string s "'"%string. *)
    := s.

  Fixpoint joinStrings (delim:string) (l:list string) : string
    := match l with
         | nil => EmptyString
         | x::nil => x
         | x::ls => append x (append delim (joinStrings delim ls))
       end.

  Definition string_sort := insertion_sort StringOrder.le_dec.

  Global Instance ToString_Z : ToString Z
    := { toString := Z_to_string10}.

  Global Instance ToString_bool : ToString bool
    := { toString := boolToString}.

  Instance ToString_brands : ToString brands
    := { toString := fun b => (joinStrings " & " b)}.
    
  Fixpoint dataToString (d:data) : string
    := match d with
           | dunit => "UNIT"%string
           | dnat n => toString n
           | dbool b => toString b
           | dstring s => stringToString s
           | dcoll l => bracketString 
                          "["%string
                          (joinStrings ", "
                                       (string_sort (map dataToString l)))
                          "]"%string
           | drec lsd => bracketString
             "{"%string
                (joinStrings "," 
                             (map (fun xy => let '(x,y):=xy in 
                                             (append (stringToString x) (append "->"%string
                                             (dataToString y)))
                                  ) lsd))
                "}"%string
           | dleft d => bracketString
                          "Left("%string
                          (dataToString d)
                          ")"%string
           | dright d => bracketString
                          "Right("%string
                          (dataToString d)
                          ")"%string
           | dbrand b d => (bracketString
                              "<"
                              (append (@toString _ ToString_brands b)
                                      (append ":" (dataToString d)))
                              ">")
           | dforeign fd => toString fd
       end.

  Global Instance ToString_data : ToString data
    := { toString := dataToString}.
  
  Fixpoint dsum (ns:list data) : option Z
    := match ns with
         | nil => Some 0%Z
         | dnat n::ls => lift (Zplus n) (dsum ls)
         | _ => None
       end.

  Definition darithmean (ns:list data) : option Z
    := match ns with
         | nil  => Some (0%Z)
         | _ => lift (fun x => Z.quot x (Z_of_nat (length ns))) (dsum ns)
       end.
  
End RUtilOps.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)