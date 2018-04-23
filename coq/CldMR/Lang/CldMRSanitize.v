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

(** This contains support functions in order to emit code which
follows lexical constraints imposed by Cloudant. *)
 

Require Import String.
Require Import Ascii.
Require Import List.
Require Import Sorting.Mergesort.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCRuntime.
Require Import NNRCMRRuntime.
Require Import CldMRUtil.
Require Import ForeignCloudant.
  
Section CldMRSanitize.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {fcloudant:foreign_cloudant}.

  Context (h:list(string*string)).

  Import ListNotations.
  Definition cldAllowedIdentifierInitialCharacters :=
    ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]%char.

  (** According to https://docs.cloudant.com/database.html, this
      cldAllowedIdentifierCharacters_fromdocs work.  But $ at least
      has been reported as causing problems with the UI.  So we
      conservatively use cldAllowedIdentifierCharacters instead. *)
  
  Definition cldAllowedIdentifierCharacters_fromdocs := ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_";"$";",";"+";"-";"/"]%char.
    
  Definition cldAllowedIdentifierCharacters := ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_"]%char.

  Definition cldIdentifierInitialCharacterToAdd := "z"%char.
  Definition cldIdenitiferCharacterForReplacement := "z"%char.

  (* Java equivalent: MROptimizer.cldIdentifierFixInitial *)
  Definition cldIdentifierFixInitial (ident:string) : string
    := match ident with
       (* We also don't want empty identifier names *)
       | EmptyString =>
         String cldIdentifierInitialCharacterToAdd EmptyString
       | String a _ =>
         if in_dec ascii_dec a cldAllowedIdentifierInitialCharacters
         then ident
         else String cldIdentifierInitialCharacterToAdd ident
       end.

  (* Java equivalent: MROptimizer.cldIdentifierSanitizeChar *)
  Definition cldIdentifierSanitizeChar (a:ascii)
    := if a == "$"%char (* special case for readability *)
       then "_"%char
       else if in_dec ascii_dec a cldAllowedIdentifierCharacters
            then a
            else cldIdenitiferCharacterForReplacement.

  (* Java equivalent: MROptimizer.cldIdentifierSanitizeBody *)
  Definition cldIdentifierSanitizeBody (ident:string)
    := map_string cldIdentifierSanitizeChar ident.
  
  (* Java equivalent MROptimizer.cldIdentifierSanitize *)
  Definition cldIdentifierSanitize (ident:string)
    := cldIdentifierFixInitial (cldIdentifierSanitizeBody (mk_lower ident)).
  
  (* Java equivalent (used in): MROptimizer.nrcmr_rename_graph_for_cloudant *)
  Definition cldSafeSeparator := "_"%string.

  (* Java equivalent (used in): MROptimizer.nrcmr_rename_graph_for_cloudant *)
  Definition cldAvoidList : list string := [].

End CldMRSanitize.

