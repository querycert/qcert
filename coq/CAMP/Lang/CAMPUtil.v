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

(** Encoding and utility functions to support the result of evaluation
over CAMP patterns. *)

Require Import String.
Require Import List.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonRuntime.

Section CAMPUtil.
  Local Open Scope string.

  (** Evaluating a CAMP pattern returns a presult, which includes two
  kinds of errors: either a match failure, which is recoverable, or a
  terminal error. *)
  
  Inductive presult A :=
  | TerminalError : presult A
  | RecoverableError : presult A
  | Success (res:A) : presult A.

  (* begin hide *)
  Arguments TerminalError {A}.
  Arguments RecoverableError {A}.
  Arguments Success {A} res.
  (* end hide *)

  (** Equality between two presult is decidable *)
  
  Global Instance presult_eqdec {A} {dec:EqDec A eq} :
    EqDec (presult A) eq.
  Proof.
    red; unfold equiv, complement.
    destruct x; destruct y; simpl;
      try solve [right; inversion 1]; eauto 2.
    destruct (res == res0); unfold equiv, complement in *;
      [left | right; inversion 1]; congruence.
  Defined.
  
  (** Prints a presult *)
  
  Global Instance print_presult {A} {tos:ToString A} : ToString (presult A)
    := { toString :=
           fun pr =>
             match pr with
             | TerminalError => "TerminalError (for more info, use debug mode)"
             | RecoverableError => "RecoverableError (for more info, use debug mode)"
             | Success res => "Success: " ++ toString res
             end
       }.
  
  (** Lifting functions used in the evaluation of patterns. Used to handle the various possible presults during evaluation. *)
  Definition liftpr {A B:Type} (f:A->B) (pr:presult A) : presult B
    := match pr with
       | TerminalError => TerminalError
       | RecoverableError => RecoverableError
       | Success a => Success (f a)
       end.

  Definition bindpr {A B:Type} (pr:presult A) (f:A->presult B) : presult B
    := match pr with
       | TerminalError => TerminalError 
       | RecoverableError => RecoverableError
       | Success a => (f a)
       end.

  Lemma liftpr_bindpr {A B:Type} (f:A->B) pr :
    liftpr f pr = bindpr pr (fun x => Success (f x)).
  Proof.
    destruct pr; simpl; trivial.
  Qed.

  (** Accumulates successful evaluation, skipping match failures. A terminal error is always final. *)
  
  Fixpoint gather_successes {A:Type} (os:list (presult A)) : presult (list A)
    := match os with
       | nil => Success nil
       | (TerminalError)::xs => TerminalError 
       | (RecoverableError)::xs => gather_successes xs
       | (Success a)::xs => liftpr (cons a) (gather_successes xs)
       end.

  (** Accumulates successful evaluation, but propagating match failure to the top *)
  
  Fixpoint enforce_successes {A:Type} (os:list (presult A)) : presult (list A)
    := match os with
       | nil => Success nil
       | (TerminalError)::xs => TerminalError
       | (RecoverableError)::xs => RecoverableError
       | (Success a)::xs => liftpr (cons a) (gather_successes xs)
       end.
  
  Definition op2tpr {A:Type} (o:option A) : presult A
    := match o with
       | None => TerminalError
       | Some x => Success x
       end.

  Definition op2rpr {A:Type} (o:option A) : presult A
    := match o with
       | None => RecoverableError
       | Some x => Success x
       end.

  Section Debug.
  (* If we were reasoning about this formally, we would want to use a proper
     one-hole context.  Since we are not, a trail of choices suffices *)
  Definition camp_src_path
    := list nat.

    Inductive presult_debug A :=
    | TerminalError_debug (s:string) (loc:camp_src_path) : presult_debug A
    | RecoverableError_debug (s:string) : presult_debug A
    | Success_debug (res:A) : presult_debug A.

    (* begin hide *)
    Arguments TerminalError_debug {A} s loc.
    Arguments RecoverableError_debug {A} s.
    Arguments Success_debug {A} res.
    (* end hide *)

    (* Not a ToString instance since it requires the top level pattern *)  
    Definition print_presult_debug {A} {B} {tos:ToString A} (p:B)
               (pPrint:B -> camp_src_path -> string) (pr:presult_debug A)
      := match pr with
         | TerminalError_debug s loc => "TerminalError: " ++ s ++ ". This error occurred in the bracketed code: \n" ++ (pPrint p (rev loc))
         | RecoverableError_debug s => "RecoverableError: " ++ s
         | Success_debug res => "Success: " ++ toString res
         end.
    
    (** Useful lifting functions used in the evaluation of patterns. Used to handle the various possible presults *)
    Definition liftpr_debug {A B:Type} (f:A->B) (pr:presult_debug A) : presult_debug B
      := match pr with
         | TerminalError_debug s loc => TerminalError_debug s loc
         | RecoverableError_debug s => RecoverableError_debug s
         | Success_debug a => Success_debug (f a)
         end.

    Definition bindpr_debug {A B:Type} (pr:presult_debug A) (f:A->presult_debug B) : presult_debug B
      := match pr with
         | TerminalError_debug s loc => TerminalError_debug s loc
         | RecoverableError_debug s => RecoverableError_debug s
         | Success_debug a => (f a)
         end.

    Lemma liftpr_debug_bindpr_debug {A B:Type} (f:A->B) pr :
      liftpr_debug f pr = bindpr_debug pr (fun x => Success_debug (f x)).
    Proof.
      destruct pr; simpl; trivial.
    Qed.

    Fixpoint gather_successes_debug {A:Type} (os:list (presult_debug A)) : presult_debug (list A)
      := match os with
         | nil => Success_debug nil
         | (TerminalError_debug s loc)::xs => TerminalError_debug s loc
         | (RecoverableError_debug s)::xs => gather_successes_debug xs
         | (Success_debug a)::xs => liftpr_debug (cons a) (gather_successes_debug xs)
         end.

    Fixpoint enforce_successes_debug {A:Type} (os:list (presult_debug A)) : presult_debug (list A)
      := match os with
         | nil => Success_debug nil
         | (TerminalError_debug s loc)::xs => TerminalError_debug s loc
         | (RecoverableError_debug s)::xs => RecoverableError_debug s
         | (Success_debug a)::xs => liftpr_debug (cons a) (gather_successes_debug xs)
         end.
  
    Definition op2tpr_debug {A:Type} (err:string) (loc:camp_src_path) (o:option A) : presult_debug A
      := match o with
         | None => TerminalError_debug err loc
         | Some x => Success_debug x
         end.
    
    Definition op2rpr_debug {A:Type} (err:string) (o:option A) : presult_debug A
      := match o with
         | None => RecoverableError_debug err
         | Some x => Success_debug x
         end.

    Definition presult_same {A} (res:presult A) (res_debug:presult_debug A) :=
      match res, res_debug with
      | TerminalError, TerminalError_debug _ _ => True
      | RecoverableError, RecoverableError_debug _ => True
      | Success x, Success_debug y => x = y
      | _, _ => False
      end.
    
    Lemma liftpr_presult_same {A B} (f:A->B) d1 d2 :
      presult_same d1 d2 ->
      presult_same (liftpr f d1) (liftpr_debug f d2).
    Proof.
      unfold presult_same.
      destruct d1; destruct d2; simpl; congruence.
    Qed.

    Lemma gather_successes_presult_same {A} d1 d2 :
      Forall2 (@presult_same A) d1 d2 ->
      presult_same (gather_successes d1) (gather_successes_debug d2).
    Proof.
      unfold presult_same.
      induction 1; simpl; trivial.
      destruct x; destruct y; destruct (gather_successes l); destruct (gather_successes_debug l'); simpl in *; subst; intuition.
    Qed.
    
    Lemma bindpr_presult_same {A B} d1 d2 f1 f2:
      presult_same d1 d2 ->
      (forall x, presult_same (f1 x) (f2 x)) ->
      presult_same (@bindpr A B d1 f1) (bindpr_debug d2 f2).
    Proof.
      destruct d1; destruct d2; simpl in *; try tauto.
      intros; subst; auto.
    Qed.
    
  End Debug.

  (** Maps the input/output(s) between NNRC and CAMP *)

  Definition pr2op {A:Type} (pr:presult A) : option A
    := match pr with
       | Success a => Some a
       | _ => None
       end.

  Lemma pr2op_op2tpr {A:Type} (op:option A) :
    pr2op (op2tpr op) = op.
  Proof.
    destruct op; trivial.
  Qed.

  Lemma pr2op_op2rpr {A:Type} (op:option A) :
    pr2op (op2rpr op) = op.
  Proof.
    destruct op; trivial.
  Qed.

  Definition isRecoverableError {A:Type} (pr:presult A)
    := match pr with
       | RecoverableError => true
       | _ => false
       end.
  
  Lemma op2tpr_not_recoverable {A:Type} (op:option A) :
    isRecoverableError (op2tpr op) = false.
  Proof.
    destruct op; trivial.
  Qed.

  Lemma isRecoverableError_liftpr {A B:Type} (f:A->B) (pr:presult A) 
    : isRecoverableError (liftpr f pr) = isRecoverableError pr.
  Proof.
    destruct pr; trivial.
  Qed.

End CAMPUtil.

(* begin hide *)
Arguments TerminalError {A}.
Arguments RecoverableError {A}.
Arguments Success {A} res.

Arguments TerminalError {A}.
Arguments RecoverableError {A}.
Arguments Success {A} res.
Arguments TerminalError_debug {A} s loc.
Arguments RecoverableError_debug {A} s.
Arguments Success_debug {A} res.
(* end hide *)

