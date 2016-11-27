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

Section Pattern.

  Require Import String.
  Require Import List.
  Require Import EquivDec.
  Require Import Morphisms.

  Require Import BasicRuntime.

  Context {fruntime:foreign_runtime}.

  (* begin hide *)
  Definition Var := nat.
  (* end hide *)

  (** Patterns in CAMP *)
  Inductive pat : Set :=
  | pconst : data -> pat   (* This allows the empty list and empty record to be created *)
  | punop : unaryOp -> pat -> pat (* this does need the first pattern argument, but providing it is more uniform with respect to pbinop *)
  | pbinop : binOp -> pat -> pat -> pat
  | pmap : pat -> pat
(*| pgroupBy : pat -> pat *)
  | passert : pat -> pat (* converts (dbool true) to [], and everything else to match failure *)
  | porElse : pat -> pat -> pat (* if the first pattern fails, try the second pattern *)
  | pit : pat
  | pletIt : pat -> pat -> pat
  | pgetconstant : string -> pat
  | penv : pat
    (* Run the first pattern, which must return a record of new bindings. This is merged with the current bindings, and used to run the second pattern *)
  | pletEnv : pat -> pat -> pat
  | pleft : pat
  | pright : pat.

  Tactic Notation "pat_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "pconst"%string
  | Case_aux c "punop"%string
  | Case_aux c "pbinop"%string
  | Case_aux c "pmap"%string
(*| Case_aux c "pgroupBy"%string *)
  | Case_aux c "passert"%string
  | Case_aux c "porElse"%string
  | Case_aux c "pit"%string
  | Case_aux c "pletIt"%string
  | Case_aux c "pgetconstant"%string
  | Case_aux c "penv"%string
  | Case_aux c "pletEnv"%string
  | Case_aux c "pleft"%string
  | Case_aux c "pright"%string].
  
  Global Instance pat_eqdec : EqDec pat eq.
  Proof.
    change (forall x y : pat, {x = y} + {x <> y}).
    decide equality.
    apply data_eqdec.
    apply unaryOp_eqdec.
    apply binOp_eqdec.
    apply string_dec.
  Qed.

  Local Open Scope string.

  Global Instance ToString_pat : ToString pat
    := { toString :=
           fix toStringp (p:pat) : string :=
             match p with
               | pconst d => "(pconst " ++ toString d ++ ")"
               | punop u p1 => "(punop " ++ toString u ++ " " ++ toStringp p1 ++ ")"
               | pbinop b p1 p2 => "(pbinop " ++ toString b ++ " " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
               | pmap p1 => "(pmap " ++ toStringp p1 ++ ")"
               | passert p1 => "(passert " ++ toStringp p1 ++ ")"
               | porElse p1 p2 => "(porElse " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
               | pit  => "pit"
               | pletIt p1 p2 => "(pletIt " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
               | pgetconstant s => "(pgetconstant " ++ s ++ ")"
               | penv => "penv"
               | pletEnv p1 p2 => "(pletEnv " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
               | pleft => "pleft"
               | pright => "pright"
             end
       }.

  (* If we were reasoning about this formally, we would want to use a proper
     one-hole context.  Since we are not, a trail of choices suffices *)
  Definition pat_src_path
    := list nat.

  Fixpoint toString_pat_with_path (p:pat) (loc:pat_src_path) :=
    match loc with
      | nil => bracketString "<<<"  (toString p) ">>>"
      | pos::loc' =>
        match p with
      | pconst d => "(pconst " ++ toString d ++ ")"
      | punop u p1 => "(punop " ++ toString u ++ " " ++
                                toString_pat_with_path p1 loc' ++ ")"
      | pbinop b p1 p2 => "(pbinop "
                            ++ toString b ++ " " ++
                            (if pos == 0
                             then toString_pat_with_path p1 loc'
                             else toString p1)
                            ++ " " ++
                            (if pos == 1
                             then toString_pat_with_path p2 loc'
                             else toString p2) ++ ")"
      | pmap p1 => "(pmap " ++ toString_pat_with_path p1 loc' ++ ")"
      | passert p1 => "(passert " ++ toString_pat_with_path p1 loc' ++ ")"
      | porElse p1 p2 => "(porElse " ++
                            (if pos == 0
                             then toString_pat_with_path p1 loc'
                             else toString p1)
                            ++ " " ++
                            (if pos == 1
                             then toString_pat_with_path p2 loc'
                             else toString p2) ++ ")"

      | pit  => "pit"
      | pletIt p1 p2 => "(pletIt " ++
                            (if pos == 0
                             then toString_pat_with_path p1 loc'
                             else toString p1)
                            ++ " " ++
                            (if pos == 1
                             then toString_pat_with_path p2 loc'
                             else toString p2) ++ ")"
      | pgetconstant s => "(pgetconstant " ++ s ++ ")"
      | penv => "penv"
      | pletEnv p1 p2 => "(pletEnv " ++ 
                            (if pos == 0
                             then toString_pat_with_path p1 loc'
                             else toString p1)
                            ++ " " ++
                            (if pos == 1
                             then toString_pat_with_path p2 loc'
                             else toString p2) ++ ")"

      | pleft => "pleft"
      | pright => "pright"
    end
    end.

  Section eval.
  (** Evaluating a pattern returns a presult.  The error strings are for debugging purposes *)

  Inductive presult A :=
  | TerminalError : presult A
  | RecoverableError : presult A
  | Success (res:A) : presult A.

  (* begin hide *)
  Arguments TerminalError {A}.
  Arguments RecoverableError {A}.
  Arguments Success {A} res.
  (* end hide *)
  
  Global Instance print_presult {A} {tos:ToString A} : ToString (presult A)
    := { toString :=
           fun pr =>
             match pr with
               | TerminalError => "TerminalError (for more info, use debug mode)"
               | RecoverableError => "RecoverableError (for more info, use debug mode)"
               | Success res => "Success: " ++ toString res
             end
       }.
  
  Global Instance presult_eqdec {A} {dec:EqDec A eq} :
    EqDec (presult A) eq.
  Proof.
    red; unfold equiv, complement.
    destruct x; destruct y; simpl;
    try solve [right; inversion 1]; eauto 2.
    destruct (res == res0); unfold equiv, complement in *;
    [left | right; inversion 1]; congruence.
  Defined.
  

  (** Useful lifting functions used in the evaluation of patterns. Used to handle the various possible presults *)
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

  Fixpoint gather_successes {A:Type} (os:list (presult A)) : presult (list A)
    := match os with
       | nil => Success nil
       | (TerminalError)::xs => TerminalError 
       | (RecoverableError)::xs => gather_successes xs
       | (Success a)::xs => liftpr (cons a) (gather_successes xs)
       end.

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

  (* begin hide *)
  Definition op2rpr {A:Type} (o:option A) : presult A
    := match o with
       | None => RecoverableError
       | Some x => Success x
       end.

  Definition pr2op (o:presult data) : option data
    := match o with
       | RecoverableError => None
       | TerminalError => Some dunit
       | Success x => Some x
       end.
  
  (* end hide *)

  (** Semantics of CAMP pattern, returning a presult *)
  Context (h:brand_relation_t).
  Context (constant_env:bindings).
        
  Fixpoint interp (p:pat) (bind:bindings) (d:data) : presult data
    := match p with
       | pconst d' => Success (normalize_data h d')
       | punop op p₁ => bindpr (interp p₁ bind d)
                               (fun d' => (op2tpr (fun_of_unaryop h op d')))
       | pbinop op p₁ p₂ => 
         bindpr (interp p₁ bind d)
                (fun d'₁ => 
                   bindpr (interp p₂ bind d)
                          (fun d'₂ =>  (op2tpr (fun_of_binop h op d'₁ d'₂))))
       | pmap p₁ =>
         match d with
         | dcoll l => liftpr dcoll (gather_successes (map (interp p₁ bind) l))
         | _ => TerminalError

         end
(* Adds some unexpected complexity since the pattern used to calculate the key may return match failure.
   How should we handle it? One option is to turn match failure into dunit, which possibly pushes part of the complexity
   down to the algebra. Not sure what the other
   options are ... - J
       | pgroupBy p₁ =>
         match d with
         | dcoll l => op2tpr "groupBy failed"
                             (lift dcoll
                                   (group_by_nested_eval_kv (fun x => pr2op (interp p₁ bind x)) l))
         | _ => TerminalError "pgroupBy evaluated when scrutinee is not a collection"
         end *)
       | passert p₁ =>     
         bindpr (interp p₁ bind d)
                (fun d' => match d' with
                           | dbool true => Success (drec nil)
                           | dbool false => RecoverableError
                           | _ => TerminalError 
                           end)
       | porElse p₁ p₂ =>
         match interp p₁ bind d with
         | TerminalError => TerminalError
         | RecoverableError => interp p₂ bind d
         | Success x => Success x
         end
       | pit => Success d
       | pletIt p₁ p₂ =>
         bindpr (interp p₁ bind d) (interp p₂ bind)
       | pgetconstant s => op2tpr (edot constant_env s)
       | penv => Success (drec bind)
       | pletEnv p₁ p₂ =>
         bindpr (interp p₁ bind d)
                (fun rd'₁ => match rd'₁ with
                             | drec d'₁ => match merge_bindings bind d'₁ with
                                           | Some bind' => interp p₂ bind' d
                                           | None => RecoverableError
                                           end
                             | _ => TerminalError 
                             end)
       | pleft =>
         match d with
         | dleft d' => Success d'
         | dright _ => RecoverableError 
         | _ => TerminalError 
         end
       | pright =>
         match d with
         | dright d' => Success d'
         | dleft _ => RecoverableError
         | _ => TerminalError 
         end
       end.

  End eval.

  (** an alternative version of the compiler that keeps debug information. 
     Theorem interp_debug_correct ensures that this version is kept in sync
     with the simpler compiler.  This forces some code duplication, but the interpreter is relatively small and simple.  Trying to avoid code duplication complicates the (relatively longer) compilers and proofs. *)
  Section eval_debug.

  Inductive presult_debug A :=
  | TerminalError_debug (s:string) (loc:pat_src_path) : presult_debug A
  | RecoverableError_debug (s:string) : presult_debug A
  | Success_debug (res:A) : presult_debug A.

    (* begin hide *)
  Arguments TerminalError_debug {A} s loc.
  Arguments RecoverableError_debug {A} s.
  Arguments Success_debug {A} res.
  (* end hide *)

  (* Not a ToString instance since it requires the top level pattern *)  
  Definition print_presult_debug {A} {tos:ToString A} (p:pat) (pr:presult_debug A)
    := match pr with
         | TerminalError_debug s loc => "TerminalError: " ++ s ++ ". This error occurred in the bracketed code: \n" ++ (toString_pat_with_path p (rev loc))
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
  
  Definition op2tpr_debug {A:Type} (err:string) (loc:pat_src_path) (o:option A) : presult_debug A
    := match o with
       | None => TerminalError_debug err loc
       | Some x => Success_debug x
       end.
    
  (* begin hide *)
  Definition op2rpr_debug {A:Type} (err:string) (o:option A) : presult_debug A
    := match o with
       | None => RecoverableError_debug err
       | Some x => Success_debug x
       end.

  Definition pr2op_debug (o:presult_debug data) : option data
    := match o with
       | RecoverableError_debug err => None
       | TerminalError_debug _ _ => Some dunit
       | Success_debug x => Some x
       end.

  (* end hide *)

  (** Semantics of CAMP pattern, returning a presult *)
  Context (h:brand_relation_t).
  Context (constant_env:list(string*data)).

  Context (print_env:bool).
  
  Definition mk_err (desc:string) (p:pat) (bind:bindings) (it:data)
    := toString p ++ " failed" ++ desc ++ "." ++
                (if print_env
                 then "\n Current environment (env): "
                        ++ toString (drec bind)
                 else "") ++
                "\n Current scrutinee (it): "
                ++ toString it ++
                "\n".
  
  (* It is important to separate out the debug messages.
     Otherwise, they get reduced by proofs, which is painful *)
  Definition punop_err (p:pat) (bind:bindings) (it:data) (d:data) : string
    := (mk_err "" p bind it ++ " The operator's argument was: " ++ toString d ++ "\n").

  Definition binop_err (p:pat) (bind:bindings) (it:data) (d'₁ d'₂:data) : string
    := (mk_err "" p bind it ++ " The operator's first argument was: " ++ toString d'₁
               ++ "\n The operator's second argument was: " ++ toString d'₂
       ++ "\n").

  Definition pmap_err (p:pat) (bind:bindings) (it:data) : string
    := mk_err " because the scrutinee was not a collection" p bind it.

  Definition passert_err (p:pat) (bind:bindings) (it d:data) : string
    := mk_err " because the argument was not a boolean" p bind it
              ++ " The argument to passert was: " ++ toString d
               ++ "\n".

  Definition pletEnv_err (p:pat) (bind:bindings) (it d:data) : string
    := mk_err " because its first argument was not a record" p bind it
              ++ " The first argument to pletEnv was: " ++ toString d.

  Definition pleft_err (bind:bindings) (it:data) : string
    := mk_err " because the scrutinee was an incompatible type" pleft bind it.

  Definition pright_err (bind:bindings) (it:data) : string
      := mk_err " because the scrutinee was an incompatible type" pright bind it.

    Definition pgetconstant_err s (bind:bindings) (it:data) : string
      := mk_err (" because the given field (" ++ s ++
                ") is not a valid constant") (pgetconstant s) bind it
                ++ " The set of constants for this execution is: " ++
                (bracketString "{" (joinStrings "; " (domain constant_env)) "}")
                ++ "\n".

  Fixpoint interp_debug (loc:pat_src_path) (p:pat) (bind:bindings) (d:data) : presult_debug data
    := match p with
       | pconst d' => Success_debug (normalize_data h d')
       | punop op p₁ =>
         match interp_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug d' => 
             match fun_of_unaryop h op d' with
               | None => TerminalError_debug (punop_err (punop op p₁) bind d d')  loc
               | Some x => Success_debug x
             end
         end
       | pbinop op p₁ p₂ =>
         match interp_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug d'₁ =>
             match interp_debug (1::loc) p₂ bind d with
               | TerminalError_debug s loc' => TerminalError_debug s loc'
               | RecoverableError_debug s => RecoverableError_debug s
               | Success_debug d'₂ =>
                 match fun_of_binop h op d'₁ d'₂ with
                   | None => TerminalError_debug (binop_err (pbinop op p₁ p₂) bind d d'₁ d'₂)  loc
                   | Some x => Success_debug x
                 end
             end
         end
       | pmap p₁ =>
         match d with
         | dcoll l => liftpr_debug dcoll (gather_successes_debug (map (interp_debug (0::loc) p₁ bind) l))
         | _ => TerminalError_debug (pmap_err (pmap p₁) bind d) loc

         end
(* Adds some unexpected complexity since the pattern used to calculate the key may return match failure.
   How should we handle it? One option is to turn match failure into dunit, which possibly pushes part of the complexity
   down to the algebra. Not sure what the other
   options are ... - J
       | pgroupBy p₁ =>
         match d with
         | dcoll l => op2tpr "groupBy failed"
                             (lift dcoll
                                   (group_by_nested_eval_kv (fun x => pr2op (interp_debug p₁ bind x)) l))
         | _ => TerminalError_debug "pgroupBy evaluated when scrutinee is not a collection"
         end *)
       | passert p₁ =>
         match interp_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug d' =>
             match d' with
               | dbool true => Success_debug (drec nil)
               | dbool false => RecoverableError_debug "assertion failure"
               | _ => TerminalError_debug (passert_err (passert p₁) bind d d') loc
             end
         end
       | porElse p₁ p₂ =>
         match interp_debug (0::loc) p₁ bind d with
         | TerminalError_debug s loc' => TerminalError_debug s loc'
         | RecoverableError_debug _ => interp_debug (1::loc) p₂ bind d
         | Success_debug x => Success_debug x
         end
       | pit => Success_debug d
       | pletIt p₁ p₂ =>
         match interp_debug (0::loc) p₁ bind d with
         | TerminalError_debug s loc' => TerminalError_debug s loc'
         | RecoverableError_debug s => RecoverableError_debug s
         | Success_debug x => interp_debug (1::loc) p₂ bind x
         end
       | pgetconstant s =>
         match edot constant_env s with
           | Some x => Success_debug x
           | None => TerminalError_debug (pgetconstant_err s bind d) loc
         end
       | penv => Success_debug (drec bind)
       | pletEnv p₁ p₂ =>
         match interp_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug rd'₁ => 
             match rd'₁ with
               | drec d'₁ => match merge_bindings bind d'₁ with
                               | Some bind' => interp_debug (1::loc) p₂ bind' d
                               | None => RecoverableError_debug "bindings could not be unfied"
                             end
               | _ => TerminalError_debug (pletEnv_err (pletEnv p₁ p₂) bind d rd'₁) loc
             end
         end
       | pleft =>
         match d with
         | dleft d' => Success_debug d'
         | dright _ => RecoverableError_debug "pleft called on a pright"
         | _ => TerminalError_debug (pleft_err bind d) loc
         end
       | pright =>
         match d with
         | dright d' => Success_debug d'
         | dleft _ => RecoverableError_debug "pright called on a pleft"
         | _ => TerminalError_debug (pright_err bind d) loc
         end
       end.

      (* begin hide *)
  Arguments TerminalError {A}.
  Arguments RecoverableError {A}.
  Arguments Success {A} res.
  Arguments TerminalError_debug {A} s loc.
  Arguments RecoverableError_debug {A} s.
  Arguments Success_debug {A} res.
  (* end hide *)

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

  Theorem interp_debug_correct (loc:pat_src_path) (p:pat) (bind:bindings) (d:data) :
    presult_same
      (interp h constant_env p bind d)
      (interp_debug loc p bind d).
  Proof.
    revert loc bind d.
    pat_cases (induction p) Case; simpl; intros.
    - trivial.
    - apply bindpr_presult_same; [eauto | ]; intros.
      destruct (fun_of_unaryop h u x); simpl; trivial. 
    - apply bindpr_presult_same; [eauto | ]; intros.
      apply bindpr_presult_same; [eauto | ]; intros.
      destruct (fun_of_binop h b x x0); simpl; trivial.
    - destruct d; simpl; trivial.
      apply liftpr_presult_same.
      apply gather_successes_presult_same.
      rewrite <- Forall2_map.
      apply Forall2_refl; red; intros.
      apply IHp.
    - apply bindpr_presult_same; [eauto | ]; intros.
      destruct x; simpl; trivial.
      destruct b; simpl; trivial.
    - specialize (IHp1 (0::loc) bind d); red in IHp1.
      repeat match_destr_in IHp1; try tauto.
    - trivial.
    - apply bindpr_presult_same; [eauto | ]; intros.
      eauto.
    - unfold op2tpr. match_destr; simpl; trivial.
    - trivial.
    - apply bindpr_presult_same; [eauto | ]; intros.
      destruct x; simpl; trivial.
      destruct (merge_bindings bind l); simpl; trivial.
    - destruct d; simpl; trivial.
    - destruct d; simpl; trivial.
  Qed.

  End eval_debug.

  Lemma interp_const_sort h c p b d:
    interp h (rec_sort c) p b d = interp h c p b d.
  Proof.
    revert c b d.
    induction p; simpl; unfold olift, olift2; intros; trivial;
    try rewrite IHp; try rewrite IHp1; try rewrite IHp2; trivial.
    - match_destr.
      f_equal.
      f_equal.
      apply map_ext; intros.
      auto.
    - unfold bindpr.
      match_destr.
    - unfold edot.
      rewrite assoc_lookupr_drec_sort.
      trivial.
    - unfold bindpr. match_destr.
      destruct res; trivial.
      match_destr.
  Qed.

  (** Semantics of CAMP patterns, returning a presult *)
  Definition eval_pattern_debug (h:list(string*string)) (print_env:bool) (p:pat) (world:list data)
    : presult_debug data
    := interp_debug h (mkWorld world) print_env nil p nil dunit.

  Definition eval_pattern_res_to_string
             (h:list(string*string)) (print_env:bool) (p:pat) (world:list data)
    : string
    := print_presult_debug p
                           (interp_debug h
                                         (mkWorld world)
                                         print_env nil p nil dunit).

  Definition eval_pattern_res (h:list(string*string)) (p:pat) (world:list data)
    : presult data
    := interp h (mkWorld world) p nil dunit.

  Definition eval_pattern (h:list(string*string)) (p:pat) (world:list data)
    : option (list data)
    := match eval_pattern_res h p world with
       | Success _ l => Some (l::nil)
       | RecoverableError _ => Some nil
       | TerminalError _ => None
       end.

End Pattern.


(* begin hide *)
Arguments TerminalError {A}.
Arguments RecoverableError {A}.
Arguments Success {A} res.

Tactic Notation "pat_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "pconst"%string
  | Case_aux c "punop"%string
  | Case_aux c "pbinop"%string
  | Case_aux c "pmap"%string
(*| Case_aux c "pgroupBy"%string *)
  | Case_aux c "passert"%string
  | Case_aux c "porElse"%string
  | Case_aux c "pit"%string
  | Case_aux c "pletIt"%string
  | Case_aux c "pgetconstant"%string
  | Case_aux c "penv"%string
  | Case_aux c "pletEnv"%string
  | Case_aux c "pleft"%string
  | Case_aux c "pright"%string].
(* end hide *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
