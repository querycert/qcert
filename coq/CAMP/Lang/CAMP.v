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

(** CAMP is a small calculus for pattern matching. Its purpose is to
  capture the semantics of rules languages that rely on the ability to
  recover from match failure. *)

(** Two distinct evaluation functions for CAMP are defined. The first
  is a standard evaluation function and serves as semantic
  definition. The second is equivalent but maintains a trace of the
  evaluation for debugging purposes. *)
  
(** Summary:
- Language: CAMP (Calculus for Aggregating Matching Patterns)
- Based on: "A Pattern Calculus for Rule Languages:
  Expressiveness, Compilation, and Mechanization" Avraham
  Shinnar, Jérôme Siméon, and Martin Hirzel. ECOOP'2015.
- URL: http://drops.dagstuhl.de/opus/volltexte/2015/5237/
- Languages translating to CAMP: TechRule, DesignRule, CAMPRule, cNNRC
- Languages translating from CAMP: NRA, cNRAEnv, NRAEnv
*)
  
Require Import String.
Require Import List.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonRuntime.
Require Import CAMPUtil.
  
Section CAMP.
  Local Open Scope string.

  Context {fruntime:foreign_runtime}.

  (** * Abstract Syntax Tree *)

  (** CAMP patterns are pure expressions. They match against a current
  value in the context of an environment. The environment has a
  globale component which is static, and a local component which can
  be modified in the course of evaluation. *)

  (** Operations include: pmap, a functional map which skips match
  failure; passert, which turns match failure into a terminal failure,
  and porElse which allows to continue to a new pattern in case of
  match failure. *)

  (** Compared to the published material, three new operators are
  added: pgetConstant which accesses the global environment, pleft and
  pright which support pattern matching against choice values. *)
  
  Inductive camp : Set :=
  | pconst : data -> camp                  (**r Constant value *)
  | punop : unary_op -> camp -> camp        (**r Unary operators *)
  | pbinop : binary_op -> camp -> camp -> camp (**r Binary operators *)
  | pmap : camp -> camp                    (**r Functional map *)
  | passert : camp -> camp                 (**r Assert pattern-matching success *)
  | porElse : camp -> camp -> camp         (**r Recover from failure *)
  | pit : camp                             (**r Current value being matched *)
  | pletIt : camp -> camp -> camp          (**r Set the current value *)
  | pgetConstant : string -> camp          (**r Access to a global variable *)
  | penv : camp                            (**r Current environment *)
  | pletEnv : camp -> camp -> camp         (**r Add bindings to the environment *)
  | pleft : camp                           (**r Matches if the value is a left choice *)
  | pright : camp.                         (**r Matches if the value is a right choice *)

  (* begin hide *)
  Tactic Notation "camp_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "pconst"%string
    | Case_aux c "punop"%string
    | Case_aux c "pbinop"%string
    | Case_aux c "pmap"%string
    | Case_aux c "passert"%string
    | Case_aux c "porElse"%string
    | Case_aux c "pit"%string
    | Case_aux c "pletIt"%string
    | Case_aux c "pgetConstant"%string
    | Case_aux c "penv"%string
    | Case_aux c "pletEnv"%string
    | Case_aux c "pleft"%string
    | Case_aux c "pright"%string].
  (* end hide *)

  (** Equality between two CAMP patterns is decidable. *)
  
  Global Instance camp_eqdec : EqDec camp eq.
  Proof.
    change (forall x y : camp, {x = y} + {x <> y}).
    decide equality.
    apply data_eqdec.
    apply unary_op_eqdec.
    apply binary_op_eqdec.
    apply string_dec.
  Qed.

  (** * Evaluation Semantics *)
  
  (** Evaluation takes a camp pattern, a global environment, a local
    environment and a current value. It returns a presult which can be
    either a successful evaluation holding a value, a match failure,
    or a terminal failure. *)

  (** The external context for evaluation includes a brand relation,
    and a global environment. *)
  
  Section Evaluation.
    Context (h:brand_relation_t).
    Context (constant_env:bindings).

    Fixpoint camp_eval (p:camp) (bind:bindings) (d:data) : presult data
      := match p with
         | pconst d' => Success (normalize_data h d')
         | punop op p₁ => bindpr (camp_eval p₁ bind d)
                                 (fun d' => (op2tpr (unary_op_eval h op d')))
         | pbinop op p₁ p₂ => 
           bindpr (camp_eval p₁ bind d)
                  (fun d'₁ => 
                     bindpr (camp_eval p₂ bind d)
                            (fun d'₂ =>  (op2tpr (binary_op_eval h op d'₁ d'₂))))
         | pmap p₁ =>
           match d with
           | dcoll l => liftpr dcoll (gather_successes (map (camp_eval p₁ bind) l))
           | _ => TerminalError
           end
         | passert p₁ =>
           bindpr (camp_eval p₁ bind d)
                  (fun d' => match d' with
                             | dbool true => Success (drec nil)
                             | dbool false => RecoverableError
                             | _ => TerminalError 
                             end)
         | porElse p₁ p₂ =>
           match camp_eval p₁ bind d with
           | TerminalError => TerminalError
           | RecoverableError => camp_eval p₂ bind d
           | Success x => Success x
           end
         | pit => Success d
         | pletIt p₁ p₂ =>
           bindpr (camp_eval p₁ bind d) (camp_eval p₂ bind)
         | pgetConstant s => op2tpr (edot constant_env s)
         | penv => Success (drec bind)
         | pletEnv p₁ p₂ =>
           bindpr (camp_eval p₁ bind d)
                  (fun rd'₁ => match rd'₁ with
                               | drec d'₁ => match merge_bindings bind d'₁ with
                                             | Some bind' => camp_eval p₂ bind' d
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

  End Evaluation.

  (** * Pretty Printing *)

  (** Evaluation traces rely on printing support for CAMP's abstract syntax. *)
    
  Global Instance ToString_camp : ToString camp
    := { toString :=
           fix toStringp (p:camp) : string :=
             match p with
             | pconst d => "(pconst " ++ toString d ++ ")"
             | punop u p1 => "(punop " ++ toString u ++ " " ++ toStringp p1 ++ ")"
             | pbinop b p1 p2 => "(pbinop " ++ toString b ++ " " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
             | pmap p1 => "(pmap " ++ toStringp p1 ++ ")"
             | passert p1 => "(passert " ++ toStringp p1 ++ ")"
             | porElse p1 p2 => "(porElse " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
             | pit  => "pit"
             | pletIt p1 p2 => "(pletIt " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
             | pgetConstant s => "(pgetConstant " ++ s ++ ")"
             | penv => "penv"
             | pletEnv p1 p2 => "(pletEnv " ++ toStringp p1++ " " ++ toStringp p2 ++ ")"
             | pleft => "pleft"
             | pright => "pright"
             end
       }.
  
  Fixpoint toString_camp_with_path (p:camp) (loc:camp_src_path) :=
    match loc with
    | nil => bracketString "<<<"  (toString p) ">>>"
    | pos::loc' =>
      match p with
      | pconst d => "(pconst " ++ toString d ++ ")"
      | punop u p1 => "(punop " ++ toString u ++ " " ++
                                toString_camp_with_path p1 loc' ++ ")"
      | pbinop b p1 p2 => "(pbinop "
                            ++ toString b ++ " " ++
                            (if pos == 0
                             then toString_camp_with_path p1 loc'
                             else toString p1)
                            ++ " " ++
                            (if pos == 1
                             then toString_camp_with_path p2 loc'
                             else toString p2) ++ ")"
      | pmap p1 => "(pmap " ++ toString_camp_with_path p1 loc' ++ ")"
      | passert p1 => "(passert " ++ toString_camp_with_path p1 loc' ++ ")"
      | porElse p1 p2 => "(porElse " ++
                                     (if pos == 0
                                      then toString_camp_with_path p1 loc'
                                      else toString p1)
                                     ++ " " ++
                                     (if pos == 1
                                      then toString_camp_with_path p2 loc'
                                      else toString p2) ++ ")"
      | pit  => "pit"
      | pletIt p1 p2 => "(pletIt " ++
                                   (if pos == 0
                                    then toString_camp_with_path p1 loc'
                                    else toString p1)
                                   ++ " " ++
                                   (if pos == 1
                                    then toString_camp_with_path p2 loc'
                                    else toString p2) ++ ")"
      | pgetConstant s => "(pgetConstant " ++ s ++ ")"
      | penv => "penv"
      | pletEnv p1 p2 => "(pletEnv " ++ 
                                     (if pos == 0
                                      then toString_camp_with_path p1 loc'
                                      else toString p1)
                                     ++ " " ++
                                     (if pos == 1
                                      then toString_camp_with_path p2 loc'
                                      else toString p2) ++ ")"
                                     
      | pleft => "pleft"
      | pright => "pright"
      end
    end.
    
  (** * Traced Evaluation *)
  
  (** An alternative version of the compiler that keeps debug
     information. While this forces some code duplication, this is
     mitigated by the fact that the evaluation code is relatively
     small and simple. *)

  (** The context is the same as for default evaluation, with an
  additional printing flag. *)

  Section EvaluationDebug.
    Context (h:brand_relation_t).
    Context (constant_env:list(string*data)).
    Context (print_env:bool).

    (** The following functions are used to produce error messages. *)
    
    Definition mk_err (desc:string) (p:camp) (bind:bindings) (it:data)
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
    Definition punop_err (p:camp) (bind:bindings) (it:data) (d:data) : string
      := (mk_err "" p bind it ++ " The operator's argument was: " ++ toString d ++ "\n").
    
    Definition binop_err (p:camp) (bind:bindings) (it:data) (d'₁ d'₂:data) : string
      := (mk_err "" p bind it ++ " The operator's first argument was: " ++ toString d'₁
                 ++ "\n The operator's second argument was: " ++ toString d'₂
                 ++ "\n").

    Definition pmap_err (p:camp) (bind:bindings) (it:data) : string
      := mk_err " because the scrutinee was not a collection" p bind it.

    Definition passert_err (p:camp) (bind:bindings) (it d:data) : string
      := mk_err " because the argument was not a boolean" p bind it
                ++ " The argument to passert was: " ++ toString d
                ++ "\n".
    
    Definition pletEnv_err (p:camp) (bind:bindings) (it d:data) : string
      := mk_err " because its first argument was not a record" p bind it
                ++ " The first argument to pletEnv was: " ++ toString d.

    Definition pleft_err (bind:bindings) (it:data) : string
      := mk_err " because the scrutinee was an incompatible type" pleft bind it.
    
    Definition pright_err (bind:bindings) (it:data) : string
      := mk_err " because the scrutinee was an incompatible type" pright bind it.
    
    Definition pgetConstant_err s (bind:bindings) (it:data) : string
      := mk_err (" because the given field (" ++ s ++
                                              ") is not a valid constant") (pgetConstant s) bind it
                ++ " The set of constants for this execution is: " ++
                (bracketString "{" (String.concat "; " (domain constant_env)) "}")
                ++ "\n".

    (** The alternative traced evaluation is defined as follows. *)
    
    Fixpoint camp_eval_debug (loc:camp_src_path) (p:camp) (bind:bindings) (d:data) : presult_debug data
      := match p with
         | pconst d' => Success_debug (normalize_data h d')
         | punop op p₁ =>
           match camp_eval_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug d' => 
             match unary_op_eval h op d' with
             | None => TerminalError_debug (punop_err (punop op p₁) bind d d')  loc
             | Some x => Success_debug x
             end
           end
         | pbinop op p₁ p₂ =>
           match camp_eval_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug d'₁ =>
             match camp_eval_debug (1::loc) p₂ bind d with
             | TerminalError_debug s loc' => TerminalError_debug s loc'
             | RecoverableError_debug s => RecoverableError_debug s
             | Success_debug d'₂ =>
               match binary_op_eval h op d'₁ d'₂ with
               | None => TerminalError_debug (binop_err (pbinop op p₁ p₂) bind d d'₁ d'₂)  loc
               | Some x => Success_debug x
               end
             end
           end
         | pmap p₁ =>
           match d with
           | dcoll l => liftpr_debug dcoll (gather_successes_debug (map (camp_eval_debug (0::loc) p₁ bind) l))
           | _ => TerminalError_debug (pmap_err (pmap p₁) bind d) loc
           end
         | passert p₁ =>
           match camp_eval_debug (0::loc) p₁ bind d with
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
           match camp_eval_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug _ => camp_eval_debug (1::loc) p₂ bind d
           | Success_debug x => Success_debug x
           end
         | pit => Success_debug d
         | pletIt p₁ p₂ =>
           match camp_eval_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug x => camp_eval_debug (1::loc) p₂ bind x
           end
         | pgetConstant s =>
           match edot constant_env s with
           | Some x => Success_debug x
           | None => TerminalError_debug (pgetConstant_err s bind d) loc
           end
         | penv => Success_debug (drec bind)
         | pletEnv p₁ p₂ =>
           match camp_eval_debug (0::loc) p₁ bind d with
           | TerminalError_debug s loc' => TerminalError_debug s loc'
           | RecoverableError_debug s => RecoverableError_debug s
           | Success_debug rd'₁ => 
             match rd'₁ with
             | drec d'₁ => match merge_bindings bind d'₁ with
                           | Some bind' => camp_eval_debug (1::loc) p₂ bind' d
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

    (** The following theorem states that traced evaluation is equivalent to regular evaluation. *)
    
    Theorem camp_eval_debug_correct (loc:camp_src_path) (p:camp) (bind:bindings) (d:data) :
      presult_same
        (camp_eval h constant_env p bind d)
        (camp_eval_debug loc p bind d).
    Proof.
      revert loc bind d.
      camp_cases (induction p) Case; simpl; intros.
      - trivial.
      - apply bindpr_presult_same; [eauto | ]; intros.
        destruct (unary_op_eval h u x); simpl; trivial. 
      - apply bindpr_presult_same; [eauto | ]; intros.
        apply bindpr_presult_same; [eauto | ]; intros.
        destruct (binary_op_eval h b x x0); simpl; trivial.
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

  End EvaluationDebug.

  (** * Toplevel *)
  
  (** Top-level evaluation functions are used externally by the Q*cert
  compiler. They take a CAMP pattern and a global environment as
  input. The initial local environment is set to an empty record, and
  the initial current value to unit. *)

  (** The result of evaluation is lifted back from presult to and
  optional value for consistency with evaluation functions for the
  other intermediate languages. *)
  
  Section Top.
    Context (h:brand_relation_t).

    Definition presult_to_result (pr:presult data) : option data :=
      match pr with
      | Success l => Some (dcoll (l::nil))
      | RecoverableError => Some (dcoll nil)
      | TerminalError => None
      end.

    Definition camp_eval_top_to_presult (q:camp) (global_env:bindings) : presult data :=
      camp_eval h (rec_sort global_env) q nil dunit.

    (** The main top-level evaluation function for CAMP is as follows. *)
    
    Definition camp_eval_top (q:camp) (global_env:bindings) : option data :=
      presult_to_result (camp_eval_top_to_presult q global_env).

    Definition presult_to_result_debug (pr:presult_debug data) : option data :=
      match pr with
      | Success_debug l => Some (dcoll (l::nil))
      | RecoverableError_debug _ => Some (dcoll nil)
      | TerminalError_debug _ _ => None
      end.

    Definition pr2op_debug (pr:presult_debug data) : option data :=
      match pr with
      | Success_debug l => Some (dsome l)
      | RecoverableError_debug _ => Some dnone
      | TerminalError_debug _ _ => None
      end.

    Definition camp_eval_top_debug_to_presult_debug
               (debug:bool) (q:camp) (global_env:bindings) : presult_debug data :=
      camp_eval_debug h (rec_sort global_env) debug nil q nil dunit.

    Theorem camp_eval_top_debug_correct (debug:bool) (p:camp) (global_env:bindings) (d:data) :
      presult_same
        (camp_eval_top_to_presult p global_env)
        (camp_eval_top_debug_to_presult_debug debug p global_env).
    Proof.
      unfold camp_eval_top_to_presult.
      unfold camp_eval_top_debug_to_presult_debug.
      apply camp_eval_debug_correct.
    Qed.
    
    Definition camp_eval_top_debug_to_data
               (debug:bool) (q:camp) (global_env:bindings) : option data :=
      presult_to_result_debug (camp_eval_debug h (rec_sort global_env) debug nil q nil dunit).

    (** The main top-level traced evaluation function for CAMP is as follows. *)
    
    Definition camp_eval_top_debug (debug:bool) (q:camp) (global_env:bindings) : string :=
      print_presult_debug q toString_camp_with_path
                          (camp_eval_top_debug_to_presult_debug debug q global_env).
  End Top.

End CAMP.

(* begin hide *)
Tactic Notation "camp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "pconst"%string
  | Case_aux c "punop"%string
  | Case_aux c "pbinop"%string
  | Case_aux c "pmap"%string
  | Case_aux c "passert"%string
  | Case_aux c "porElse"%string
  | Case_aux c "pit"%string
  | Case_aux c "pletIt"%string
  | Case_aux c "pgetConstant"%string
  | Case_aux c "penv"%string
  | Case_aux c "pletEnv"%string
  | Case_aux c "pleft"%string
  | Case_aux c "pright"%string].
(* end hide *)

