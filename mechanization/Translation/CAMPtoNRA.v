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
Require Import Omega.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRARuntime.
Require Import CAMPRuntime.
  
Section CAMPtoNRA.
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.

  (* Output encoding *)

  Definition lift_failure d :=
    match d with
      | TerminalError => None
      | RecoverableError => Some (dcoll nil)
      | Success d' => Some (dcoll (d'::nil))
    end.

  (** Translation from CAMP to NRA *)

  Fixpoint nra_of_camp (p:camp) : nra :=
    match p with
    | pconst d' => nra_match (NRAConst d')
    | punop uop p₁ => NRAMap (NRAUnop uop NRAID) (nra_of_camp p₁)
    | pbinop bop p₁ p₂ =>
      NRAMap (NRABinop bop (NRAUnop (OpDot "a1") NRAID) (NRAUnop (OpDot "a2") NRAID))
             (NRAProduct (NRAMap (NRAUnop (OpRec "a1") NRAID) (nra_of_camp p₁))
                         (NRAMap (NRAUnop (OpRec "a2") NRAID) (nra_of_camp p₂)))
    | pmap p₁ =>
      nra_match
        (NRAUnop OpFlatten
                 (NRAMap
                    (nra_of_camp p₁)
                    (unnest_two
                       "a1"
                       "PDATA"
                       (NRAUnop OpBag (nra_wrap_a1 (NRAUnop (OpDot "PDATA") NRAID))))))
    | passert p₁ => NRAMap (NRAConst (drec nil)) (NRASelect NRAID (nra_of_camp p₁))
    | porElse p₁ p₂ => NRADefault (nra_of_camp p₁) (nra_of_camp p₂)
    | pit => nra_match nra_data
    | pletIt p₁ p₂ =>
      NRAUnop OpFlatten
              (NRAMap (nra_of_camp p₂)
                      (unnest_two
                         "a1"
                         "PDATA"
                         (NRAUnop OpBag
                                  (nra_wrap_a1 (nra_of_camp p₁)))))
    | pgetConstant s => nra_match (NRAGetConstant s)
    | penv => nra_match nra_bind
    | pletEnv p₁ p₂ =>
      NRAUnop OpFlatten
              (NRAMap
                 (nra_of_camp p₂)
                 (unnest_two (* Needed because MergeConcat may fail so is a
                                collection which must be unnested *)
                    "PBIND1"
                    "PBIND"
                    (NRAMap (NRABinop OpRecConcat
                                      (NRAUnop (OpRec "PDATA") (NRAUnop (OpDot "PDATA") NRAID))
                                      (NRAUnop (OpRec "PBIND1") (NRABinop OpRecMerge
                                                                          (NRAUnop (OpDot "PBIND") NRAID)
                                                                          (NRAUnop (OpDot "PBIND1") NRAID))))
                            (unnest_two
                               "a1"
                               "PBIND1"
                               (NRAUnop OpBag
                                        (NRABinop OpRecConcat
                                                  NRAID
                                                  (NRAUnop (OpRec "a1") (nra_of_camp p₁))))))))
    | pleft =>
      NRAApp (NRAEither (nra_match NRAID) (nra_fail)) nra_data
    | pright =>
      NRAApp (NRAEither (nra_fail) (nra_match NRAID)) nra_data
    end.

  (** top level version sets up the appropriate input 
      (with an empty context) 
  *)

  Definition nra_of_camp_top p :=
    NRAUnop OpFlatten
          (NRAMap (nra_of_camp p)
                (NRAUnop OpBag
                       (nra_context (NRAConst (drec nil)) NRAID))).

  (** Auxiliary lemmas -- all used inside pmap proof *)

  Lemma lift_map_lift (l:list data) :
    lift_map (fun x : data => Some (drec (("PDATA", x) :: nil))) l =
    Some (map (fun x => (drec (("PDATA", x) :: nil))) l).
  Proof.
    induction l; simpl. reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma lift_map_lift2 bind (l l':list data):
    (lift_map
       (fun x : data =>
          match x with
            | drec r1 =>
              Some
                (drec
                   (rec_concat_sort
                      (("PBIND", drec bind)
                         :: ("a1", dcoll l') :: nil) r1))
            | _ => None
          end)
       (map (fun x : data => drec (("PDATA", x) :: nil)) l)) =
    Some (map (fun x :data => (drec
                   (rec_concat_sort
                      (("PBIND", drec bind)
                         :: ("a1", dcoll l') :: nil) (("PDATA", x) :: nil)))) l). 
  Proof.
    induction l; simpl.
    reflexivity.
    rewrite IHl.
    simpl.
    reflexivity.
  Qed.

  Lemma lift_map_lift3 bind (l l':list data):
    lift_map
      (fun x : data =>
         match x with
           | drec r => Some (drec (rremove r "a1"))
           | _ => None
         end)
      (map
         (fun x : data =>
            drec
              (rec_concat_sort
                 (("PBIND", drec bind)
                    :: ("a1", dcoll l') :: nil)
                 (("PDATA", x) :: nil))) l ++ nil)
    =
    Some (map (fun x : data =>
                 drec
                   (rec_concat_sort
                      (("PBIND", drec bind) :: nil)
                      (("PDATA", x) :: nil))) l ++ nil).
  Proof.
    induction l; simpl.
    reflexivity.
    simpl.
    rewrite IHl.
    simpl.
    reflexivity.
  Qed.

  Lemma oflatten_lift1 (l:option (list data)):
    (olift
       (fun d1 : data =>
          lift_oncoll (fun l0 : list data => lift dcoll (oflatten l0)) d1)
       (lift dcoll
             (lift (fun t' : list data => dcoll nil :: t') l))) =
     (olift
       (fun d1 : data =>
          lift_oncoll (fun l0 : list data => lift dcoll (oflatten l0)) d1)
       (lift dcoll l)).
  Proof.
    destruct l; try reflexivity.
    induction l; simpl; try reflexivity.
    simpl.
    unfold oflatten; simpl.
    assert (forall d, lift (fun t':list data => t') d = d).
    intros.
    destruct d; try reflexivity.
    rewrite H.
    reflexivity.
  Qed.

  (** Theorem 4.2: lemma of translation correctness for campterns *)

  Theorem camp_trans_correct {h:brand_relation_t} c p bind d:
    lift_failure (camp_eval h c p bind d) = nra_eval h c (nra_of_camp p) (nra_context_data (drec bind) d).
  Proof.
    revert d bind;
    camp_cases (induction p) Case; simpl; intros.
    - Case "pconst"%string.
      reflexivity.
    - Case "punop"%string.
      rewrite <- IHp; clear IHp; simpl.
      destruct (camp_eval h c p bind d); try reflexivity.
      simpl; destruct (unary_op_eval h u res); reflexivity.
    - Case "pbinop"%string.
      rewrite <- IHp1; rewrite <- IHp2; clear IHp1 IHp2.
      destruct (camp_eval h c p1 bind d); try reflexivity.
      destruct (camp_eval h c p2 bind d); try reflexivity.
      simpl; destruct (binary_op_eval h b res res0); reflexivity.
    - Case "pmap"%string.
      destruct d; try reflexivity.
      unfold omap_product in *; simpl.
      unfold oncoll_map_concat in *; simpl.
      rewrite lift_map_lift; simpl.
      unfold omap_concat in *; simpl.
      rewrite lift_map_lift2; simpl.
      rewrite lift_map_lift3; simpl.
      induction l; simpl; try reflexivity.
      unfold nra_context_data in IHp.
      assert ((rec_concat_sort (("PBIND", drec bind) :: nil)
                   (("PDATA", a) :: nil)) =
              ("PBIND", drec bind) :: ("PDATA", a) :: nil).
      reflexivity.
      rewrite H; clear H.
      rewrite <- (IHp a bind).
      clear IHp.
      destruct (camp_eval h c p bind a); try reflexivity; simpl.
      rewrite IHl; simpl.
      rewrite oflatten_lift1.
      reflexivity.
      revert IHl.
      destruct ((lift_map (nra_eval h c (nra_of_camp p))
              (map
                 (fun x : data =>
                  drec
                    (rec_concat_sort (("PBIND", drec bind) :: nil)
                       (("PDATA", x) :: nil))) l ++ nil))).
      * simpl. intros.
        unfold oflatten in *.
        simpl.
        revert IHl.
        destruct ((lift_flat_map
              (fun x : data =>
               match x with
               | dcoll y => Some y
               | _ => None
               end) l0)); simpl; intros;
        revert IHl;
        destruct (gather_successes (map (camp_eval h c p bind) l)); intros; simpl in *; try reflexivity; congruence.
      * simpl.
        destruct ((gather_successes (map (camp_eval h c p bind) l))); simpl; intros.
        reflexivity.
        congruence.
        congruence.
    - Case "passert"%string.
      rewrite <- IHp; clear IHp; simpl.
      destruct (camp_eval h c p bind d); try reflexivity.
      destruct res; try reflexivity; simpl.
      destruct b; reflexivity.
    - Case "porElse"%string.
      rewrite <- IHp1; clear IHp1; simpl.
      destruct (camp_eval h c p1 bind d); simpl; auto.
    - Case "pit"%string.
      reflexivity.
    - Case "pletIt"%string.
      rewrite <- IHp1; clear IHp1; simpl.
      destruct (camp_eval h c p1 bind d); try reflexivity.
      simpl.
      specialize (IHp2 res).
      unfold nra_context_data in IHp2.
      rewrite <- IHp2; clear IHp2.
      destruct (camp_eval h c p2 bind res); reflexivity.      
    - Case "pgetConstant"%string.
      destruct (edot c s); simpl; trivial.
    - Case "penv"%string.
      eauto. 
    - Case "pletEnv"%string.
      rewrite <- IHp1; clear IHp1; simpl.
      destruct (camp_eval h c p1 bind d); try reflexivity.
      destruct res; try reflexivity.
      simpl.
      destruct (merge_bindings bind l); try reflexivity.
      specialize (IHp2 d l0).
      unfold nra_context_data in *.
      simpl.
      rewrite <- IHp2; clear IHp2; simpl.
      destruct (camp_eval h c p2 l0 d); try reflexivity.
    - Case "pleft"%string.
      unfold lift_failure. destruct d; simpl; trivial.
    - Case "pright"%string.
      unfold lift_failure. destruct d; simpl; trivial.
  Qed.

  Lemma camp_trans_yields_coll {h:brand_relation_t} c p d d0:
    Forall (fun x => data_normalized h (snd x)) c ->
    nra_eval h c (nra_of_camp p) d = Some d0 ->
    {x | d0 = dcoll x}.
  Proof.
    Ltac findcol := 
      repeat match goal with
        | [H:context [ olift _ ?x] |- _ ] => 
          (case_eq x;  [intros ?|idtac]; intros eq; rewrite eq in H;
           simpl in *; try discriminate)
        | [H:context [ olift2 _ ?x ?y] |- _ ] => 
          (case_eq x; 
           [intros ?|idtac]; intros eq; rewrite eq in H;
           simpl in *; try discriminate);
            (case_eq y; 
             [intros ?|idtac]; intros eq2; rewrite eq2 in H;
             simpl in *; try discriminate)
        | [H:lift_oncoll _ ?d = Some _ |- _] => 
          destruct d; simpl in *; try discriminate
        | [H:lift _ _ = Some _ |- _ ] =>
          apply some_lift in H; destruct H; try subst
        | [H:Some _ = Some _ |- _ ] => inversion H; clear H; try subst
      end; eauto.
    revert d d0; induction p; simpl; intros; try findcol.
    destruct (IHp1 _ _ H eq). subst.
    destruct x; findcol.
    destruct d; try congruence.
    destruct (edot l "PDATA"); try congruence.
    findcol.
    destruct d1; try congruence;
    [ exists (d1::nil); congruence | exists (nil); congruence].
    destruct d1; try congruence;
    [ exists nil; congruence | exists (d1::nil); congruence].
  Qed.

  Lemma camp_trans_top_nra_context {h:brand_relation_t} c p d:
    Forall (fun x => data_normalized h (snd x)) c ->
    nra_eval h c (nra_of_camp_top p) d 
    = nra_eval h c (nra_of_camp p) (nra_context_data (drec nil) d).
  Proof.
    simpl.
    unfold olift, nra_context_data; intros; trivial.
    case_eq (h ⊢ (nra_of_camp p) @ₐ (drec (("PBIND", drec nil) :: ("PDATA", d) :: nil)) ⊣ c); simpl; trivial; intros.
    unfold oflatten.
    simpl.
    apply camp_trans_yields_coll in H0; trivial.
    destruct H0; subst; simpl.
    rewrite app_nil_r.
    trivial.
  Qed.

  Lemma camp_trans_top_correct {h:brand_relation_t} c p d:
    Forall (fun x => data_normalized h (snd x)) c ->
    lift_failure (camp_eval h c p nil d) = nra_eval h c (nra_of_camp_top p) d.
  Proof.
    intros.
    rewrite camp_trans_top_nra_context by trivial.
    apply camp_trans_correct.
  Qed.

  (* Wrapping the error on the NRA side might be a little nicer, notably for later
     top-level proofs *)

  Definition lift_camp_failure (d : option data) :=
    match d with
      | Some (dcoll nil) => RecoverableError
      | Some (dcoll (l::nil)) => Success l
      | _ => TerminalError
    end.

  Lemma camp_trans_correct_r {h:brand_relation_t} c p bind d:
      camp_eval h c p bind d =
      lift_camp_failure (nra_eval h c (nra_of_camp p) (nra_context_data (drec bind) d)).
  Proof.
    rewrite <- camp_trans_correct.
    destruct (camp_eval h c p bind d); intros; simpl; reflexivity.
  Qed.

  Lemma camp_trans_top_correct_r {h:brand_relation_t} c p d:
    Forall (fun x => data_normalized h (snd x)) c ->
      camp_eval h c p nil d =
      lift_camp_failure (nra_eval h c (nra_of_camp_top p) d).
  Proof.
    intros.
    rewrite <- camp_trans_top_correct by trivial.
    destruct (camp_eval h c p nil d); intros; simpl; eauto.
  Qed.

  Section size.
    (** Proof showing linear size translation *)
    Lemma camp_trans_size p :
      nra_size (nra_of_camp p) <= 41 * camp_size p.
    Proof.
      induction p; simpl; omega.
    Qed.

  End size.

  Section sugar.
    (* Mapping to NRA for the built-in operators *)
    (* and *)
  
    Definition nra_of_pand (p1 p2:camp) : nra :=
      nra_of_camp (pand p1 p2).

    Definition nra_for_pand (q1 q2:nra) : nra :=
      (♯flatten(χ⟨q2
                 ⟩( unnest_two "PBIND1" "PBIND"
                               (χ⟨‵[| ("PDATA", (ID) · "PDATA")|]
                                   ⊕ ‵[| ("PBIND1", (ID) · "PBIND" ⊗ (ID) · "PBIND1")|]
                                 ⟩( unnest_two "a1" "PBIND1"
                                               (‵{|ID
                                                     ⊕ ‵[| ("a1",
                                                            χ⟨‵[||] ⟩( σ⟨ID ⟩( q1)))|]|}))))))%nra.


    Lemma nra_of_pand_works (p1 p2:camp) :
      nra_of_camp (pand p1 p2) = nra_for_pand (nra_of_camp p1) (nra_of_camp p2).
    Proof.
      simpl.
      reflexivity.
    Qed.
  
    (* WW *)
    
    Definition nra_of_WW (p:camp) :=
      nra_of_camp (WW p).

  End sugar.

  Section Top.
    Context (h:brand_relation_t).

    Definition camp_to_nra_top (q:camp) : nra :=
      NRAApp (nra_of_camp q) (nra_context (NRAConst (drec nil)) (NRAConst dunit)).

    Theorem camp_to_nra_top_correct :
      forall q:camp, forall global_env:bindings,
          camp_eval_top h q global_env =
          nra_eval_top h (camp_to_nra_top q) global_env.
    Proof.
      intros.
      unfold camp_eval_top.
      unfold nra_eval_top.
      unfold camp_to_nra_top.
      unfold presult_to_result.
      unfold camp_eval_top_to_presult.
      generalize (@camp_trans_correct h (rec_sort global_env) q nil dunit); intros.
      unfold lift_failure in H.
      destruct (camp_eval h (rec_sort global_env) q nil dunit);
      rewrite H;
      simpl;
      unfold nra_context_data in *; reflexivity.
    Qed.
      
  End Top.
  
End CAMPtoNRA.

