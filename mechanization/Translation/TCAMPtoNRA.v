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

Require Import Bool.
Require Import String.
Require Import List.
Require Import Utils.
Require Import CommonSystem.
Require Import NRASystem.
Require Import CAMPSystem.
Require Import CAMPtoNRA.
Require Import Eqdep_dec.

Section TCAMPtoNRA.
  Local Open Scope string_scope.
  Local Open Scope list_scope.
  Local Open Scope nra_scope.

  (** Auxiliary definitions and lemmas for the types corresponding to the encoding of input/output(s) of Patterns in the NRA *)

  Context {m:basic_model}.

  Definition nra_context_type tbind tpid : rtype := 
    Rec Closed (("PBIND",tbind) :: ("PDATA",tpid) :: nil) (eq_refl _).

  Definition nra_wrap_a1_type tbind tpid : rtype := 
    Rec Closed (("PBIND",tbind) :: ("a1",tpid) :: nil) (eq_refl _).
  Local Open Scope camp_scope.

  Lemma ATnra_match {τc n τin τout} :
    n ▷ τin >=> τout ⊣ τc ->
    nra_match n ▷ τin >=> Coll τout ⊣ τc.
  Proof.
    intros; econstructor; eauto.
    econstructor.
  Qed.

  Lemma ATnra_match_inv {τc n τin τout} :
    nra_match n ▷ τin >=> τout ⊣ τc ->
    exists τout', τout = Coll τout' /\ n ▷ τin >=> τout' ⊣ τc.
  Proof.
    inversion 1; subst.
    inversion H2; subst.
    eauto.
  Qed.

  Lemma ATnra_match_invcoll {τc n τin τout} :
    nra_match n ▷ τin >=> Coll τout ⊣ τc ->
    n ▷ τin >=> τout ⊣ τc.
  Proof.
    intros. apply ATnra_match_inv in H; destruct H as [?[??]].
    inversion H; rtype_equalizer.
    subst. trivial.
  Qed.

  (** Auxiliary lemmas specific to some of the NRA expressions used in
  the translation *)

  Lemma ATdot {τc p s τin τ pf τout k}:
    p  ▷ τin >=> Rec k τ pf ⊣ τc ->
    tdot τ s = Some τout ->
    NRAUnop (OpDot s) p ▷ τin >=> τout ⊣ τc.
  Proof.
    intros.
    repeat econstructor; eauto.
  Qed.

  Lemma ATdot_inv {τc p s τin τout}:
    NRAUnop (OpDot s) p ▷ τin >=> τout ⊣ τc ->
    exists τ pf k,
      p  ▷ τin >=> Rec k τ pf ⊣ τc /\
      tdot τ s = Some τout.
  Proof.
    inversion 1; subst.
    inversion H2; subst.
    repeat econstructor; eauto.
  Qed.

  Lemma ATnra_data τc τ τin :
    nra_data ▷ nra_context_type τ τin >=> τin ⊣ τc.
  Proof.
    eapply ATdot.
    - econstructor.
    - reflexivity.
  Qed.

  Hint Constructors nra_type unary_op_type binary_op_type.
  Hint Resolve ATdot ATnra_match ATnra_data.
  
  (*  type rule for unnest_two.  Since it is a bit complicated,
       the type derivation is presented here, inline with the definition
   *)

  Lemma ATunnest_two (s1 s2:string) (op:nra) τc τin τ₁ pf1 τs τrem pf2 :
    op ▷ τin >=> (Coll (Rec Closed τ₁ pf1)) ⊣ τc ->
    tdot τ₁ s1 = Some (Coll τs) ->
    τrem = (rremove (rec_concat_sort τ₁ ((s2,τs)::nil)) s1) ->
    unnest_two s1 s2 op ▷ 
               τin >=> Coll (Rec Closed τrem pf2) ⊣ τc.
  Proof.
    intros; subst.
    econstructor; eauto.
    Grab Existential Variables.
    eauto.
    unfold rec_concat_sort; eauto.
  Qed.

  Lemma Coll_proj1 τ :
    proj1_sig (Coll τ) = Coll₀ (proj1_sig τ).
  Proof.
    reflexivity.
  Qed.

  Lemma ATunnest_two_inv {s1 s2:string} {op:nra} {τc τin τout} :
    unnest_two s1 s2 op ▷ τin >=> Coll τout ⊣ τc ->
    exists τ₁ pf1 τs pf2,
    op ▷ τin >=> (Coll (Rec Closed τ₁ pf1)) ⊣ τc /\
    tdot τ₁ s1 = Some (Coll τs) /\
    τout = Rec Closed (rremove (rec_concat_sort τ₁ ((s2,τs)::nil)) s1) pf2.
  Proof.
    Ltac ics H := inversion H; clear H; subst.
    intros H.
    ics H. rtype_equalizer. subst.
    ics H4. ics H1. ics H6. ics H5.
    rtype_equalizer. subst.
    ics H4. destruct τ₂0; simpl in *; try discriminate.
    subst.
    ics H5.  ics H3. ics H7. ics H8.
    ics H2; rtype_equalizer. ics H1. rtype_equalizer. subst.
    destruct τ₂; try discriminate.
    destruct τ₂; try discriminate.
    simpl in H.
    ics H; rtype_equalizer. subst.
    destruct p; simpl in *. 
    repeat econstructor; eauto.
  Qed.

  (** Main lemma for the type preservation of the translation. *)
  Lemma nra_of_camp_type_preserve' τc Γ pf p τin τout :
    camp_type τc Γ p τin τout ->
    nra_of_camp p ▷ (nra_context_type (Rec Closed Γ pf) τin) >=> Coll τout ⊣ τc.
  Proof.
    Hint Resolve data_type_drec_nil.
    revert τc Γ pf τin τout.
    induction p; simpl; inversion 1; subst.
    (* PTconst *)
    - eauto.
    (* PTunop *)
    - eauto. 
    (* PTbinop *)
    - econstructor.
      + eapply (@type_NRABinop m τc (Rec Closed (("a1", τ₂₁)::("a2", τ₂₂)::nil) (eq_refl _))); eauto.
      + econstructor; eauto.
    (* PTmap *)
    - econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      eapply ATunnest_two.
      + econstructor; eauto.
         econstructor; eauto.
         econstructor; eauto.
         eapply ATdot; eauto.
         * econstructor; eauto.
         * reflexivity.
      + reflexivity.
      + reflexivity.
    (* PTassert *)
    - repeat econstructor; eauto.
    (* PTorElse *)
    - eauto.
    (* PTit *)
    - eauto.
    (* PTletIt *)
    - econstructor; eauto.
      econstructor; eauto.
      eapply ATunnest_two.
      + econstructor; eauto.
         econstructor; eauto.
         econstructor; eauto.
         eapply ATdot; eauto.
         econstructor.
         reflexivity.
      + reflexivity.
      + reflexivity.
    (* PTgetconstant *)
    - repeat (econstructor; eauto).
    (* PTenv *)
    - rewrite (is_list_sorted_ext _ _ pf pf0).
      repeat (econstructor; eauto).
    (* PTletEnv *)
    - econstructor; eauto.
      econstructor; eauto.
      + assert (Γeq:Γ'' = rec_concat_sort Γ Γ')
                  by (unfold merge_bindings in *; 
                       destruct (Compat.compatible Γ Γ'); congruence).
           generalize (merge_bindings_sorted H4). subst. 
           intros.
           eapply ATunnest_two.
         * econstructor.
           2: {
           eapply ATunnest_two.
           econstructor; eauto. econstructor; eauto.
           econstructor. reflexivity. reflexivity.
           }
           simpl.
           econstructor; eauto.
           simpl.
           econstructor; eauto; try (
                                    econstructor; [|econstructor]; econstructor; reflexivity).
           econstructor; eauto.
           eapply type_NRABinop.
           eapply type_OpRecMerge_closed.
           eauto.
           econstructor; eauto.
           econstructor; eauto.
           unfold tdot, edot; simpl. eauto.
           econstructor; eauto.
           econstructor; eauto. reflexivity.
         * reflexivity.
         * reflexivity.
    (* PTEither *)
    - repeat (econstructor; eauto).
    (* PTEitherConcat *)
    - repeat (econstructor; eauto).
      Grab Existential Variables.
      eauto. eauto. eauto. eauto. eauto. 
      eauto. eauto. eauto. eauto. eauto. 
      eauto. eauto. eauto. eauto. eauto.
  Qed.

  Lemma nra_of_camp_type_preserve τc Γ pf p τin τout :
    camp_type τc Γ p τin τout ->
    nra_of_camp p ▷ (nra_context_type (Rec Closed Γ pf) τin) >=> Coll τout ⊣ τc.
  Proof.
    intros H.
    apply nra_of_camp_type_preserve'.
    trivial.
  Qed.

  (** Some corollaries of the main Lemma *)

  Lemma nra_of_camp_nra_of_camp_top p c τc τin τout :
    bindings_type c τc ->
    nra_of_camp p ▷ (nra_context_type (Rec Closed nil eq_refl) τin) >=> Coll τout ⊣ τc ->
    nra_of_camp_top p ▷ τin >=> Coll τout ⊣ τc.
  Proof.
    Hint Resolve normalize_normalizes.
    Hint Resolve normalize_preserves_type.
    intros.
    econstructor; [eauto | ].
    econstructor; [eauto | ].
    econstructor; [eauto | ].
    econstructor.
    - apply (type_OpRecConcat (τ₁:=("PBIND", (Rec Closed nil eq_refl))::nil) (τ₂:=(("PDATA",τin)::nil))).
      econstructor.
    - econstructor.
      + repeat (econstructor; eauto).
      + econstructor.
        simpl.
        * apply bindings_type_has_type.
          econstructor.
    - econstructor; [ | eauto 2].
      econstructor.
    Grab Existential Variables.
    eauto. eauto.
  Qed.
    
  Theorem nra_of_camp_top_type_preserve p c τc τin τout :
    bindings_type c τc ->
    camp_type τc nil p τin τout ->
    nra_of_camp_top p ▷ τin >=> Coll τout ⊣ τc.
  Proof.
    intros.
    eapply nra_of_camp_nra_of_camp_top; eauto.
    eapply nra_of_camp_type_preserve; eauto.
  Qed.

  Hint Constructors camp_type.

  (** Section dedicated to the reverse direction for type preservation *)

  Lemma ATaid_inv {τc τin τout} :
    NRAID ▷ τin >=> τout ⊣ τc -> τin = τout.
  Proof.
     inversion 1; congruence.
  Qed.

  Lemma UIP_refl_dec 
        {A:Type}
        (dec:forall x y:A, {x = y} + {x <> y}) 
        {x:A} 
        (p1:x = x) : p1 = eq_refl x.
  Proof.
    intros. apply (UIP_dec); auto.
  Qed.

  Ltac inverter := 
    match goal with
      | [H:Coll _ = Coll _ |- _] => inversion H; clear H
      | [H:unary_op_type OpBag _ _ |- _ ] => 
        inversion H; clear H; subst
      | [H:nra_context _ _ ▷ _ >=> _ ⊣ _ |- _ ] => unfold nra_context in H
      | [H:nra_double _ _ _ _ _ ▷ _ >=> _  ⊣ _|- _ ] => unfold nra_double in H
      | [H:nra_wrap_a1 _ ▷ _ >=> _ ⊣ _ |- _ ] => unfold nra_wrap_a1 in H
      | [H:nra_match _ ▷ _ >=> Coll _ ⊣ _ |- _] =>
        apply ATnra_match_invcoll in H
      | [H:nra_match _ ▷ _ >=> _ ⊣ _ |- _] =>
        apply ATnra_match_inv in H;
          destruct H as [? [??]]
      | [H:NRAUnop _ (OpDot _) _ ▷ _ >=> _ ⊣ _ |- _] =>
        apply ATdot_inv in H;
          destruct H as [? [? [??]]]
      | [H:unary_op_type (OpDot _) _ _ |- _ ] => inversion H; clear H
      | [H:unary_op_type OpFlatten _ _ |- _ ] => inversion H; clear H
      | [H:unary_op_type OpSingleton _ _ |- _ ] => inversion H; clear H
      | [H:unary_op_type (OpCast _) _ _ |- _ ] => inversion H; clear H
      | [H:unary_op_type (OpRec _) _ _ |- _ ] => inversion H; clear H
      | [H:binary_op_type OpRecConcat _ _ _ |- _ ] => inversion H; clear H
      | [H:binary_op_type OpRecMerge _ _ _ |- _ ] => inversion H; clear H
      | [H:NRAID ▷ _ >=> _ ⊣ _ |- _ ] => apply ATaid_inv in H
      | [H:nra_data ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:nra_fail ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRAMap _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRAEither _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRAEitherConcat _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRADefault _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRAApp _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRAProduct _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRASelect _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRABinop _ _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRAUnop _ _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:NRAConst _ ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:nra_bind ▷ _ >=> _ ⊣ _ |- _ ] => inversion H; clear H
      | [H:data_type _ (dcoll _) _ |- _ ] => inversion H; clear H
      | [H:Rec₀ _ _  = Rec₀ _ _ |- _ ] => inversion H; clear H
      | [H:(_,_)  = (_,_) |- _ ] => inversion H; clear H
      | [H:(map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) _)
           = 
           (map
              (fun x' : string * {τ₀' : rtype₀ | wf_rtype₀ τ₀' = true} =>
                 (fst x', proj1_sig (snd x'))) _) |- _ ] =>
        apply map_rtype_fequal in H; trivial
      | [H:Rec _ _ _ = Rec _ _ _ |- _ ] => generalize (Rec_inv H); clear H; intro H; try subst
      | [H:context [nil = map 
                            (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                               (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
      | [H:context [map 
                      (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                         (fst x, proj1_sig (snd x))) _ = nil] |- _] => apply map_eq_nil in H
                                                                                             
      | [H:context [(_::nil) = map 
                                 (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                    (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
                                                                                          
      | [H:context [map 
                      (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                         (fst x, proj1_sig (snd x))) _ = (_::nil) ] |- _] => apply map_eq_cons in H;
          destruct H as [? [? [? [??]]]]
      | [H:prod string
                (@sig rtype₀ (fun τ₀ : rtype₀ => @eq bool (wf_rtype₀ τ₀) true))
         |- _] =>
        destruct H
      | [H:unnest_two _ _ _ ▷ _ >=> Coll _ ⊣ _ |- _ ] =>
        apply ATunnest_two_inv in H; destruct H as [?[?[?[?[?[??]]]]]]
      | [H:proj1_sig _ = Coll₀ (proj1_sig _) |- _ ] =>
        rewrite <- Coll_proj1 in H; rtype_equalizer
      | [H:(@eq bool ?x ?x) |- _ ] => generalize (UIP_refl_dec bool_dec H); intro; subst H
      | [H:nra_context_type _ _ = Rec _ _ _ |- _ ] => unfold nra_context_type in H
      | [H:Coll₀ _ = Coll₀ _ |- _ ] => inversion H; clear H
      | [H:proj1_sig _ =
           Rec₀
             (map
                (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                   (fst x, proj1_sig (snd x))) _) |- _ ] 
        => apply Rec₀_eq_proj1_Rec in H; destruct H as [??]
    end; try rtype_equalizer; try subst; simpl in *; try inverter.
  
  Lemma nra_of_camp_type_form_output_weak τc p τin τout :
    nra_of_camp p ▷ τin >=> τout ⊣ τc ->
    exists τout',τout = Coll τout'.
  Proof.
    revert τin τout.
    induction p; simpl; intros; try inverter; eauto.
  Qed.

  Theorem nra_of_camp_type_form_output τc p τin τout :
    nra_of_camp p ▷ τin >=> τout ⊣ τc ->
    {τout' | τout = Coll τout'}.
  Proof.
    intros H.
    apply nra_of_camp_type_form_output_weak in H.
    destruct τout.
    destruct x;
      try solve [cut False; [intuition|destruct H; inversion H]].
    simpl in e. exists (exist _ x e).
    reflexivity.
  Qed.

  Lemma nra_of_camp_top_type_form_output_weak τc p τin τout :
    nra_of_camp_top p ▷ τin >=> τout ⊣ τc ->
    exists τout', τout = Coll τout'.
  Proof.
    unfold nra_of_camp_top; intros; inverter.
    eauto.
  Qed.

  Theorem nra_of_camp_top_type_form_output τc p τin τout :
    nra_of_camp_top p ▷ τin >=> τout ⊣ τc ->
    {τout' | τout = Coll τout'}.
  Proof.
    intros H.
    apply nra_of_camp_top_type_form_output_weak in H.
    destruct τout.
    destruct x;
      try solve [cut False; [intuition|destruct H; inversion H]].
    simpl in e. exists (exist _ x e).
    reflexivity.
  Qed.
  
  Ltac tdi := 
    repeat match goal with
             | [H:tdot ?l ?p = Some ?t |- _ ] 
               => progress (inversion H; clear H)
             | [H:context [rec_concat_sort ?ls1 ?ls2] |- _ ] 
               => unfold rec_concat_sort in H; simpl in H;
                  match type of H with
                    | context [rec_sort _ ] => fail 1
                    | _ => idtac
                  end
           end.

End TCAMPtoNRA.

