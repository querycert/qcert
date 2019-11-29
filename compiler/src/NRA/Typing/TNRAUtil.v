(*
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
Require Import Compare_dec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import NRA.
Require Import NRASugar.
Require Import NRAExt.
Require Import TNRA.

Section TNRAUtil.
  Context {m:basic_model}.
  Context (τconstants:tbindings).

  Local Open Scope nra_scope.

  Lemma ATdot {p s τc τin τ pf τout} :
    p  ▷ τin >=> Rec Closed τ pf ⊣ τc ->
    tdot τ s = Some τout ->
    NRAUnop (OpDot s) p ▷ τin >=> τout ⊣ τc.
  Proof.
    intros.
    repeat econstructor; eauto.
  Qed.

  Lemma ATdot_inv {p s τc τin τout}:
    NRAUnop (OpDot s) p ▷ τin >=> τout ⊣ τc ->
    exists τ pf k,
      p  ▷ τin >=> Rec k τ pf ⊣ τc /\
      tdot τ s = Some τout.
  Proof.
    inversion 1; subst.
    inversion H2; subst.
    repeat econstructor; eauto.
  Qed.
  (** Auxiliary lemmas specific to some of the NRA expressions used in
  the translation *)

  Definition nra_context_type tbind tpid : rtype := 
    Rec Closed (("PBIND"%string,tbind) :: ("PDATA"%string,tpid) :: nil) (eq_refl _).

  Lemma ATnra_data τc τ τin :
    nra_data ▷ nra_context_type τ τin >=> τin ⊣ τc.
  Proof.
    eapply ATdot.
    - econstructor.
    - reflexivity.
  Qed.

  Lemma ATnra_data_inv' k τc τ τin pf τout:
      nra_data ▷ Rec k [("PBIND"%string, τ); ("PDATA"%string, τin)] pf >=> τout ⊣ τc ->
      τin = τout.
  Proof.
    unfold nra_data.
    intros H.
    inversion H; clear H; subst.
    inversion H2; clear H2; subst.
    inversion H5; clear H5; subst.
    destruct τ'; inversion H3; clear H3; subst.
    destruct τ'; inversion H4; clear H4; subst.
    destruct τ'; inversion H6; clear H6; subst.
    rtype_equalizer. subst.
    destruct p; destruct p0; simpl in *; subst.
    inversion H0; trivial.
  Qed.
    
  Lemma ATnra_data_inv τc τ τin τout:
    nra_data ▷ nra_context_type τ τin >=> τout ⊣ τc ->
    τin = τout.
  Proof.
    unfold nra_context_type.
    apply ATnra_data_inv'.
  Qed.

  Hint Constructors nra_type unary_op_type binary_op_type.
  Hint Resolve ATdot ATnra_data.
  (*  type rule for unnest_two.  Since it is a bit complicated,
       the type derivation is presented here, inline with the definition
   *)
(*
  Definition unnest_two s1 s2 op :=
    (* τin >=> (Coll (rremove (rec_concat_sort τ₁ ("s2",τs)) s1) *)
    NRAMap 
         (* (rec_concat_sort τ₁ ("s2",τs) >=> (rremove (rec_concat_sort τ₁ ("s2",τs)) s1) *)
         ((NRAUnop (OpRecRemove s1)) NRAID)
         (* τin >=>  (Coll (rec_concat_sort τ₁ ("s2",τs)) *)
         (NRAMapProduct 
            (*  (Rec τ₁ pf1) >=> (Coll ("s2",τs) *)
            (NRAMap 
               (* τs >=> ("s2",τs) *)
               ((NRAUnop (NRARec s2)) NRAID)
               (* (Rec τ₁ pf1) >=> Coll τs , where tdot τ₁ s1 = Coll τs *)
               ((NRUnop (OpDot s1)) NRAID)) 
            (* τin >=> (Coll (Rec τ₁ pf1)) *)
            op).
 *)
  
  Lemma ATunnest_two (s1 s2:string) (op:NRA.nra) τc τin τ₁ pf1 τs τrem pf2 :
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
    unfold rec_concat_sort. eauto.
  Qed.

  Lemma ATRecEither s τc τl τr pf1 pf2:
    nra_type τc (NRARecEither s) (Either τl τr)
             (Either
                (Rec Closed ((s,τl)::nil) pf1)
                (Rec Closed ((s,τr)::nil) pf2)).
  Proof.
    econstructor; eauto.
  Qed.
  
Ltac nra_inverter := 
  match goal with
  | [H:Coll _ = Coll _ |- _] => inversion H; clear H
  | [H: `?τ₁ = Coll₀ (`?τ₂) |- _] => rewrite (Coll_right_inv τ₁ τ₂) in H; subst
  | [H:  Coll₀ (`?τ₂) = `?τ₁ |- _] => symmetry in H
  (* Note: do not generalize too hastily on unary_op/binary_op constructors *)
  | [H:@nra_type _ _ NRAID _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAMap _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAMapProduct _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAEither _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAEitherConcat _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRARecEither _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRADefault _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAApp _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAProduct _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRASelect _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAUnop _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRABinop _ _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAConst _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (nra_data) _ _ |- _ ] => apply ATnra_data_inv' in H
  | [H:@nra_type _ _ (nra_data) (nra_context_type _ _) _ |- _ ] => apply ATnra_data_inv in H
  | [H: (_,_)  = (_,_) |- _ ] => inversion H; clear H
  | [H: map (fun x2 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
               (fst x2, ` (snd x2))) ?x0 = [] |- _] => apply (map_rtype_nil x0) in H; simpl in H; subst
  | [H: (map
           (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
              (fst x, proj1_sig (snd x))) _)
        = 
        (map
           (fun x' : string * {τ₀' : rtype₀ | wf_rtype₀ τ₀' = true} =>
              (fst x', proj1_sig (snd x'))) _) |- _ ] =>
    apply map_rtype_fequal in H; trivial
  | [H:Rec _ _ _ = Rec _ _ _ |- _ ] => generalize (Rec_inv H); clear H; intro H; try subst
  | [H: context [(_::nil) = map 
                              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                 (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
                                                                                       
  | [H: context [map 
                   (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                      (fst x, proj1_sig (snd x))) _ = (_::_) ] |- _] => apply map_eq_cons in H;
                                                                        destruct H as [? [? [? [??]]]]
  | [H: Coll₀ _ = Coll₀ _ |- _ ] => inversion H; clear H
  | [H: Rec₀ _ _ = Rec₀ _ _ |- _ ] => inversion H; clear H
  | [H: nra_type _ _ (snd ?x) _ |- _] => destruct x; simpl in *; subst
  | [H:unary_op_type OpBag _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type OpFlatten _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type (OpRec _) _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type (OpDot _) _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type (OpRecRemove _) _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type OpRight _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type OpLeft _ _ |- _ ] => inversion H; clear H; subst
  | [H:binary_op_type OpRecConcat _ _ _ |- _ ] => inversion H; clear H
  | [H:binary_op_type OpAnd _ _ _ |- _ ] => inversion H; clear H
  | [H:binary_op_type OpRecMerge _ _ _ |- _ ] => inversion H; clear H
  end; try rtype_equalizer; try assumption; try subst; simpl in *; try nra_inverter.

  Lemma ATunnest_two_inv (s1 s2:string) (op:NRA.nra) τc τin rec  :
    unnest_two s1 s2 op ▷ 
                       τin >=> Coll rec ⊣ τc ->
    exists τ₁ pf1 τs τrem pf2,
    op ▷ τin >=> (Coll (Rec Closed τ₁ pf1)) ⊣ τc /\
    tdot τ₁ s1 = Some (Coll τs) /\
    rec = (Rec Closed τrem pf2) /\
    τrem = (rremove (rec_concat_sort τ₁ ((s2,τs)::nil)) s1).
  Proof.
    unfold unnest_two.
    intros H.
    inversion H; clear H; intros.
    nra_inverter.
    destruct x; simpl in *.
    repeat eexists; intuition; eauto.
  Qed.

End TNRAUtil.

Ltac nra_inverter := 
  match goal with
  | [H:Coll _ = Coll _ |- _] => inversion H; clear H
  | [H: `?τ₁ = Coll₀ (`?τ₂) |- _] => rewrite (Coll_right_inv τ₁ τ₂) in H; subst
  | [H:  Coll₀ (`?τ₂) = `?τ₁ |- _] => symmetry in H
  (* Note: do not generalize too hastily on unary_op/binary_op constructors *)
  | [H:@nra_type _ _ NRAID _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAMap _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAMapProduct _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAEither _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAEitherConcat _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRARecEither _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRADefault _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAApp _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAProduct _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRASelect _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAUnop _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRABinop _ _ _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (NRAConst _) _ _ |- _ ] => inversion H; clear H
  | [H:@nra_type _ _ (nra_data) _ _ |- _ ] => apply ATnra_data_inv' in H
  | [H:@nra_type _ _ (nra_data) (nra_context_type _ _) _ |- _ ] => apply ATnra_data_inv in H
  | [H: (_,_)  = (_,_) |- _ ] => inversion H; clear H
  | [H: map (fun x2 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
               (fst x2, ` (snd x2))) ?x0 = [] |- _] => apply (map_rtype_nil x0) in H; simpl in H; subst
  | [H: (map
           (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
              (fst x, proj1_sig (snd x))) _)
        = 
        (map
           (fun x' : string * {τ₀' : rtype₀ | wf_rtype₀ τ₀' = true} =>
              (fst x', proj1_sig (snd x'))) _) |- _ ] =>
    apply map_rtype_fequal in H; trivial
  | [H:Rec _ _ _ = Rec _ _ _ |- _ ] => generalize (Rec_inv H); clear H; intro H; try subst
  | [H: context [(_::nil) = map 
                              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                 (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
                                                                                       
  | [H: context [map 
                   (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                      (fst x, proj1_sig (snd x))) _ = (_::_) ] |- _] => apply map_eq_cons in H;
                                                                        destruct H as [? [? [? [??]]]]
  | [H: Coll₀ _ = Coll₀ _ |- _ ] => inversion H; clear H
  | [H: Rec₀ _ _ = Rec₀ _ _ |- _ ] => inversion H; clear H
  | [H: nra_type _ _ (snd ?x) _ |- _] => destruct x; simpl in *; subst
  | [H:unary_op_type OpBag _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type OpFlatten _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type (OpRec _) _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type (OpDot _) _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type (OpRecRemove _) _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type OpRight _ _ |- _ ] => inversion H; clear H; subst
  | [H:unary_op_type OpLeft _ _ |- _ ] => inversion H; clear H; subst
  | [H:binary_op_type OpRecConcat _ _ _ |- _ ] => inversion H; clear H
  | [H:binary_op_type OpAnd _ _ _ |- _ ] => inversion H; clear H
  | [H:binary_op_type OpRecMerge _ _ _ |- _ ] => inversion H; clear H
  end; try rtype_equalizer; try assumption; try subst; simpl in *; try nra_inverter.

