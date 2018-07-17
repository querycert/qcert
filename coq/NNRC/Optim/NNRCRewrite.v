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

(* This includes some rewrites/simplification rules for the Nested relational calculus *)

Require Import String.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRCRuntime.
Require Import NNRC.
Require Import NNRCShadow.
Require Import NNRCEq.
Require Import NNRCRewriteUtil.

Section NNRCRewrite.
  Local Open Scope nnrc_scope.
  (* unshadow(e) ≡ᶜ e *)

  Context {fruntime:foreign_runtime}.

  Lemma nnrc_unshadow_preserves sep renamer avoid (e:nnrc) :
    nnrc_eq (unshadow sep renamer avoid e) e.
  Proof.
    unfold nnrc_eq.
    intros.
    simpl.
    apply nnrc_unshadow_eval.
  Qed.

  (* { a: e }.a ≡ e *)

  Lemma dot_of_rec a (e:nnrc) :
    nnrc_eq (NNRCUnop (OpDot a) (NNRCUnop (OpRec a) e)) e.
  Proof.
    unfold nnrc_eq; intros ? ? ? ? _.
    unfold nnrc_eval.
    simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e)); [|reflexivity]; simpl.
    unfold edot; simpl.
    destruct (string_eqdec a a); congruence.
  Qed.

  Lemma nnrc_merge_concat_to_concat s1 s2 p1 p2:
    s1 <> s2 ->
    ‵[| (s1, p1)|] ⊗ ‵[| (s2, p2)|] ≡ᶜ ‵{|‵[| (s1, p1)|] ⊕ ‵[| (s2, p2)|]|}.
  Proof.
    red; intros; simpl.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base p1)); simpl; trivial.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base p2)); simpl; trivial.
    unfold merge_bindings.
    simpl.
    unfold compatible_with; simpl.
    destruct (EquivDec.equiv_dec s1 s2); try congruence.
    simpl.
    reflexivity.
  Qed.
  
  Lemma for_nil x e2 :
    nnrc_eq (NNRCFor x ‵{||} e2) ‵{||}.
  Proof.
    red; simpl; trivial.
  Qed.

  Lemma for_singleton_to_let x e1 e2:
    nnrc_eq (NNRCFor x (NNRCUnop OpBag e1) e2)
                (NNRCUnop OpBag (NNRCLet x e1 e2)).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); simpl; trivial.
    match_destr.
  Qed.

  Lemma flatten_nil_nnrc  :
    nnrc_eq (♯flatten(‵{||})) ‵{||}.
  Proof.
    red; simpl; trivial.
  Qed.


    (** cNNRC evaluation is only sensitive to the environment modulo
      lookup. *)
  Lemma nnrc_core_eval_lookup_equiv_on h σc σ₁ σ₂ (e:nnrc) :
    lookup_equiv_on (nnrc_free_vars e) σ₁ σ₂ ->
    nnrc_core_eval h σc σ₁ e = 
    nnrc_core_eval h σc σ₂ e.
      Proof.
        revert σ₁ σ₂.
        induction e; simpl; intros σ₁ σ₂ eqq; trivial
        ; try apply lookup_equiv_on_dom_app in eqq.
        - red in eqq; simpl in eqq; rewrite eqq; tauto.
        - erewrite IHe1, IHe2; try reflexivity; tauto.
        - erewrite IHe; try reflexivity; tauto.
        - destruct eqq as [eqq1 eqq2].
          rewrite (IHe1 _ _ eqq1).
          match_destr.
          erewrite IHe2; try reflexivity.
          unfold lookup_equiv_on in *.
          intros; simpl.
          match_destr.
          apply eqq2; trivial.
          apply remove_in_neq; trivial.
        - destruct eqq as [eqq1 eqq2].
          rewrite (IHe1 _ _ eqq1).
          match_destr.
          destruct d; simpl; trivial.
          f_equal.
          apply lift_map_ext; intros.
          erewrite IHe2; try reflexivity.
          unfold lookup_equiv_on in *.
          intros; simpl.
          match_destr.
          apply eqq2; trivial.
          apply remove_in_neq; trivial.
        - destruct eqq as [eqq1 eqq2].
          rewrite (IHe1 _ _ eqq1).
          apply olift_ext; intros.
          destruct a; simpl; trivial.
          apply lookup_equiv_on_dom_app in eqq2.
          destruct eqq2.
          destruct b; eauto.
        - destruct eqq as [eqq1 eqq2].
          rewrite (IHe1 _ _ eqq1).
          apply olift_ext; intros.
          apply lookup_equiv_on_dom_app in eqq2.
          destruct eqq2 as [eqq2 eqq3].
          destruct a; simpl; trivial.
          + erewrite IHe2; try reflexivity.
             unfold lookup_equiv_on in *.
             intros; simpl.
             match_destr.
             apply eqq2; trivial.
             apply remove_in_neq; trivial.
          + erewrite IHe3; try reflexivity.
             unfold lookup_equiv_on in *.
             intros; simpl.
             match_destr.
             apply eqq3; trivial.
             apply remove_in_neq; trivial.
      Qed.

  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|ee|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma map_sigma_fusion (e1 e2 e3:nnrc) ee (v1 v2:var) :
    ~ In v1 (nnrc_free_vars e3) ->
    nnrc_eq
      (NNRCFor v2 
              (NNRCUnop OpFlatten
                       (NNRCFor v1 e1
                               (NNRCIf e2 (NNRCUnop OpBag ee) (NNRCConst (dcoll nil)))))
              e3)
      (NNRCUnop OpFlatten
               (NNRCFor v1 e1
                       (NNRCIf e2
                              (NNRCUnop OpBag (NNRCLet v2 ee e3))
                              (NNRCConst (dcoll nil))))).
  Proof.
    intro notinfree.
    unfold nnrc_eq; intros ? ? ? ? _.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); try reflexivity; simpl.
    destruct d; simpl; trivial.
    clear e1.
    repeat rewrite olift_lift.
    simpl.
    transitivity (
        lift dcoll
             (olift (fun c1 =>
        (lift_map
           (fun d1 : data => nnrc_core_eval h cenv ((v2, d1) :: env) (nnrc_to_nnrc_base e3))
           c1))
    (olift (fun x : list data => oflatten x)
      (lift_map
         (fun d1 : data =>
          olift
            (fun d : data =>
             match d with
             | dbool true =>
                 olift (fun d0 : data => Some (dcoll (d0 :: nil)))
                   (nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base ee))
             | dbool false => Some (dcoll nil)
             | _ => None
             end) (nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2))) l)
                 ))).
    {
      match goal with
        [|- match (olift _ ?x) with | Some _ => _ | None => _ end = _] => destruct x 
      end; simpl; trivial.
      destruct (oflatten l0); simpl; trivial.
    }
    transitivity (
      lift dcoll
           (olift (fun x : list data => oflatten x)
    (lift_map
       (fun d1 : data =>
        olift
          (fun d : data =>
           match d with
           | dbool true =>
               olift (fun d0 : data => Some (dcoll (d0 :: nil)))
                 match nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base ee) with
                 | Some d0 =>
                     nnrc_core_eval h cenv ((v2, d0) :: (v1, d1) :: env)
                       (nnrc_to_nnrc_base e3)
                 | None => None
                 end
           | dbool false => Some (dcoll nil)
           | _ => None
           end) (nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2))) l))).
    2: { idtac.
         match goal with
           [|- _ = olift _ ?x ] => destruct x 
         end; simpl; trivial.
         }
       f_equal.
    induction l; try reflexivity; simpl.
    destruct ((nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e2))); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct b; intros.
     - destruct ((nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base ee)))
       ; simpl; trivial.
       rewrite oflatten_lift_cons_dcoll.
       rewrite olift_lift; simpl.
       replace (nnrc_core_eval h cenv ((v2, d) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)) with
           (nnrc_core_eval h cenv ((v2, d) :: env) (nnrc_to_nnrc_base e3)).
       2: { idtac.
            apply nnrc_core_eval_lookup_equiv_on; trivial.
            red; simpl; intros.
            destruct (string_eqdec x v2); simpl; trivial.
            destruct (string_eqdec x v1); simpl; trivial.
            rewrite nnrc_to_nnrc_base_free_vars_same in notinfree.
            congruence.
            }
       destruct (nnrc_core_eval h cenv ((v2, d) :: env) (nnrc_to_nnrc_base e3))
        ; simpl; trivial
        ; [ | match goal with [|- olift _ ?x = _ ] => destruct x; simpl; trivial end].
        rewrite <- lift_olift.
        rewrite oflatten_lift_cons_dcoll.
        f_equal.
        match type of IHl with
        | ?x = _ => transitivity x
        end.
        + apply olift_ext; trivial.
        + rewrite IHl.
           apply olift_ext; trivial.
 - repeat (rewrite oflatten_lift_empty_dcoll).
   rewrite (olift_eta oflatten).
   rewrite IHl.
   rewrite <- (olift_eta oflatten).
   trivial.
            Qed.   

  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|ee|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t1 := ee IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma map_sigma_fusion_samevar (e1 e2 e3:nnrc) e (v1:var) :
    nnrc_eq
      (NNRCFor v1 
              (NNRCUnop OpFlatten
                       (NNRCFor v1 e1
                               (NNRCIf e2 (NNRCUnop OpBag e) (NNRCConst (dcoll nil)))))
              e3)
      (NNRCUnop OpFlatten
               (NNRCFor v1 e1
                       (NNRCIf e2
                              (NNRCUnop OpBag (NNRCLet v1 e e3))
                              (NNRCConst (dcoll nil))))).
  Proof.
    unfold nnrc_eq; intros ? ? ? ? _.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); try reflexivity; simpl.
    destruct d; simpl; trivial.
    clear e1.
    repeat rewrite olift_lift.
    simpl.
    transitivity (
        lift dcoll
             (olift (fun c1 =>
        (lift_map
           (fun d1 : data => nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e3))
           c1))
    (olift (fun x : list data => oflatten x)
      (lift_map
         (fun d1 : data =>
          olift
            (fun d : data =>
             match d with
             | dbool true =>
                 olift (fun d0 : data => Some (dcoll (d0 :: nil)))
                   (nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e))
             | dbool false => Some (dcoll nil)
             | _ => None
             end) (nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2))) l)
                 ))).
    {
      match goal with
        [|- match (olift _ ?x) with | Some _ => _ | None => _ end = _] => destruct x 
      end; simpl; trivial.
      destruct (oflatten l0); simpl; trivial.
    }
    transitivity (
      lift dcoll
           (olift (fun x : list data => oflatten x)
    (lift_map
       (fun d1 : data =>
        olift
          (fun d : data =>
           match d with
           | dbool true =>
               olift (fun d0 : data => Some (dcoll (d0 :: nil)))
                 match nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e) with
                 | Some d0 =>
                     nnrc_core_eval h cenv ((v1, d0) :: (v1, d1) :: env)
                       (nnrc_to_nnrc_base e3)
                 | None => None
                 end
           | dbool false => Some (dcoll nil)
           | _ => None
           end) (nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2))) l))).
    2: { idtac.
         match goal with
           [|- _ = olift _ ?x ] => destruct x 
         end; simpl; trivial.
         }
       f_equal.
    induction l; try reflexivity; simpl.
    destruct ((nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e2))); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct b; intros.
     - destruct ((nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e)))
       ; simpl; trivial.
       rewrite oflatten_lift_cons_dcoll.
       rewrite olift_lift; simpl.
       replace (nnrc_core_eval h cenv ((v1, d) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)) with
           (nnrc_core_eval h cenv ((v1, d) :: env) (nnrc_to_nnrc_base e3)).
       2: { idtac.
            apply nnrc_core_eval_lookup_equiv_prop; trivial.
            red; simpl; intros.
            destruct (string_eqdec x v1); simpl; trivial.
            }
       destruct (nnrc_core_eval h cenv ((v1, d) :: env) (nnrc_to_nnrc_base e3))
        ; simpl; trivial
        ; [ | match goal with [|- olift _ ?x = _ ] => destruct x; simpl; trivial end].
        rewrite <- lift_olift.
        rewrite oflatten_lift_cons_dcoll.
        f_equal.
        match type of IHl with
        | ?x = _ => transitivity x
        end.
        + apply olift_ext; trivial.
        + rewrite IHl.
           apply olift_ext; trivial.
 - repeat (rewrite oflatten_lift_empty_dcoll).
   rewrite (olift_eta oflatten).
   rewrite IHl.
   rewrite <- (olift_eta oflatten).
   trivial.
            Qed. 


  Lemma for_over_if x e1 e2  e3 ebody :
    nnrc_eq (NNRCFor x (NNRCIf e1 e2 e3) ebody)
            (NNRCIf e1 (NNRCFor x e2 ebody)
                   (NNRCFor x e3 ebody)).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); simpl; trivial.
    destruct d; simpl; trivial.
    destruct b; simpl; trivial.
  Qed.

  Lemma for_over_for x y source body1 body2 :
    ~ In y (nnrc_free_vars body2) ->
    nnrc_eq (NNRCFor x (NNRCFor y source body1) body2)
            (NNRCFor y source
                     (NNRCLet x body1 body2)).
  Proof.
    red; simpl; intros nin; intros.
    rewrite nnrc_to_nnrc_base_free_vars_same in nin.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base source)); simpl; trivial.
    destruct d; simpl; trivial.
    (* simplify a bit *)
    transitivity (
    match
      (lift_map
         (fun d1 : data => nnrc_core_eval h cenv ((y, d1) :: env) (nnrc_to_nnrc_base body1)) l)
  with
  | Some c1 =>
      lift dcoll
        (lift_map
           (fun d1 : data => nnrc_core_eval h cenv ((x, d1) :: env) (nnrc_to_nnrc_base body2))
           c1)
  | _ => None
    end).
    {
      destruct (lift_map
                  (fun d1 : data => nnrc_core_eval h cenv ((y, d1) :: env) (nnrc_to_nnrc_base body1)) l); simpl; trivial.
    }
    (* another tweak *)
    transitivity (lift dcoll
                       (olift (fun c1 => (lift_map
           (fun d1 : data => nnrc_core_eval h cenv ((x, d1) :: env) (nnrc_to_nnrc_base body2))
           c1)) (lift_map
                   (fun d1 : data => nnrc_core_eval h cenv ((y, d1) :: env) (nnrc_to_nnrc_base body1)) l))).
    {
      destruct (lift_map
                  (fun d1 : data => nnrc_core_eval h cenv ((y, d1) :: env) (nnrc_to_nnrc_base body1)) l); simpl; trivial.
    }
    f_equal.
    induction l; simpl; simpl; trivial.
    destruct (nnrc_core_eval h cenv ((y, a) :: env) (nnrc_to_nnrc_base body1))
    ; simpl; trivial.
    rewrite olift_lift; simpl.
    generalize (@nnrc_core_eval_remove_free_env _ h cenv ((x, d)::nil) y a)
    ; simpl; intros HH.
    rewrite HH by tauto; clear HH.
    destruct (nnrc_core_eval h cenv ((x, d) :: env) (nnrc_to_nnrc_base body2))
    ; simpl
    ; [rewrite <- IHl | ]
    ; destruct (lift_map
                  (fun d1 : data => nnrc_core_eval h cenv ((y, d1) :: env) (nnrc_to_nnrc_base body1)) l); simpl; trivial.
  Qed.
    
  Lemma for_over_either_disjoint x e1 xl el xr er ebody:
    disjoint (xl::xr::nil) (nnrc_free_vars ebody) ->
    nnrc_eq (NNRCFor x (NNRCEither e1 xl el xr er) ebody)
            (NNRCEither e1
                       xl (NNRCFor x el ebody)
                       xr (NNRCFor x er ebody)).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    apply disjoint_cons_inv1 in H.
    destruct H as [disj nin1].
    apply disjoint_cons_inv1 in disj.
    destruct disj as [_ nin2].
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); simpl; trivial.
    rewrite nnrc_to_nnrc_base_free_vars_same in nin2, nin1.
    destruct d; simpl; trivial;
      (destruct (equiv_dec (A:=string) xl xl); [|congruence]);
      match_case; simpl; intros; match_destr;
        f_equal;
      apply lift_map_ext; intros.
    - generalize (@nnrc_core_eval_remove_free_env _ h cenv ((x,x0)::nil) xl d env (nnrc_to_nnrc_base ebody)); simpl; intros re1; rewrite re1; trivial.
    - generalize (@nnrc_core_eval_remove_free_env _ h cenv ((x,x0)::nil) xr d env (nnrc_to_nnrc_base ebody)); simpl; intros re1; rewrite re1; trivial.
  Qed.

  Lemma nnrclet_rename e₁ e₂ x x' :
    ~ In x' (nnrc_free_vars e₂) ->
    ~ In x' (nnrc_bound_vars e₂) ->
    nnrc_eq (NNRCLet x e₁ e₂)
            (NNRCLet x' e₁ (nnrc_subst e₂ x (NNRCVar x'))).
  Proof.
    red; simpl; intros nfree nbound; intros.
    generalize (@nnrc_eval_cons_subst _ h cenv e₂ env x);
      unfold nnrc_eval; simpl; intros.
    match_destr.
    rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
    specialize (H1 d x' nfree nbound).
    rewrite <- nnrc_to_nnrc_base_subst_comm in H1. simpl in H1.
    rewrite H1.
    trivial.
  Qed.

   Lemma nnrcfor_rename e₁ e₂ x x' :
    ~ In x' (nnrc_free_vars e₂) ->
    ~ In x' (nnrc_bound_vars e₂) ->
    nnrc_eq (NNRCFor x e₁ e₂)
            (NNRCFor x' e₁ (nnrc_subst e₂ x (NNRCVar x'))).
  Proof.
    red; simpl; intros nfree nbound; intros.
    generalize (@nnrc_eval_cons_subst _ h cenv e₂ env x);
      unfold nnrc_eval; simpl; intros.
    do 2 match_destr.
    f_equal.
    apply lift_map_ext; intros dd inn.
    rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
    specialize (H1 dd x' nfree nbound).
    rewrite <- nnrc_to_nnrc_base_subst_comm in H1. simpl in H1.
    rewrite H1.
    trivial.
  Qed.

  Lemma nnrceither_rename_l e1 xl el xr er xl' :
    ~ In xl' (nnrc_free_vars el) ->
    ~ In xl' (nnrc_bound_vars el) ->
    nnrc_eq (NNRCEither e1 xl el xr er)
            (NNRCEither e1 xl' (nnrc_subst el xl (NNRCVar xl')) xr er).
  Proof.
    red; simpl; intros nfree nbound; intros.
    generalize (@nnrc_eval_cons_subst _ h cenv el env xl);
      unfold nnrc_eval; simpl; intros.
    do 2 match_destr.
    rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
    specialize (H1 d xl' nfree nbound).
    rewrite <- nnrc_to_nnrc_base_subst_comm in H1. simpl in H1.
    rewrite H1.
    trivial.
  Qed.

  Lemma nnrceither_rename_r e1 xl el xr er xr' :
    ~ In xr' (nnrc_free_vars er) ->
    ~ In xr' (nnrc_bound_vars er) ->
    nnrc_eq (NNRCEither e1 xl el xr er)
                (NNRCEither e1 xl el xr' (nnrc_subst er xr (NNRCVar xr'))).
  Proof.
    red; simpl; intros nfree nbound; intros.
    generalize (@nnrc_eval_cons_subst _ h cenv er env xr);
      unfold nnrc_eval; simpl; intros.
    unfold nnrc_eval; simpl.
    do 2 match_destr.
    rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
    specialize (H1 d xr' nfree nbound).
    rewrite <- nnrc_to_nnrc_base_subst_comm in H1. simpl in H1.
    rewrite H1.
    trivial.
  Qed.

  Lemma for_over_either sep x e1 xl el xr er ebody:
    nnrc_eq (NNRCFor x (NNRCEither e1 xl el xr er) ebody)
            (    let xl' := really_fresh_in_ext sep xl (nnrc_free_vars el ++ nnrc_bound_vars el) ebody in
                 let xr' := really_fresh_in_ext sep xr (nnrc_free_vars er ++ nnrc_bound_vars er) ebody in
              (NNRCEither e1
                       xl' (NNRCFor x (nnrc_subst el xl (NNRCVar xl')) ebody)
                       xr' (NNRCFor x (nnrc_subst er xr (NNRCVar xr')) ebody))).
  Proof.
    simpl.
    transitivity (NNRCFor x (NNRCEither e1
                                       (really_fresh_in_ext sep xl (nnrc_free_vars el ++ nnrc_bound_vars el) ebody)
                                       (nnrc_subst el xl (NNRCVar (really_fresh_in_ext sep xl (nnrc_free_vars el ++ nnrc_bound_vars el) ebody)))
                                       (really_fresh_in_ext sep xr (nnrc_free_vars er ++ nnrc_bound_vars er) ebody)
                                       (nnrc_subst er xr (NNRCVar (really_fresh_in_ext sep xr (nnrc_free_vars er ++ nnrc_bound_vars er) ebody)))) ebody).
    - rewrite <- nnrceither_rename_l; simpl.
      rewrite <- nnrceither_rename_r; simpl.
      reflexivity.
      + intro inn.
        assert (inn2:In (really_fresh_in_ext sep xr (nnrc_free_vars er ++ nnrc_bound_vars er) ebody)
                    (nnrc_free_vars er ++ nnrc_bound_vars er))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in_ext sep xr (nnrc_free_vars er ++ nnrc_bound_vars er) ebody)
                    (nnrc_free_vars er ++ nnrc_bound_vars er))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in_ext sep xl (nnrc_free_vars el ++ nnrc_bound_vars el) ebody)
                    (nnrc_free_vars el ++ nnrc_bound_vars el))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in_ext sep xl (nnrc_free_vars el ++ nnrc_bound_vars el) ebody)
                    (nnrc_free_vars el ++ nnrc_bound_vars el))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
    - assert ((nnrc_free_vars ebody) =
              (nnrc_free_vars (nnrc_to_nnrc_base ebody))).
      apply nnrc_to_nnrc_base_free_vars_same.
      apply for_over_either_disjoint.
      red; simpl; intuition; subst.
      rewrite H in H1.
      revert H1.
      apply really_fresh_from_free_ext; intros.
      rewrite H in H1.
      revert H1.
      apply really_fresh_from_free_ext; intros.
  Qed.

  Lemma nnrcunop_over_either op e1 xl el xr er:
    nnrc_eq (NNRCUnop op (NNRCEither e1 xl el xr er))
                (NNRCEither e1 xl (NNRCUnop op el) xr (NNRCUnop op er)).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    repeat match_destr.
  Qed.

  Lemma nnrcunop_over_if op e1 e2 e3:
    nnrc_eq (NNRCUnop op (NNRCIf e1 e2 e3))
                (NNRCIf e1 (NNRCUnop op e2) (NNRCUnop op e3)).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); simpl; trivial.
    repeat match_destr.
  Qed.

  (* ♯flatten({ e1 ? { $t1 } : {} | $t1 ∈ { e2 } }) ≡ LET $t1 := e2 IN e1 ? { $t1 } : {} *)

  Lemma sigma_to_if (e1 e2:nnrc) (v:var) :
    nnrc_eq
      (NNRCUnop OpFlatten
                (NNRCFor v (NNRCUnop OpBag e2)
                         (NNRCIf e1
                                 (NNRCUnop OpBag (NNRCVar v))
                                 (NNRCConst (dcoll nil)))))
      (NNRCLet v e2 (NNRCIf e1 (NNRCUnop OpBag (NNRCVar v)) (NNRCConst (dcoll nil)))).
  Proof.
    unfold nnrc_eq; intros ? ? ? ? _.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e2)); try reflexivity; simpl.
    dest_eqdec; try congruence.
    destruct (nnrc_core_eval h cenv ((v,d) :: env) (nnrc_to_nnrc_base e1)); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    destruct b; reflexivity.
  Qed.

  Lemma unshadow_free_vars sep renamer (x:var) (e:nnrc):
    In x (nnrc_free_vars (unshadow sep renamer nil e)) -> In x (nnrc_free_vars e).
  Proof.
    rewrite unshadow_nnrc_free_vars.
    intros; assumption.
  Qed.

  (** optimizations for record projection *)
  Lemma nnrcproject_over_concat sl p1 p2 :
    π[sl](p1 ⊕ p2)
          ≡ᶜ π[sl](p1) ⊕ π[sl](p2).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base p2));
      destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base p1)); simpl.
    - destruct d; destruct d0; simpl; trivial.
      rewrite rproject_rec_sort_commute, rproject_app.
      trivial.
    - trivial.
    - destruct d; simpl; trivial.
    - trivial.
  Qed.

  Lemma nnrcproject_over_const sl l :
    π[sl](NNRCConst (drec l)) ≡ᶜ NNRCConst (drec (rproject l sl)).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    rewrite rproject_rec_sort_commute.
    rewrite rproject_map_fst_same; intuition.
  Qed.
  
  Lemma nnrcproject_over_rec_in sl s p :
    In s sl ->
    π[sl](‵[| (s, p) |]) ≡ᶜ ‵[| (s, p) |].
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base p)); simpl; trivial.
    destruct (in_dec string_dec s sl); intuition.
  Qed.

  Lemma nnrcproject_over_nnrcproject sl1 sl2 p :
    π[sl1](π[sl2](p)) ≡ᶜ π[set_inter string_dec sl2 sl1](p).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base p)); simpl; trivial.
    destruct d; simpl; trivial.
    rewrite rproject_rproject.
    trivial.
  Qed.

  Lemma nnrcproject_over_either sl p xl xr p1 p2 :
    π[sl](NNRCEither p xl p1 xr p2) ≡ᶜ NNRCEither p xl (π[sl](p1)) xr (π[sl](p2)).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base p)); simpl; trivial.
    destruct d; simpl; trivial.
  Qed.

End NNRCRewrite.

Hint Rewrite @sigma_to_if : nnrc_rew.
(* Hint Rewrite subst_var_preserves : nnrc_rew. *)

