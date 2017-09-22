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

Section NNRCRewrite.
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

  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma map_sigma_fusion (e1 e2 e3:nnrc) (v1 v2:var) :
    ~ In v1 (nnrc_free_vars e3) ->
    nnrc_eq
      (NNRCFor v2 
              (NNRCUnop OpFlatten
                       (NNRCFor v1 e1
                               (NNRCIf e2 (NNRCUnop OpBag (NNRCVar v1)) (NNRCConst (dcoll nil)))))
              e3)
      (NNRCUnop OpFlatten
               (NNRCFor v1 e1
                       (NNRCIf e2
                              (NNRCUnop OpBag (NNRCLet v2 (NNRCVar v1) e3))
                              (NNRCConst (dcoll nil))))).
  Proof.
    intro notinfree.
    unfold nnrc_eq; intros ? ? ? ? _.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); try reflexivity; simpl.
    dest_eqdec; try congruence.
    clear e1 e.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    destruct ((nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e2))); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    case_eq b; intros.
    - autorewrite with alg.
      rewrite oflatten_lift_cons_dcoll.
      autorewrite with alg in IHl.
      unfold olift in *.
      case_eq (lift_map
              (fun d1 : data =>
               match nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2) with
               | Some (dbool true) =>
                   match nnrc_core_eval h cenv ((v2, d1) :: (v1, d1) :: env) (nnrc_to_nnrc_base e3) with
                   | Some x'0 => Some (dcoll (x'0 :: nil))
                   | None => None
                   end
               | Some (dbool false) => Some (dcoll nil)
               | _ => None
               end) l); intros; rewrite H1 in IHl; case_eq (lift_map
                (fun d1 : data =>
                 match nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2) with
                 | Some (dbool true) => Some (dcoll (d1 :: nil))
                 | Some (dbool false) => Some (dcoll nil)
                 | _ => None
                 end) l); intros; rewrite H2 in IHl; simpl in *.
      + clear H1 H2.
        unfold lift in *.
        case_eq (oflatten l1); case_eq (oflatten l0); intros;  rewrite H1 in *; rewrite H2 in *.
        * simpl.
          assert (exists l4, lift_map (fun d1 : data => nnrc_core_eval h cenv ((v2, d1) :: env) (nnrc_to_nnrc_base e3)) l3 = Some l4).
          destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v2, d1) :: env) (nnrc_to_nnrc_base e3)) l3); try congruence.
          exists l4; reflexivity.
          elim H3; clear H3; intros.
          rewrite H3 in *; clear H3.
          simpl.
          inversion IHl. subst; clear IHl.
          assert (nnrc_core_eval h cenv ((v2, a) :: env) (nnrc_to_nnrc_base e3)
                  = nnrc_core_eval h cenv((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)).
          rewrite nnrc_to_nnrc_base_free_vars_same in notinfree.
          generalize (@nnrc_core_eval_remove_free_env _ h cenv ((v2,a)::nil) v1 a env (nnrc_to_nnrc_base e3) notinfree); intros.
          simpl in H0.
          rewrite H0; clear H0; reflexivity.
          rewrite H0; clear H0.
          destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          rewrite (oflatten_cons (d::nil) l0 l2).
          reflexivity.
          assumption.
        * simpl.
          destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v2, d1) :: env) (nnrc_to_nnrc_base e3)) l2); try congruence.
          simpl.
          destruct (nnrc_core_eval h cenv ((v2, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          rewrite oflatten_cons_none; [reflexivity|assumption].
          destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          rewrite oflatten_cons_none; [reflexivity|assumption].
        * congruence.
        * destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          rewrite oflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (oflatten l0); intros; rewrite H3 in *; try congruence.
        destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
        rewrite oflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (oflatten l0); intros; rewrite H3 in *; try congruence.
        simpl in *.
        destruct (nnrc_core_eval h cenv ((v2, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
        destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v2, d1) :: env) (nnrc_to_nnrc_base e3)) l1); try reflexivity; try congruence.
        simpl.
        destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
        destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
        destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
      + destruct (nnrc_core_eval h cenv ((v2, a) :: (v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
    - autorewrite with alg.
      rewrite oflatten_lift_empty_dcoll.
      rewrite oflatten_lift_empty_dcoll.
      autorewrite with alg in IHl.
      rewrite IHl.
      reflexivity.
  Qed.

  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma map_sigma_fusion_samevar (e1 e2 e3:nnrc) (v1:var) :
    nnrc_eq
      (NNRCFor v1 
              (NNRCUnop OpFlatten
                       (NNRCFor v1 e1
                               (NNRCIf e2 (NNRCUnop OpBag (NNRCVar v1)) (NNRCConst (dcoll nil)))))
              e3)
      (NNRCUnop OpFlatten
               (NNRCFor v1 e1
                       (NNRCIf e2
                              (NNRCUnop OpBag e3)
                              (NNRCConst (dcoll nil))))).
  Proof.
    unfold nnrc_eq; intros ? ? ? ? _.
    unfold nnrc_eval; simpl.
    destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base e1)); try reflexivity; simpl.
    dest_eqdec; try congruence.
    clear e1 e.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    destruct ((nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e2))); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    case_eq b; intros.
    - autorewrite with alg.
      rewrite oflatten_lift_cons_dcoll.
      autorewrite with alg in IHl.
      unfold olift in *.
      case_eq (lift_map
              (fun d1 : data =>
               match nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2) with
               | Some (dbool true) =>
                   match nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e3) with
                   | Some x'0 => Some (dcoll (x'0 :: nil))
                   | None => None
                   end
               | Some (dbool false) => Some (dcoll nil)
               | _ => None
               end) l); intros; rewrite H1 in IHl; case_eq (lift_map
                (fun d1 : data =>
                 match nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e2) with
                 | Some (dbool true) => Some (dcoll (d1 :: nil))
                 | Some (dbool false) => Some (dcoll nil)
                 | _ => None
                 end) l); intros; rewrite H2 in IHl; simpl in *.
      + clear H1 H2.
        unfold lift in *.
        case_eq (oflatten l1); case_eq (oflatten l0); intros;  rewrite H1 in *; rewrite H2 in *.
        * simpl.
          assert (exists l4, lift_map (fun d1 : data => nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e3)) l3 = Some l4).
          destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e3)) l3); try congruence.
          exists l4; reflexivity.
          elim H3; clear H3; intros.
          rewrite H3 in *; clear H3.
          simpl.
          inversion IHl. subst; clear IHl.
          destruct (nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          rewrite (oflatten_cons (d::nil) l0 l2).
          reflexivity.
          assumption.
        * simpl.
          destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e3)) l2); try congruence.
          simpl.
          destruct (nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          rewrite oflatten_cons_none; [reflexivity|assumption].
        * congruence.
        * destruct (nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
          rewrite oflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (oflatten l0); intros; rewrite H3 in *; try congruence.
        destruct (nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
        rewrite oflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (oflatten l0); intros; rewrite H3 in *; try congruence.
        simpl in *.
        destruct (nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
        destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v1, d1) :: env) (nnrc_to_nnrc_base e3)) l1); try reflexivity; try congruence.
        simpl.
        destruct (nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
      + destruct (nnrc_core_eval h cenv ((v1, a) :: env) (nnrc_to_nnrc_base e3)); try reflexivity.
    - autorewrite with alg.
      rewrite oflatten_lift_empty_dcoll.
      rewrite oflatten_lift_empty_dcoll.
      autorewrite with alg in IHl.
      rewrite IHl.
      reflexivity.
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

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
