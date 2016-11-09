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

Section NRew.
  Require Import String.
  Require Import List ListSet.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import NNRC NNRCEq NNRCShadow.
  Require Import NRewUtil.

  Local Open Scope nrc_scope.
  (* unshadow(e) ≡ᶜ e *)

  Context {fruntime:foreign_runtime}.

  Lemma unshadow_preserves sep renamer avoid (e:nrc) :
    nnrc_eq (unshadow sep renamer avoid e) e.
  Proof.
    unfold nnrc_eq.
    intros.
    apply unshadow_eval.
  Qed.

  (* { a: e }.a ≡ e *)

  Lemma dot_of_rec a (e:nrc) :
    nnrc_eq (NRCUnop (ADot a) (NRCUnop (ARec a) e)) e.
  Proof.
    unfold nnrc_eq; intros ? ? _.
    simpl.
    destruct (nrc_eval h env e); [|reflexivity]; simpl.
    unfold edot; simpl.
    destruct (string_eqdec a a); congruence.
  Qed.

    Lemma nrc_merge_concat_to_concat s1 s2 p1 p2:
    s1 <> s2 ->
    ‵[| (s1, p1)|] ⊗ ‵[| (s2, p2)|] ≡ᶜ ‵{|‵[| (s1, p1)|] ⊕ ‵[| (s2, p2)|]|}.
  Proof.
    red; intros; simpl.
    destruct (nrc_eval h env p1); simpl; trivial.
    destruct (nrc_eval h env p2); simpl; trivial.
    unfold merge_bindings.
    simpl.
    unfold compatible_with; simpl.
    destruct (EquivDec.equiv_dec s1 s2); try congruence.
    simpl.
    reflexivity.
  Qed.
  
  Lemma for_nil x e2 :
    nnrc_eq (NRCFor x ‵{||} e2) ‵{||}.
  Proof.
    red; simpl; trivial.
  Qed.
    
  Lemma for_singleton_to_let x e1 e2:
    nnrc_eq (NRCFor x (NRCUnop AColl e1) e2)
            (NRCUnop AColl (NRCLet x e1 e2)).
  Proof.
    red; simpl; intros.
    destruct (nrc_eval h env e1); simpl; trivial.
    match_destr.
  Qed.

  Lemma flatten_nil_nrc  :
    nnrc_eq (♯flatten(‵{||})) ‵{||}.
  Proof.
    red; simpl; trivial.
  Qed.


  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma map_sigma_fusion (e1 e2 e3:nrc) (v1 v2:var) :
    ~ In v1 (nrc_free_vars e3) ->
    nnrc_eq
      (NRCFor v2 
              (NRCUnop AFlatten
                       (NRCFor v1 e1
                               (NRCIf e2 (NRCUnop AColl (NRCVar v1)) (NRCConst (dcoll nil)))))
              e3)
      (NRCUnop AFlatten
               (NRCFor v1 e1
                       (NRCIf e2
                              (NRCUnop AColl (NRCLet v2 (NRCVar v1) e3))
                              (NRCConst (dcoll nil))))).
  Proof.
    intro notinfree.
    unfold nnrc_eq; intros ? ? _.
    simpl.
    destruct (nrc_eval h env e1); try reflexivity; simpl.
    dest_eqdec; try congruence.
    clear e1 e.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    destruct ((nrc_eval h ((v1, a) :: env) e2)); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    case_eq b; intros.
    - autorewrite with alg.
      rewrite lift_cons_dcoll.
      autorewrite with alg in IHl.
      unfold olift in *.
      case_eq (rmap
              (fun d1 : data =>
               match nrc_eval h ((v1, d1) :: env) e2 with
               | Some (dbool true) =>
                   match nrc_eval h ((v2, d1) :: (v1, d1) :: env) e3 with
                   | Some x'0 => Some (dcoll (x'0 :: nil))
                   | None => None
                   end
               | Some (dbool false) => Some (dcoll nil)
               | _ => None
               end) l); intros; rewrite H0 in IHl; case_eq (rmap
                (fun d1 : data =>
                 match nrc_eval h ((v1, d1) :: env) e2 with
                 | Some (dbool true) => Some (dcoll (d1 :: nil))
                 | Some (dbool false) => Some (dcoll nil)
                 | _ => None
                 end) l); intros; rewrite H1 in IHl; simpl in *.
      + clear H0 H1.
        unfold lift in *.
        case_eq (rflatten l1); case_eq (rflatten l0); intros;  rewrite H0 in *; rewrite H1 in *.
        * simpl.
          assert (exists l4, rmap (fun d1 : data => nrc_eval h ((v2, d1) :: env) e3) l3 = Some l4).
          destruct (rmap (fun d1 : data => nrc_eval h ((v2, d1) :: env) e3) l3); try congruence.
          exists l4; reflexivity.
          elim H2; clear H2; intros.
          rewrite H2 in *; clear H2.
          simpl.
          inversion IHl. subst; clear IHl.
          assert (nrc_eval h ((v2, a) :: env) e3 = nrc_eval h ((v2, a) :: (v1, a) :: env) e3).
          generalize (@nrc_eval_remove_free_env _ h ((v2,a)::nil) v1 a env e3 notinfree); intros.
          simpl in H.
          rewrite H; clear H; reflexivity.
          rewrite H; clear H.
          destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
          rewrite (rflatten_cons (d::nil) l0 l2).
          reflexivity.
          assumption.
        * simpl.
          destruct (rmap (fun d1 : data => nrc_eval h ((v2, d1) :: env) e3) l2); try congruence.
          simpl.
          destruct (nrc_eval h ((v2, a) :: env) e3); try reflexivity.
          destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
          rewrite rflatten_cons_none; [reflexivity|assumption].
          destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
          rewrite rflatten_cons_none; [reflexivity|assumption].
        * congruence.
        * destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
          rewrite rflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (rflatten l0); intros; rewrite H2 in *; try congruence.
        destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
        rewrite rflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (rflatten l0); intros; rewrite H2 in *; try congruence.
        simpl in *.
        destruct (nrc_eval h ((v2, a) :: env) e3); try reflexivity.
        destruct (rmap (fun d1 : data => nrc_eval h ((v2, d1) :: env) e3) l1); try reflexivity; try congruence.
        simpl.
        destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
        destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
        destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
      + destruct (nrc_eval h ((v2, a) :: (v1, a) :: env) e3); try reflexivity.
    - autorewrite with alg.
      rewrite lift_empty_dcoll.
      rewrite lift_empty_dcoll.
      autorewrite with alg in IHl.
      rewrite IHl.
      reflexivity.
  Qed.

    (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma map_sigma_fusion_samevar (e1 e2 e3:nrc) (v1:var) :
    nnrc_eq
      (NRCFor v1 
              (NRCUnop AFlatten
                       (NRCFor v1 e1
                               (NRCIf e2 (NRCUnop AColl (NRCVar v1)) (NRCConst (dcoll nil)))))
              e3)
      (NRCUnop AFlatten
               (NRCFor v1 e1
                       (NRCIf e2
                              (NRCUnop AColl e3)
                              (NRCConst (dcoll nil))))).
  Proof.
    unfold nnrc_eq; intros ? ? _.
    simpl.
    destruct (nrc_eval h env e1); try reflexivity; simpl.
    dest_eqdec; try congruence.
    clear e1 e.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    destruct ((nrc_eval h ((v1, a) :: env) e2)); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    case_eq b; intros.
    - autorewrite with alg.
      rewrite lift_cons_dcoll.
      autorewrite with alg in IHl.
      unfold olift in *.
      case_eq (rmap
              (fun d1 : data =>
               match nrc_eval h ((v1, d1) :: env) e2 with
               | Some (dbool true) =>
                   match nrc_eval h ((v1, d1) :: env) e3 with
                   | Some x'0 => Some (dcoll (x'0 :: nil))
                   | None => None
                   end
               | Some (dbool false) => Some (dcoll nil)
               | _ => None
               end) l); intros; rewrite H0 in IHl; case_eq (rmap
                (fun d1 : data =>
                 match nrc_eval h ((v1, d1) :: env) e2 with
                 | Some (dbool true) => Some (dcoll (d1 :: nil))
                 | Some (dbool false) => Some (dcoll nil)
                 | _ => None
                 end) l); intros; rewrite H1 in IHl; simpl in *.
      + clear H0 H1.
        unfold lift in *.
        case_eq (rflatten l1); case_eq (rflatten l0); intros;  rewrite H0 in *; rewrite H1 in *.
        * simpl.
          assert (exists l4, rmap (fun d1 : data => nrc_eval h ((v1, d1) :: env) e3) l3 = Some l4).
          destruct (rmap (fun d1 : data => nrc_eval h ((v1, d1) :: env) e3) l3); try congruence.
          exists l4; reflexivity.
          elim H2; clear H2; intros.
          rewrite H2 in *; clear H2.
          simpl.
          inversion IHl. subst; clear IHl.
          destruct (nrc_eval h ((v1, a) :: env) e3); try reflexivity.
          rewrite (rflatten_cons (d::nil) l0 l2).
          reflexivity.
          assumption.
        * simpl.
          destruct (rmap (fun d1 : data => nrc_eval h ((v1, d1) :: env) e3) l2); try congruence.
          simpl.
          destruct (nrc_eval h ((v1, a) :: env) e3); try reflexivity.
          rewrite rflatten_cons_none; [reflexivity|assumption].
        * congruence.
        * destruct (nrc_eval h ((v1, a) :: env) e3); try reflexivity.
          rewrite rflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (rflatten l0); intros; rewrite H2 in *; try congruence.
        destruct (nrc_eval h ((v1, a) :: env) e3); try reflexivity.
        rewrite rflatten_cons_none; [reflexivity|assumption].
      + unfold lift in *.
        case_eq (rflatten l0); intros; rewrite H2 in *; try congruence.
        simpl in *.
        destruct (nrc_eval h ((v1, a) :: env) e3); try reflexivity.
        destruct (rmap (fun d1 : data => nrc_eval h ((v1, d1) :: env) e3) l1); try reflexivity; try congruence.
        simpl.
        destruct (nrc_eval h ((v1, a) :: env) e3); try reflexivity.
      + destruct (nrc_eval h ((v1, a) :: env) e3); try reflexivity.
    - autorewrite with alg.
      rewrite lift_empty_dcoll.
      rewrite lift_empty_dcoll.
      autorewrite with alg in IHl.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma for_over_if x e1 e2  e3 ebody :
    nnrc_eq (NRCFor x (NRCIf e1 e2 e3) ebody)
            (NRCIf e1 (NRCFor x e2 ebody)
                   (NRCFor x e3 ebody)).
  Proof.
    red; simpl; intros.
    destruct (nrc_eval h env e1); simpl; trivial.
    destruct d; simpl; trivial.
    destruct b; simpl; trivial.
  Qed.
    
  Lemma for_over_either_disjoint x e1 xl el xr er ebody:
    disjoint (xl::xr::nil) (nrc_free_vars ebody) ->
    nnrc_eq (NRCFor x (NRCEither e1 xl el xr er) ebody)
            (NRCEither e1
                       xl (NRCFor x el ebody)
                       xr (NRCFor x er ebody)).
  Proof.
    red; simpl; intros.
    apply disjoint_cons_inv1 in H.
    destruct H as [disj nin1].
    apply disjoint_cons_inv1 in disj.
    destruct disj as [_ nin2].
    destruct (nrc_eval h env e1); simpl; trivial.
    destruct d; simpl; trivial;
      (destruct (equiv_dec (A:=string) xl xl); [|congruence]);
      match_case; simpl; intros; match_destr;
        f_equal;
      apply rmap_ext; intros.
    - generalize (@nrc_eval_remove_free_env _ h ((x,x0)::nil) xl d env ebody); simpl; intros re1; rewrite re1; trivial.
    - generalize (@nrc_eval_remove_free_env _ h ((x,x0)::nil) xr d env ebody); simpl; intros re1; rewrite re1; trivial.
  Qed.

  Lemma nrceither_rename_l e1 xl el xr er xl' :
    ~ In xl' (nrc_free_vars el) ->
    ~ In xl' (nrc_bound_vars el) ->
    nnrc_eq (NRCEither e1 xl el xr er)
            (NRCEither e1 xl' (nrc_subst el xl (NRCVar xl')) xr er).
  Proof.
    red; simpl; intros nfree nbound; intros.
    do 2 match_destr.
    rewrite nrc_eval_cons_subst; trivial.
  Qed.

    Lemma nrceither_rename_r e1 xl el xr er xr' :
    ~ In xr' (nrc_free_vars er) ->
    ~ In xr' (nrc_bound_vars er) ->
    nnrc_eq (NRCEither e1 xl el xr er)
            (NRCEither e1 xl el xr' (nrc_subst er xr (NRCVar xr'))).
  Proof.
    red; simpl; intros nfree nbound; intros.
    do 2 match_destr.
    rewrite nrc_eval_cons_subst; trivial.
  Qed.

  Lemma for_over_either sep x e1 xl el xr er ebody:
    nnrc_eq (NRCFor x (NRCEither e1 xl el xr er) ebody)
            (    let xl' := really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody in
                 let xr' := really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody in
              (NRCEither e1
                       xl' (NRCFor x (nrc_subst el xl (NRCVar xl')) ebody)
                       xr' (NRCFor x (nrc_subst er xr (NRCVar xr')) ebody))).
  Proof.
    simpl.
    transitivity (NRCFor x (NRCEither e1
                                       (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)
                                       (nrc_subst el xl (NRCVar (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)))
                                       (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)
                                       (nrc_subst er xr (NRCVar (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)))) ebody).
    - rewrite <- nrceither_rename_l; simpl.
      rewrite <- nrceither_rename_r; simpl.
      reflexivity.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)
                    (nrc_free_vars er ++ nrc_bound_vars er))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)
                    (nrc_free_vars er ++ nrc_bound_vars er))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)
                    (nrc_free_vars el ++ nrc_bound_vars el))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)
                    (nrc_free_vars el ++ nrc_bound_vars el))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
    - apply for_over_either_disjoint.
      red; simpl; intuition; subst;
        apply really_fresh_from_free in H0; trivial.
  Qed.        

    Lemma nrcunop_over_either op e1 xl el xr er:
      nnrc_eq (NRCUnop op (NRCEither e1 xl el xr er))
              (NRCEither e1 xl (NRCUnop op el) xr (NRCUnop op er)).
    Proof.
      red; simpl; intros.
      repeat match_destr.
    Qed.

    Lemma nrcunop_over_if op e1 e2 e3:
      nnrc_eq (NRCUnop op (NRCIf e1 e2 e3))
              (NRCIf e1 (NRCUnop op e2) (NRCUnop op e3)).
    Proof.
      red; simpl; intros.
      destruct (nrc_eval h env e1); simpl; trivial.
      repeat match_destr.
    Qed.

    (* ♯flatten({ e1 ? { $t1 } : {} | $t1 ∈ { e2 } }) ≡ LET $t1 := e2 IN e1 ? { $t1 } : {} *)

  Lemma sigma_to_if (e1 e2:nrc) (v:var) :
    nnrc_eq
      (NRCUnop AFlatten
               (NRCFor v (NRCUnop AColl e2)
                       (NRCIf e1
                              (NRCUnop AColl (NRCVar v))
                              (NRCConst (dcoll nil)))))
      (NRCLet v e2 (NRCIf e1 (NRCUnop AColl (NRCVar v)) (NRCConst (dcoll nil)))).
  Proof.                        
    unfold nnrc_eq; intros ? ? _.
    simpl.
    destruct (nrc_eval h env e2); try reflexivity; simpl.
    dest_eqdec; try congruence.
    destruct (nrc_eval h ((v,d) :: env) e1); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    destruct b; reflexivity.
  Qed.
    
  Lemma unshadow_free_vars sep renamer (x:var) (e:nrc):
    In x (nrc_free_vars (unshadow sep renamer nil e)) -> In x (nrc_free_vars e).
  Proof.
    rewrite unshadow_nrc_free_vars.
    intros; assumption.
  Qed.

    (** optimizations for record projection *)
  Lemma nrcproject_over_concat sl p1 p2 :
    π[sl](p1 ⊕ p2)
          ≡ᶜ π[sl](p1) ⊕ π[sl](p2).
  Proof.
    red; simpl; intros.
    destruct (nrc_eval h env p2);
      destruct (nrc_eval h env p1); simpl.
    - destruct d; destruct d0; simpl; trivial.
      rewrite rproject_rec_sort_commute, rproject_app.
      trivial.
    - trivial.
    - destruct d; simpl; trivial.
    - trivial.
  Qed.

   Lemma nrcproject_over_const sl l :
    π[sl](NRCConst (drec l)) ≡ᶜ NRCConst (drec (rproject l sl)).
  Proof.
    red; simpl; intros.
    rewrite rproject_rec_sort_commute.
    rewrite rproject_map_fst_same; intuition.
  Qed.
  
  Lemma nrcproject_over_rec_in sl s p :
    In s sl ->
    π[sl](‵[| (s, p) |]) ≡ᶜ ‵[| (s, p) |].
  Proof.
    red; simpl; intros.
    destruct (nrc_eval h env p); simpl; trivial.
    destruct (in_dec string_dec s sl); intuition.
  Qed.

  Lemma nrcproject_over_nrcproject sl1 sl2 p :
    π[sl1](π[sl2](p)) ≡ᶜ π[set_inter string_dec sl2 sl1](p).
  Proof.
    red; simpl; intros.
    destruct (nrc_eval h env p); simpl; trivial.
    destruct d; simpl; trivial.
    rewrite rproject_rproject.
    trivial.
  Qed.

  Lemma nrcproject_over_either sl p xl xr p1 p2 :
    π[sl](NRCEither p xl p1 xr p2) ≡ᶜ NRCEither p xl (π[sl](p1)) xr (π[sl](p2)).
  Proof.
    red; simpl; intros.
    destruct (nrc_eval h env p); simpl; trivial.
    destruct d; simpl; trivial.
  Qed.

End NRew.

Hint Rewrite @sigma_to_if : nrc_rew.
(* Hint Rewrite subst_var_preserves : nrc_rew. *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
