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
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import Decidable.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRSimpRuntime.

Section NNRSimpRewrite.
  Local Open Scope nnrs_imp.

  Context {fruntime:foreign_runtime}.

  Lemma distinct_nil_eq :
    NNRSimpUnop OpDistinct (‵{||}) ≡ᵉ ‵{||}.
  Proof.
    red; simpl; trivial.
  Qed.
  
  Lemma for_nil_eq x e2 :
    (NNRSimpFor x ‵{||} e2) ≡ˢ NNRSimpSkip.
  Proof.
    red; simpl; trivial.
  Qed.
    
  (* renaming *)
  Lemma rename_let_eq x x' e s:
    ~ In x' (nnrs_imp_stmt_free_vars s) ->
    ~ In x' (nnrs_imp_stmt_bound_vars s) ->
    (NNRSimpLet x e s) ≡ˢ
            (NNRSimpLet x' e (nnrs_imp_stmt_rename s x x')).
  Proof.
    intros nin1 nin2.
    red; simpl; intros.
    destruct e; simpl; trivial.
    - apply olift_ext; intros.
      generalize (nnrs_imp_stmt_eval_rename h σc σ s x x' a nin1 nin2)
      ; intros HH.
      unfold var in *.
      repeat match_option_in HH
      ; repeat match_destr_in HH
      ; try contradiction.
      intuition congruence.
    - generalize (nnrs_imp_stmt_eval_rename h σc σ s x x' None nin1 nin2)
      ; intros HH.
      unfold var in *.
      repeat match_option_in HH
      ; repeat match_destr_in HH
      ; try contradiction.
      intuition congruence.
  Qed.

  Lemma rename_for_eq x x' e s:
    ~ In x' (nnrs_imp_stmt_free_vars s) ->
    ~ In x' (nnrs_imp_stmt_bound_vars s) ->
    (NNRSimpFor x e s) ≡ˢ
            (NNRSimpFor x' e (nnrs_imp_stmt_rename s x x')).
  Proof.
    intros nin1 nin2.
    red; simpl; intros.
    match_destr.
    destruct d; simpl; trivial.
    clear dn_σ e.
    revert σ.
    induction l; simpl; trivial; intros σ.
      generalize (nnrs_imp_stmt_eval_rename h σc σ s x x' (Some a) nin1 nin2)
      ; intros HH.
      unfold var in *.
      repeat match_option_in HH
      ; repeat match_destr_in HH
      ; try contradiction.
      intuition congruence.
  Qed.

  Lemma rename_either_l_eq e s₁ x₁ x₁' x₂ s₂:
    ~ In x₁' (nnrs_imp_stmt_free_vars s₁) ->
    ~ In x₁' (nnrs_imp_stmt_bound_vars s₁) ->
    (NNRSimpEither e x₁ s₁ x₂ s₂) ≡ˢ
            (NNRSimpEither e x₁' (nnrs_imp_stmt_rename s₁ x₁ x₁') x₂ s₂).
  Proof.
    intros nin1 nin2.
    red; simpl; intros.
    match_destr.
    destruct d; simpl; trivial.
    generalize (nnrs_imp_stmt_eval_rename h σc σ s₁ x₁ x₁' (Some d) nin1 nin2)
    ; intros HH.
    unfold var in *.
    repeat match_option_in HH
    ; repeat match_destr_in HH
    ; try contradiction.
    intuition congruence.
  Qed.

  Lemma rename_either_r_eq e s₁ x₁ x₂ x₂'  s₂:
    ~ In x₂' (nnrs_imp_stmt_free_vars s₂) ->
    ~ In x₂' (nnrs_imp_stmt_bound_vars s₂) ->
    (NNRSimpEither e x₁ s₁ x₂ s₂) ≡ˢ
            (NNRSimpEither e x₁ s₁ x₂' (nnrs_imp_stmt_rename s₂ x₂ x₂')).
  Proof.
    intros nin1 nin2.
    red; simpl; intros.
    match_destr.
    destruct d; simpl; trivial.
    generalize (nnrs_imp_stmt_eval_rename h σc σ s₂ x₂ x₂' (Some d) nin1 nin2)
    ; intros HH.
    unfold var in *.
    repeat match_option_in HH
    ; repeat match_destr_in HH
    ; try contradiction.
    intuition congruence.
  Qed.
    
  Lemma for_map_eval h σc x₁ expr tmp₁ source σ₁ σ₂ d:
    x₁ <> tmp₁ ->
    ~ In x₁ (nnrs_imp_expr_free_vars expr) ->
    ~ In x₁ (domain σ₁) ->
    nnrs_imp_stmt_eval h σc
                       (NNRSimpFor tmp₁ source
                                   (NNRSimpAssign x₁
                                                  (NNRSimpBinop
                                                     OpBagUnion
                                                     (NNRSimpVar x₁)
                                                     expr))) (σ₁++(x₁,Some (dcoll d))::σ₂) =
    match nnrs_imp_expr_eval h σc (σ₁++(x₁,Some (dcoll d))::σ₂) source with
    | Some (dcoll s) =>
      lift (fun dd => (σ₁++(x₁,Some (dcoll (d++concat dd)))::σ₂))
           (lift_map (fun dd =>
                        match
                          nnrs_imp_expr_eval h σc ((tmp₁, Some dd)::σ₁++σ₂) expr with
                        | Some (dcoll l) => Some l
                        | _ => None
                        end
                     ) s)
    | _ => None
    end.
  Proof.
    simpl; intros neq nin1 nin2.
    match_option.
    destruct d0; trivial.
    clear source eqq.
    revert d.
    induction l; simpl; intros d.
    - rewrite app_nil_r; trivial.
    - unfold var in *.
      destruct (x₁ == tmp₁); try congruence.
      destruct (string_dec x₁ tmp₁); try congruence.
      rewrite lookup_app.
      rewrite lookup_nin_none by trivial.
      unfold id; simpl.
      destruct (x₁ == x₁); try congruence.
      simpl.
      generalize (nnrs_imp_expr_eval_unused h σc ((tmp₁, Some a) :: σ₁) σ₂ expr x₁ (Some (dcoll d))); simpl; intros HH; unfold var in *.
      rewrite HH by tauto; clear HH.
      case_eq (nnrs_imp_expr_eval h σc ((tmp₁, Some a) :: σ₁ ++ σ₂) expr)
      ; simpl; trivial; intros d' eqq.
      destruct d'; simpl; trivial.
      rewrite lookup_app.
      rewrite lookup_nin_none by trivial.
      rewrite update_app_nin by trivial.
      simpl.
      destruct (string_dec x₁ x₁); try congruence.
      rewrite IHl.
      unfold lift.
      match_destr; simpl.
      unfold bunion.
      rewrite app_ass.
      trivial.
  Qed.

    Ltac disect_tac H stac
    := 
      unfold var in *
      ; cut_to H; unfold domain in *; [ | solve[stac]..]
      ; unfold lift2P in H
      ; (repeat match_option_in H; try contradiction).

  Ltac pcong
    := solve[repeat (match goal with
                     | [H: _ = _ |- _ ] => rewrite H in *; clear H
                     end; try tauto)].

  Ltac fuse_t stac
    := repeat progress (
                repeat rewrite in_app_iff in *
                ; repeat
                    match goal with
                    | [H : ~ (_ \/ _ ) |- _ ] => apply not_or in H
                    | [H : (_ \/ _ ) -> False |- _ ] => apply not_or in H
                    | [H: _ /\ _ |- _ ] => destruct H
                    | [ H : _ * _ |- _ ] => destruct H
                    | [H: _::_ = _::_ |- _ ] => invcs H
                    | [ H: domain (_ ++ _) = domain _ |- _ ] =>
                      rewrite domain_app in H
                      ; unfold domain in H
                      ; symmetry in H; apply map_app_break in H
                      ; destruct H as [? [?[?[??]]]]; subst; simpl in *
                    | [ H: map (_ ++ _) = map _ |- _ ] =>
                      rewrite map_app in H
                      ; symmetry in H; apply map_app_break in H
                      ; destruct H as [? [?[?[??]]]]; subst; simpl in *
                    | [ H: _ :: _ = map _ ?x |- _ ] =>
                      destruct x; try discriminate; simpl in H; invcs H
                    | [ H: _ :: _ = domain ?x |- _ ] =>
                      destruct x; try discriminate; simpl in H; invcs H
                    | [H : ~ In _ (remove _ _ _) |- _ ] =>
                      apply not_in_remove_impl_not_in in H; [| congruence]
                    | [H : ?x ++ _ = ?y ++ _ |- _ ] =>
                      let HH := fresh in
                      assert (HH:domain y = domain x) by
                          (unfold domain in *;
                           try (intuition congruence)
                           ; pcong)
                      ; apply app_inv_head_domain in H;[clear HH|apply HH]

                    | [H : nnrs_imp_stmt_eval _ _ _ ?p1 = ?p2 |- _ ] =>
                          apply nnrs_imp_stmt_eval_domain_stack in H

                    | [ H: forall a b c, _ -> ?x1 :: ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                      specialize (H (x1::nil) (snd dd) x2); simpl in H
                      ; match dd with
                        | (_,_) => idtac
                        | _ => destruct dd
                        end
                      ; simpl in *
                      ; cut_to H; [ | eauto 3 | reflexivity]
                    end
                ; simpl in *; trivial; intros; try subst; try contradiction; try solve [congruence | f_equal; congruence]).

    Ltac fuse_tt := fuse_t ltac:(try tauto; try congruence).

  Lemma for_for_fuse_eq x₁ tmp₁ source expr tmp₂ expr₂ tmp₃ body rest :
    x₁ <> tmp₁ ->
    x₁ <> tmp₂ ->
    tmp₂ <> tmp₁ ->
    ~ In x₁ (nnrs_imp_expr_free_vars expr) ->
    ~ In x₁ (nnrs_imp_expr_free_vars source) ->
    ~ In tmp₂ (nnrs_imp_expr_free_vars source) ->
    ~ In tmp₂ (nnrs_imp_expr_free_vars expr) ->
    ~ In tmp₁ (nnrs_imp_stmt_free_vars body) ->
    ~ In x₁ (nnrs_imp_stmt_free_vars body) ->
    ~ In x₁ (nnrs_imp_stmt_free_vars rest) ->
    liftP (fun e => ~ In x₁ (nnrs_imp_expr_free_vars e)) expr₂ ->
    disjoint (nnrs_imp_stmt_maybewritten_vars body) (nnrs_imp_expr_free_vars expr) ->
    NNRSimpLet x₁ (Some (NNRSimpConst (dcoll nil)))
                   (NNRSimpSeq
                      (NNRSimpFor tmp₁ source
                                  (NNRSimpAssign x₁
                                              (NNRSimpBinop
                                                 OpBagUnion
                                                 (NNRSimpVar x₁)
                                                 (NNRSimpUnop OpBag expr))))
                      (NNRSimpLet tmp₂ expr₂
                                  (NNRSimpSeq
                                     (NNRSimpFor tmp₃ (NNRSimpVar x₁)
                                                 body
                                     )
                                     rest)))
                   ≡ˢ
                   (NNRSimpLet tmp₂ expr₂
                               (NNRSimpSeq
                                  (NNRSimpFor tmp₁ source
                                              (NNRSimpLet tmp₃ (Some expr) body))
                                  rest)).
  Proof.
    Ltac match_in_eq_t
      := match goal with
         | [ |- match ?x with | Some _ => _ | None => _ end
                = match ?y with | Some _ => _ | None => _ end] =>
           let eqqq := fresh "eqqq" in
           cut (x=y); [intros eqqq; rewrite eqqq; trivial | ]
         end.

    red; intros neq1 neq2 neq3 nin1 nin2 nin3 nin4 nin5 nin6 nin7 nin8 disj1; intros; simpl.
      generalize (nnrs_imp_expr_eval_unused h σc nil σ source)
      ; simpl; intros HH.
      repeat rewrite HH by tauto.
      generalize (for_map_eval h σc x₁ (NNRSimpUnop OpBag expr) tmp₁ source nil σ []); simpl; intros HH2.
      rewrite HH in HH2 by tauto.
      rewrite HH2 by tauto; clear HH2.
      unfold var in *.
      destruct (x₁ == tmp₁); try congruence; clear c.
      destruct (x₁ == tmp₂); try congruence; clear c.
      case_eq (nnrs_imp_expr_eval h σc σ source)
      ; simpl; [intros ? eqq | intros eqq].
      2: {
           idtac.
           destruct expr₂; simpl; trivial.
           destruct (nnrs_imp_expr_eval h σc σ n); simpl; trivial.
           rewrite HH by tauto.
           rewrite eqq; simpl; trivial.
           }
         
     destruct expr₂; simpl.
     - transitivity (olift
    (fun init : option data =>
     match
       olift (nnrs_imp_stmt_eval h σc rest)
         match nnrs_imp_expr_eval h σc σ source with
         | Some (dcoll c1) =>
             (fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                option (list (string * option data)) :=
                match dl with
                | [] => Some σ₁
                | d1 :: dl' =>
                    match
                      olift
                        (fun init0 : option data =>
                         match
                           nnrs_imp_stmt_eval h σc body ((tmp₃, init0) :: (tmp₁, Some d1) :: σ₁)
                         with
                         | Some (_ :: σ') => Some σ'
                         | _ => None
                         end) (lift Some (nnrs_imp_expr_eval h σc ((tmp₁, Some d1) :: σ₁) expr))
                    with
                    | Some (_ :: σ₂) => for_fun dl' σ₂
                    | _ => None
                    end
                end) c1 ((tmp₂, init) :: σ)
         | _ => None
         end
     with
     | Some (_ :: σ') => Some σ'
     | _ => None
     end) (lift Some (nnrs_imp_expr_eval h σc σ n))).
             2: { idtac.
                  destruct (lift Some (nnrs_imp_expr_eval h σc σ n)); simpl; trivial.
                  match_in_eq_t.
                  f_equal.
                  rewrite HH by tauto.
                  rewrite eqq; trivial.
                  }
         rewrite eqq.
         destruct d; simpl
         ; try solve [unfold olift; match_destr].
         repeat rewrite olift_lift.
         simpl.
         destruct (x₁ == x₁); [| congruence].
         unfold id; simpl.
         (* remove unneeded x₁ from n evaluation *)
         transitivity (
             match
               olift
                 (fun x : list (list data) =>
                    olift
                      (fun init : option data =>
                         match
                           olift (nnrs_imp_stmt_eval h σc rest)
                                 ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                                     option (list (string * option data)) :=
                                     match dl with
                                     | [] => Some σ₁
                                     | d :: dl' =>
                                       match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d) :: σ₁) with
                                       | Some (_ :: σ₂) => for_fun dl' σ₂
                                       | _ => None
                                       end
                                     end) (concat x) ((tmp₂, init) :: (x₁, Some (dcoll (concat x))) :: σ))
                         with
                         | Some (_ :: σ') => Some σ'
                         | _ => None
                         end) (lift Some (nnrs_imp_expr_eval h σc  σ n)))
                 (lift_map
                    (fun dd : data =>
                       match
                         olift (fun d : data => Some (dcoll [d]))
                               (nnrs_imp_expr_eval h σc ((tmp₁, Some dd) :: σ) expr)
                       with
                       | Some (dcoll l0) => Some l0
                       | _ => None
                       end) l)
             with
             | Some (_ :: σ') => Some σ'
             | _ => None
             end).
         {
           match_in_eq_t.
           apply olift_ext; intros.
           generalize (nnrs_imp_expr_eval_unused h σc nil σ n)
           ; simpl; intros HH2.
           repeat rewrite HH2 by tauto.
           trivial.
         }
         rewrite olift_commute.
         case_eq (nnrs_imp_expr_eval h σc σ n); simpl; trivial
         ; intros ? eqq1.
         replace (lift_map
         (fun dd : data =>
          match
            olift (fun d0 : data => Some (dcoll [d0]))
              (nnrs_imp_expr_eval h σc ((tmp₁, Some dd) :: σ) expr)
          with
          | Some (dcoll l0) => Some l0
          | _ => None
          end) l) with
             (lift_map
         (fun dd : data =>
            lift (fun d0 : data => [d0])
                 (nnrs_imp_expr_eval h σc ((tmp₁, Some dd) :: σ) expr)) l).
         2: { idtac.
              apply lift_map_ext; intros.
              destruct ((nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr)); simpl; trivial.
              }
            rewrite lift_map_lift.
              rewrite olift_lift.
              (* simplify the concat *)
              transitivity (match
    olift
      (fun x : list data =>
       match
         olift (nnrs_imp_stmt_eval h σc rest)
           ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
               option (list (string * option data)) :=
               match dl with
               | [] => Some σ₁
               | d0 :: dl' =>
                   match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                   | Some (_ :: σ₂) => for_fun dl' σ₂
                   | _ => None
                   end
               end) x
              ((tmp₂, Some d)
               :: (x₁, Some (dcoll x)) :: σ))
       with
       | Some (_ :: σ') => Some σ'
       | _ => None
       end) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                match_in_eq_t.
                f_equal.
                rewrite <- flat_map_concat_map, flat_map_singleton; trivial.
              }

              transitivity (match
    olift
      (fun x : list data =>
       match
         olift (nnrs_imp_stmt_eval h σc rest)
               (lift (fun σ =>
                        match σ with
                        | xx::σ' => (xx::(x₁, Some (dcoll x))::σ')
                        | _ => σ
                        end)
                  ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
               option (list (string * option data)) :=
               match dl with
               | [] => Some σ₁
               | d0 :: dl' =>
                   match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                   | Some (_ :: σ₂) => for_fun dl' σ₂
                   | _ => None
                   end
               end) x ((tmp₂, Some d):: σ)))
       with
       | Some (_ :: σ') => Some σ'
       | _ => None
       end) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                match_in_eq_t.
                f_equal.
                clear HH eqq eqq1 H.
                clear dn_σ.
                revert σ.
                generalize (dcoll a).
                generalize (Some d).
                induction a; simpl; trivial; intros o dd σ.
                generalize (nnrs_imp_stmt_eval_unused h σc ((tmp₃, Some a)::(tmp₂, o)::nil) σ body x₁ (Some dd)); simpl; intros HH1.
                cut_to HH1; [| tauto..].
                unfold lift2P in HH1.
                unfold var in *.
                repeat match_option_in HH1
                ; fuse_tt.
                specialize (HH1 ((s, o2) :: (s0, o3)::nil) o4 p0).
                cut_to HH1; simpl; try tauto.
                fuse_tt.
              }

              transitivity (match
    olift
      (fun x : list data =>
       match
         olift (fun σ => (olift
              (fun σ0 : list (string * option data) =>
               match σ0 with
               | [] => None
               | xx :: σ' => Some (xx :: (x₁, Some (dcoll x)) :: σ')
               end) (nnrs_imp_stmt_eval h σc rest σ)))
              ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                  option (list (string * option data)) :=
                  match dl with
                  | [] => Some σ₁
                  | d0 :: dl' =>
                      match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                      | Some (_ :: σ₂) => for_fun dl' σ₂
                      | _ => None
                      end
                  end) x ((tmp₂, Some d) :: σ))
       with
       | Some (_ :: σ') => Some σ'
       | _ => None
       end) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end ).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                match_in_eq_t.
                rewrite olift_lift.
                apply olift_ext; intros.
                assert (domain ((tmp₂, Some d) :: σ) = domain a0).
                {
                  revert H0; clear.
                  generalize ((tmp₂, Some d)).
                  revert σ a0.
                  induction a; simpl; intros.
                  + invcs H0; simpl; trivial.
                  + match_option_in H0.
                    match_destr_in H0.
                    fuse_tt.
                    specialize (IHa _ _ _ H0).
                    simpl in *.
                    congruence.
                }
                simpl in H1.
                destruct a0; try discriminate.
                generalize (nnrs_imp_stmt_eval_unused h σc (p::nil) a0 rest x₁ (Some (dcoll a))); simpl; intros HH1.
                cut_to HH1; [| tauto..].
                unfold lift2P in HH1.
                unfold var in *.
                repeat match_option_in HH1
                ; fuse_tt.
              }
              transitivity (match
    olift
      (fun x : list data =>
           (olift
              (fun σ0 : list (string * option data) =>
                 match σ0 with
                 | [] => None
                 | xx :: σ' => Some ((x₁, Some (dcoll x)) :: σ')
                 end)
         (olift (nnrs_imp_stmt_eval h σc rest)
              ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                  option (list (string * option data)) :=
                  match dl with
                  | [] => Some σ₁
                  | d0 :: dl' =>
                      match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                      | Some (_ :: σ₂) => for_fun dl' σ₂
                      | _ => None
                      end
                  end) x ((tmp₂, Some d) :: σ))))
) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                destruct (((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
          option (list (string * option data)) :=
          match dl with
          | [] => Some σ₁
          | d0 :: dl' =>
              match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
              | Some (_ :: σ₂) => for_fun dl' σ₂
              | _ => None
              end
          end) a ((tmp₂, Some d) :: σ))); simpl; trivial.
                destruct (nnrs_imp_stmt_eval h σc rest l0); simpl; trivial.
                destruct p; simpl; trivial.
              }
              (* finally we can get rid of the extra x₁ *)
              transitivity (match
                               olift
                                 (fun x : list data =>
                                    (olift (nnrs_imp_stmt_eval h σc rest)
                                           ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                                               option (list (string * option data)) :=
                match dl with
                | [] => Some σ₁
                | d0 :: dl' =>
                    match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                    | Some (_ :: σ₂) => for_fun dl' σ₂
                    | _ => None
                    end
                end) x ((tmp₂, Some d) :: σ))))
      (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                destruct ((lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)); simpl; trivial.
                destruct ((olift (nnrs_imp_stmt_eval h σc rest)
         ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
             option (list (string * option data)) :=
             match dl with
             | [] => Some σ₁
             | d0 :: dl' =>
                 match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                 | Some (_ :: σ₂) => for_fun dl' σ₂
                 | _ => None
                 end
             end) l0 ((tmp₂, Some d) :: σ)))); simpl; trivial.
                destruct p; simpl; trivial.
              }

              (* swap the olifts *)
              transitivity (match
       olift (nnrs_imp_stmt_eval h σc rest)
             (olift
                (fun x : list data =>
         ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
             option (list (string * option data)) :=
             match dl with
             | [] => Some σ₁
             | d0 :: dl' =>
                 match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                 | Some (_ :: σ₂) => for_fun dl' σ₂
                 | _ => None
                 end
             end) x ((tmp₂, Some d) :: σ)))
      (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l))
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
  end ).
              {
                match_in_eq_t.
                destruct ((lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)); simpl; trivial.
              }

              (* now, let's work on geting rid of the tmp₁ on the other side *)
              transitivity (match
    olift (nnrs_imp_stmt_eval h σc rest)
      ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
          option (list (string * option data)) :=
          match dl with
          | [] => Some σ₁
          | d1 :: dl' =>
              match
                olift
                  (fun init0 : option data =>
                   match
                     nnrs_imp_stmt_eval h σc body ((tmp₃, init0) :: σ₁)
                   with
                   | Some (_ :: σ') => Some ( (tmp₁, Some d1)::σ')
                   | _ => None
                   end) (lift Some (nnrs_imp_expr_eval h σc ((tmp₁, Some d1) :: σ₁) expr))
              with
              | Some (_ :: σ₂) => for_fun dl' σ₂
              | _ => None
              end
          end) l ((tmp₂, Some d) :: σ))
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              2: { idtac.
                   match_in_eq_t.
                   f_equal.
                   generalize (((tmp₂, Some d) :: σ)).
                   clear eqq.
                   induction l; simpl; trivial; intros.
                   destruct ((lift Some (nnrs_imp_expr_eval h σc ((tmp₁, Some a) :: l0) expr))); simpl; trivial.
                   generalize (nnrs_imp_stmt_eval_unused h σc ((tmp₃, o)::nil) l0 body tmp₁ (Some a)); simpl; intros HH1.
                cut_to HH1; [| tauto..].
                unfold lift2P in HH1.
                unfold var in *.
                repeat match_option_in HH1
                ; fuse_tt.
                   }

                 (* now that we have moved out the tmp₁, eliminate it *)
                 (* also simplify the lift Some *)
                 transitivity (   match
    olift (nnrs_imp_stmt_eval h σc rest)
      ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
          option (list (string * option data)) :=
          match dl with
          | [] => Some σ₁
          | d1 :: dl' =>
              match
                olift
                  (fun init0 : data =>
                   nnrs_imp_stmt_eval h σc body ((tmp₃, Some init0) :: σ₁) 
                   ) (nnrs_imp_expr_eval h σc ((tmp₁, Some d1) :: σ₁) expr)
              with
              | Some (_ :: σ₂) => for_fun dl' σ₂
              | _ => None
              end
          end) l ((tmp₂, Some d) :: σ))
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
  end).
                   2: { idtac.
                        match_in_eq_t.
                        f_equal.
                        clear.
                        generalize ((tmp₂, Some d) :: σ).
                        induction l; simpl; intros; trivial.
                        destruct ((nnrs_imp_expr_eval h σc ((tmp₁, Some a) :: l0) expr)); simpl; trivial.
                        destruct (nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: l0) ); simpl; trivial.
                        destruct p; simpl; trivial.
                        }
                      match_in_eq_t.
                      f_equal.
                      clear HH eqq e eqq1.
                      generalize (Some d); clear d.
                      clear dn_σ.
                      revert σ.
                      induction l; simpl; trivial; intros σ o.
                      generalize (nnrs_imp_expr_eval_unused h σc ((tmp₁, Some a)::nil) σ expr)
                      ; simpl; intros HH1.
                      repeat rewrite HH1 by tauto; clear HH1.
                      unfold var in *.
                      destruct (nnrs_imp_expr_eval h σc ((tmp₁, Some a) :: σ) expr)
                      ; simpl; trivial.
                      rewrite olift_lift.
                      (* the body evaluation is independent, so we can pull it out *)
                      transitivity (
     match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d) :: (tmp₂, o) :: σ) with
     | Some (_ :: σ₂) =>
       olift (fun x : list data =>
         (fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
            option (list (string * option data)) :=
            match dl with
            | [] => Some σ₁
            | d0 :: dl' =>
                match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                | Some (_ :: σ₂0) => for_fun dl' σ₂0
                | _ => None
                end
            end) x σ₂)
             (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
     | _ => None
     end).
                      {
                        clear.
                        destruct (nnrs_imp_stmt_eval h σc body ((tmp₃, Some d) :: (tmp₂, o) :: σ))
                        ; destruct ((lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)); simpl; trivial.
                        match_destr.
                      }
                      match_option.
                      generalize (nnrs_imp_stmt_eval_domain_stack eqq)
                      ; simpl ; intros eqq1.
                      destruct p; simpl in *; try discriminate.
                      destruct p.
                      invcs eqq1.
                      destruct p0; simpl in *; try discriminate.
                      destruct p.
                      invcs H1.
                      rewrite <- IHl.
                      f_equal.
                      apply lift_map_ext; intros.
                      apply nnrs_imp_expr_eval_same.
                      red; simpl; intros dd inn.
                      destruct (string_eqdec dd tmp₁); simpl; trivial.
                      apply (nnrs_imp_stmt_eval_lookup_preserves_unwritten
                                    ((s, Some d) :: (s0, o)::nil)
                                    ((s, o0) :: (s0, o1)::nil) _ _ eqq (eq_refl _))
                      ; simpl.
                      right.
                      intros inn2.
                      apply (disj1 dd); trivial.
                        - destruct d; simpl; trivial.
         repeat rewrite olift_lift.
         simpl.
         destruct (x₁ == x₁); [| congruence].
         unfold id; simpl.
         replace (lift_map
         (fun dd : data =>
          match
            olift (fun d0 : data => Some (dcoll [d0]))
              (nnrs_imp_expr_eval h σc ((tmp₁, Some dd) :: σ) expr)
          with
          | Some (dcoll l0) => Some l0
          | _ => None
          end) l) with
             (lift_map
         (fun dd : data =>
            lift (fun d0 : data => [d0])
                 (nnrs_imp_expr_eval h σc ((tmp₁, Some dd) :: σ) expr)) l).
         2: { idtac.
              apply lift_map_ext; intros.
              destruct ((nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr)); simpl; trivial.
              }
            rewrite lift_map_lift.
              rewrite olift_lift.
              (* simplify the concat *)
              transitivity (match
    olift
      (fun x : list data =>
       match
         olift (nnrs_imp_stmt_eval h σc rest)
           ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
               option (list (string * option data)) :=
               match dl with
               | [] => Some σ₁
               | d0 :: dl' =>
                   match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                   | Some (_ :: σ₂) => for_fun dl' σ₂
                   | _ => None
                   end
               end) x
              ((tmp₂, None)
               :: (x₁, Some (dcoll x)) :: σ))
       with
       | Some (_ :: σ') => Some σ'
       | _ => None
       end) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                match_in_eq_t.
                f_equal.
                rewrite <- flat_map_concat_map, flat_map_singleton; trivial.
              }

              transitivity (match
    olift
      (fun x : list data =>
       match
         olift (nnrs_imp_stmt_eval h σc rest)
               (lift (fun σ =>
                        match σ with
                        | xx::σ' => (xx::(x₁, Some (dcoll x))::σ')
                        | _ => σ
                        end)
                  ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
               option (list (string * option data)) :=
               match dl with
               | [] => Some σ₁
               | d0 :: dl' =>
                   match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                   | Some (_ :: σ₂) => for_fun dl' σ₂
                   | _ => None
                   end
               end) x ((tmp₂, None):: σ)))
       with
       | Some (_ :: σ') => Some σ'
       | _ => None
       end) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                match_in_eq_t.
                f_equal.
                clear HH eqq H.
                clear dn_σ.
                revert σ.
                generalize (dcoll a).
                generalize ((@None (@data (@foreign_runtime_data fruntime)))).
                induction a; simpl; trivial; intros o dd σ.
                generalize (nnrs_imp_stmt_eval_unused h σc ((tmp₃, Some a)::(tmp₂, o)::nil) σ body x₁ (Some dd)); simpl; intros HH1.
                cut_to HH1; [| tauto..].
                unfold lift2P in HH1.
                unfold var in *.
                repeat match_option_in HH1
                ; fuse_tt.
                specialize (HH1 ((s, o2) :: (s0, o3)::nil) o4 p0).
                cut_to HH1; simpl; try tauto.
                fuse_tt.
              }

              transitivity (match
    olift
      (fun x : list data =>
       match
         olift (fun σ => (olift
              (fun σ0 : list (string * option data) =>
               match σ0 with
               | [] => None
               | xx :: σ' => Some (xx :: (x₁, Some (dcoll x)) :: σ')
               end) (nnrs_imp_stmt_eval h σc rest σ)))
              ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                  option (list (string * option data)) :=
                  match dl with
                  | [] => Some σ₁
                  | d0 :: dl' =>
                      match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                      | Some (_ :: σ₂) => for_fun dl' σ₂
                      | _ => None
                      end
                  end) x ((tmp₂, None) :: σ))
       with
       | Some (_ :: σ') => Some σ'
       | _ => None
       end) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end ).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                match_in_eq_t.
                rewrite olift_lift.
                apply olift_ext; intros.
                assert (domain ((tmp₂, None) :: σ) = domain a0).
                {
                  revert H0; clear.
                  generalize ((tmp₂, (@None (@data (@foreign_runtime_data fruntime))))).
                  revert σ a0.
                  induction a; simpl; intros.
                  + invcs H0; simpl; trivial.
                  + match_option_in H0.
                    match_destr_in H0.
                    fuse_tt.
                    specialize (IHa _ _ _ H0).
                    simpl in *.
                    congruence.
                }
                simpl in H1.
                destruct a0; try discriminate.
                generalize (nnrs_imp_stmt_eval_unused h σc (p::nil) a0 rest x₁ (Some (dcoll a))); simpl; intros HH1.
                cut_to HH1; [| tauto..].
                unfold lift2P in HH1.
                unfold var in *.
                repeat match_option_in HH1
                ; fuse_tt.
              }
              transitivity (match
    olift
      (fun x : list data =>
           (olift
              (fun σ0 : list (string * option data) =>
                 match σ0 with
                 | [] => None
                 | xx :: σ' => Some ((x₁, Some (dcoll x)) :: σ')
                 end)
         (olift (nnrs_imp_stmt_eval h σc rest)
              ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                  option (list (string * option data)) :=
                  match dl with
                  | [] => Some σ₁
                  | d0 :: dl' =>
                      match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                      | Some (_ :: σ₂) => for_fun dl' σ₂
                      | _ => None
                      end
                  end) x ((tmp₂, None) :: σ))))
) (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                match_in_eq_t.
                apply olift_ext; intros.
                destruct (((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
          option (list (string * option data)) :=
          match dl with
          | [] => Some σ₁
          | d0 :: dl' =>
              match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
              | Some (_ :: σ₂) => for_fun dl' σ₂
              | _ => None
              end
          end) a ((tmp₂, None) :: σ))); simpl; trivial.
                destruct (nnrs_imp_stmt_eval h σc rest l0); simpl; trivial.
                destruct p; simpl; trivial.
              }
              (* finally we can get rid of the extra x₁ *)
              transitivity (match
                               olift
                                 (fun x : list data =>
                                    (olift (nnrs_imp_stmt_eval h σc rest)
                                           ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
                                               option (list (string * option data)) :=
                match dl with
                | [] => Some σ₁
                | d0 :: dl' =>
                    match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                    | Some (_ :: σ₂) => for_fun dl' σ₂
                    | _ => None
                    end
                end) x ((tmp₂, None) :: σ))))
      (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              {
                destruct ((lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)); simpl; trivial.
                destruct ((olift (nnrs_imp_stmt_eval h σc rest)
         ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
             option (list (string * option data)) :=
             match dl with
             | [] => Some σ₁
             | d0 :: dl' =>
                 match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                 | Some (_ :: σ₂) => for_fun dl' σ₂
                 | _ => None
                 end
             end) l0 ((tmp₂, None) :: σ)))); simpl; trivial.
                destruct p; simpl; trivial.
              }

              (* swap the olifts *)
              transitivity (match
       olift (nnrs_imp_stmt_eval h σc rest)
             (olift
                (fun x : list data =>
         ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
             option (list (string * option data)) :=
             match dl with
             | [] => Some σ₁
             | d0 :: dl' =>
                 match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                 | Some (_ :: σ₂) => for_fun dl' σ₂
                 | _ => None
                 end
             end) x ((tmp₂, None) :: σ)))
      (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l))
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
  end ).
              {
                match_in_eq_t.
                destruct ((lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)); simpl; trivial.
              }

              (* now, let's work on geting rid of the tmp₁ on the other side *)
              transitivity (match
    olift (nnrs_imp_stmt_eval h σc rest)
      ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
          option (list (string * option data)) :=
          match dl with
          | [] => Some σ₁
          | d1 :: dl' =>
              match
                olift
                  (fun init0 : option data =>
                   match
                     nnrs_imp_stmt_eval h σc body ((tmp₃, init0) :: σ₁)
                   with
                   | Some (_ :: σ') => Some ( (tmp₁, Some d1)::σ')
                   | _ => None
                   end) (lift Some (nnrs_imp_expr_eval h σc ((tmp₁, Some d1) :: σ₁) expr))
              with
              | Some (_ :: σ₂) => for_fun dl' σ₂
              | _ => None
              end
          end) l ((tmp₂, None) :: σ))
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
                             end).
              2: { idtac.
                   match_in_eq_t.
                   f_equal.
                   generalize (((tmp₂, None) :: σ)).
                   clear eqq.
                   induction l; simpl; trivial; intros.
                   destruct ((lift Some (nnrs_imp_expr_eval h σc ((tmp₁, Some a) :: l0) expr))); simpl; trivial.
                   generalize (nnrs_imp_stmt_eval_unused h σc ((tmp₃, o)::nil) l0 body tmp₁ (Some a)); simpl; intros HH1.
                cut_to HH1; [| tauto..].
                unfold lift2P in HH1.
                unfold var in *.
                repeat match_option_in HH1
                ; fuse_tt.
                   }

                 (* now that we have moved out the tmp₁, eliminate it *)
                 (* also simplify the lift Some *)
                 transitivity (   match
    olift (nnrs_imp_stmt_eval h σc rest)
      ((fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
          option (list (string * option data)) :=
          match dl with
          | [] => Some σ₁
          | d1 :: dl' =>
              match
                olift
                  (fun init0 : data =>
                   nnrs_imp_stmt_eval h σc body ((tmp₃, Some init0) :: σ₁) 
                   ) (nnrs_imp_expr_eval h σc ((tmp₁, Some d1) :: σ₁) expr)
              with
              | Some (_ :: σ₂) => for_fun dl' σ₂
              | _ => None
              end
          end) l ((tmp₂, None) :: σ))
  with
  | Some (_ :: σ') => Some σ'
  | _ => None
  end).
                   2: { idtac.
                        match_in_eq_t.
                        f_equal.
                        clear.
                        generalize ((tmp₂, None) :: σ).
                        induction l; simpl; intros; trivial.
                        destruct ((nnrs_imp_expr_eval h σc ((tmp₁, Some a) :: l0) expr)); simpl; trivial.
                        destruct (nnrs_imp_stmt_eval h σc body ((tmp₃, Some d) :: l0) ); simpl; trivial.
                        destruct p; simpl; trivial.
                        }
                      match_in_eq_t.
                      f_equal.
                      clear HH eqq e.
                      generalize ((@None (@data (@foreign_runtime_data fruntime)))).
                      clear dn_σ.
                      revert σ.
                      induction l; simpl; trivial; intros σ o.
                      generalize (nnrs_imp_expr_eval_unused h σc ((tmp₁, Some a)::nil) σ expr)
                      ; simpl; intros HH1.
                      repeat rewrite HH1 by tauto; clear HH1.
                      unfold var in *.
                      destruct (nnrs_imp_expr_eval h σc ((tmp₁, Some a) :: σ) expr)
                      ; simpl; trivial.
                      rewrite olift_lift.
                      (* the body evaluation is independent, so we can pull it out *)
                      transitivity (
     match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d) :: (tmp₂, o) :: σ) with
     | Some (_ :: σ₂) =>
       olift (fun x : list data =>
         (fix for_fun (dl : list data) (σ₁ : list (string * option data)) {struct dl} :
            option (list (string * option data)) :=
            match dl with
            | [] => Some σ₁
            | d0 :: dl' =>
                match nnrs_imp_stmt_eval h σc body ((tmp₃, Some d0) :: σ₁) with
                | Some (_ :: σ₂0) => for_fun dl' σ₂0
                | _ => None
                end
            end) x σ₂)
             (lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)
     | _ => None
     end).
     {
       clear.
       destruct (nnrs_imp_stmt_eval h σc body ((tmp₃, Some d) :: (tmp₂, o) :: σ))
       ; destruct ((lift_map (fun x : data => nnrs_imp_expr_eval h σc ((tmp₁, Some x) :: σ) expr) l)); simpl; trivial.
       match_destr.
     }
     match_option.
     generalize (nnrs_imp_stmt_eval_domain_stack eqq)
     ; simpl ; intros eqq1.
     destruct p; simpl in *; try discriminate.
     destruct p.
     invcs eqq1.
     destruct p0; simpl in *; try discriminate.
     destruct p.
     invcs H1.
     rewrite <- IHl.
     f_equal.
     apply lift_map_ext; intros.
     apply nnrs_imp_expr_eval_same.
     red; simpl; intros dd inn.
     destruct (string_eqdec dd tmp₁); simpl; trivial.
     apply (nnrs_imp_stmt_eval_lookup_preserves_unwritten
              ((s, Some d) :: (s0, o)::nil)
              ((s, o0) :: (s0, o1)::nil) _ _ eqq (eq_refl _))
     ; simpl.
     right.
     intros inn2.
     apply (disj1 dd); trivial.
    Qed.

End NNRSimpRewrite.

