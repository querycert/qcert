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
Require Import Bool.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import Decidable.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRSimpRuntime.

Section NNRSimpUnflatten.
  Local Open Scope nnrs_imp.

  Context {fruntime:foreign_runtime}.

  Section unflatten.
    (* This should really be done via (backwards propagating) dataflow analysis, 
     but we don't currently have a dataflow analysis set up. 
     For a single variable, this should work; although it will not see through
     assignments *)

    Section def.

      Fixpoint nnrs_imp_expr_unflatten_init (e:nnrs_imp_expr) : option nnrs_imp_expr
        := match e with
           | NNRSimpBinop OpBagUnion e₁ e₂ =>
             lift2 (NNRSimpBinop OpBagUnion)
                   (nnrs_imp_expr_unflatten_init e₁)
                   (nnrs_imp_expr_unflatten_init e₂)
           | NNRSimpUnop OpBag (NNRSimpConst (dcoll l)) =>
             Some (NNRSimpConst (dcoll l))
           | NNRSimpUnop OpBag (NNRSimpUnop OpBag e₁) =>
             Some (NNRSimpUnop OpBag e₁)
           | NNRSimpConst (dcoll nil) =>
             Some (NNRSimpConst (dcoll nil))
           | NNRSimpConst (dcoll ((dcoll l)::nil)) =>
             Some (NNRSimpConst (dcoll l))
           | _ => None
           end.

      Definition nnrs_imp_expr_unflatten_init_option (oe:option nnrs_imp_expr) 
        : option (option nnrs_imp_expr)
        := match oe with
           | Some e => lift Some (nnrs_imp_expr_unflatten_init e)
           | None => Some None
           end.

      Fixpoint nnrs_imp_expr_unflatten_read (e:nnrs_imp_expr) (v:var) : option nnrs_imp_expr
        := match e with
           | NNRSimpVar x =>
             if x == v
             then None
             else Some (NNRSimpVar x)
           | NNRSimpUnop OpFlatten (NNRSimpVar x) =>
             if x == v
             then Some (NNRSimpVar x)
             else Some (NNRSimpUnop OpFlatten (NNRSimpVar x) )
           | NNRSimpGetConstant x =>
             Some (NNRSimpGetConstant x)
           | NNRSimpConst d =>
             Some (NNRSimpConst d)
           | NNRSimpUnop u e₁ =>
             lift (NNRSimpUnop u)
                  (nnrs_imp_expr_unflatten_read e₁ v)
           | NNRSimpBinop b e₁ e₂ =>
             lift2 (NNRSimpBinop b)
                   (nnrs_imp_expr_unflatten_read e₁ v)
                   (nnrs_imp_expr_unflatten_read e₂ v)
           | NNRSimpGroupBy g sl e₁ =>
             lift (NNRSimpGroupBy g sl) (nnrs_imp_expr_unflatten_read e₁ v)
           end.

      Definition nnrs_imp_expr_unflatten_read_option (oe:option nnrs_imp_expr) (v:var)
        : option (option nnrs_imp_expr)
        := match oe with
           | Some e => lift Some (nnrs_imp_expr_unflatten_read e v)
           | None => Some None
           end.

      Fixpoint nnrs_imp_expr_unflatten_write (e:nnrs_imp_expr) (v:var) : option nnrs_imp_expr
        := match e with
           | NNRSimpVar x =>
             if x == v
             then Some (NNRSimpVar x)
             else None
           | NNRSimpBinop OpBagUnion e₁ e₂ =>
             lift2 (NNRSimpBinop OpBagUnion)
                   (nnrs_imp_expr_unflatten_write e₁ v)
                   (nnrs_imp_expr_unflatten_write e₂ v)
           | NNRSimpUnop OpBag e₁ =>
             if in_dec string_dec v (nnrs_imp_expr_free_vars e₁)
             then None
             else Some e₁
           | NNRSimpConst (dcoll nil) =>
             Some (NNRSimpConst (dcoll nil))
           | NNRSimpConst (dcoll ((dcoll l)::nil)) =>
             Some (NNRSimpConst (dcoll l))
           | _ => None
           end.

      Definition lift3 {A B C D} (f:A->B->C->D) x y z
        := match x, y, z with
           | Some x, Some y, Some z => Some (f x y z)
           | _, _, _ => None
           end.
      
      Fixpoint nnrs_imp_stmt_unflatten (s:nnrs_imp_stmt) (v:var) : option nnrs_imp_stmt
        := match s with
           | NNRSimpSkip =>
             Some NNRSimpSkip
           | NNRSimpSeq s₁ s₂ =>
             lift2 NNRSimpSeq
                   (nnrs_imp_stmt_unflatten s₁ v)
                   (nnrs_imp_stmt_unflatten s₂ v)
           | NNRSimpAssign x e =>
             lift (NNRSimpAssign x)
                  (if x == v
                   then nnrs_imp_expr_unflatten_write e v
                   else nnrs_imp_expr_unflatten_read e v)
           | NNRSimpLet x oe s₁ =>
             lift2 (NNRSimpLet x)
                   (nnrs_imp_expr_unflatten_read_option oe v)
                   (if x == v then Some s₁ else nnrs_imp_stmt_unflatten s₁ v)
           | NNRSimpFor x e s₁ =>
             lift2 (NNRSimpFor x)
                   (nnrs_imp_expr_unflatten_read e v)
                   (if x == v then Some s₁ else nnrs_imp_stmt_unflatten s₁ v)
           | NNRSimpIf e s₁ s₂ =>
             lift3 NNRSimpIf
                   (nnrs_imp_expr_unflatten_read e v)
                   (nnrs_imp_stmt_unflatten s₁ v)
                   (nnrs_imp_stmt_unflatten s₂ v)
           | NNRSimpEither e x₁ s₁ x₂ s₂ =>
             lift3 (fun e s₁ s₂ => NNRSimpEither e x₁ s₁ x₂ s₂)
                   (nnrs_imp_expr_unflatten_read e v)
                   (if x₁ == v then Some s₁ else nnrs_imp_stmt_unflatten s₁ v)
                   (if x₂ == v then Some s₂ else nnrs_imp_stmt_unflatten s₂ v)
           end.

      Section safe.

        Fixpoint nnrs_imp_stmt_read_out (s:nnrs_imp_stmt) (v:var) : bool
          := match s with
             | NNRSimpSkip => false
             | NNRSimpSeq s₁ s₂ =>
               nnrs_imp_stmt_read_out s₁ v
               || nnrs_imp_stmt_read_out s₂ v
             | NNRSimpAssign x e =>
               (x <>b v) && nnrs_imp_expr_may_use e v
             | NNRSimpLet x oe s₁ =>
               match oe with
               | Some e => nnrs_imp_expr_may_use e v
               | None => false
               end
               || ((x <>b v) && nnrs_imp_stmt_read_out s₁ v)
             | NNRSimpFor x e s₁ =>
               nnrs_imp_expr_may_use e v
               || ((x <>b v) && nnrs_imp_stmt_read_out s₁ v)
             | NNRSimpIf e s₁ s₂ =>
               nnrs_imp_expr_may_use e v
               || nnrs_imp_stmt_read_out s₁ v
               || nnrs_imp_stmt_read_out s₂ v
             | NNRSimpEither e x₁ s₁ x₂ s₂ =>
               nnrs_imp_expr_may_use e v
               || ((x₁ <>b v) && nnrs_imp_stmt_read_out s₁ v)
               || ((x₂ <>b v) && nnrs_imp_stmt_read_out s₂ v)
             end.
        
        Definition nnrs_imp_stmt_unflatten_safe s v : option nnrs_imp_stmt
          := if nnrs_imp_stmt_read_out s v
             then nnrs_imp_stmt_unflatten s v
             else None.

      End safe.

    End def.

    Section ident.
      
      Lemma nnrs_imp_expr_unflatten_read_nfree_id {e v}:
        ~ In v (nnrs_imp_expr_free_vars e) ->
        nnrs_imp_expr_unflatten_read e v = Some e.
      Proof.
        nnrs_imp_expr_cases (induction e) Case
        ; simpl; intros nfree
        ; trivial.
        - Case "NNRSimpVar"%string.
          match_destr.
          tauto.
        - Case "NNRSimpBinop"%string.
          rewrite in_app_iff in *.
          rewrite IHe1, IHe2; tauto.
        - Case "NNRSimpUnop"%string.
          rewrite IHe by tauto.
          destruct u; simpl; try reflexivity.
          destruct e; simpl; try reflexivity.
          destruct (equiv_dec v0 v); try reflexivity.
          simpl in *; tauto.
        - Case "NNRSimpGroupBy"%string.
          rewrite IHe; tauto.
      Qed.

      Lemma nnrs_imp_stmt_unflatten_nfree_id {s v}:
        ~ In v (nnrs_imp_stmt_free_vars s) ->
        nnrs_imp_stmt_unflatten s v = Some s.
      Proof.
        nnrs_imp_stmt_cases (induction s) Case
        ; simpl; repeat rewrite in_app_iff; intros nfree
        ; trivial.
        - Case "NNRSimpSeq"%string.
          rewrite IHs1, IHs2; eauto.
        - Case "NNRSimpAssign"%string.
          match_destr; try tauto.
          rewrite nnrs_imp_expr_unflatten_read_nfree_id; tauto.
        - Case "NNRSimpLet"%string.
          destruct o; simpl.
          + rewrite nnrs_imp_expr_unflatten_read_nfree_id by tauto.
            simpl.
            destruct (equiv_dec v0 v); trivial.
            rewrite IHs; intuition.
            apply remove_nin_inv in H1.
            intuition.
          + destruct (equiv_dec v0 v); trivial.
            rewrite IHs; intuition.
            apply remove_nin_inv in H1.
            intuition.
        - Case "NNRSimpFor"%string.
          rewrite nnrs_imp_expr_unflatten_read_nfree_id by tauto.
          destruct (equiv_dec v0 v); trivial.
          rewrite IHs; intuition.
          apply remove_nin_inv in H1.
          intuition.
        - Case "NNRSimpIf"%string.
          rewrite nnrs_imp_expr_unflatten_read_nfree_id by tauto.
          rewrite IHs1, IHs2; tauto.
        - Case "NNRSimpEither"%string.
          rewrite nnrs_imp_expr_unflatten_read_nfree_id by tauto.
          simpl; intuition.
          apply remove_nin_inv in H1.
          apply remove_nin_inv in H2.
          destruct (equiv_dec v0 v); trivial
          ; destruct (equiv_dec v1 v); trivial.
          + rewrite IHs2; intuition.
          + rewrite IHs1; intuition congruence.
          + rewrite IHs1, IHs2; intuition congruence.
      Qed.

    End ident.
    Section eval.

      Definition flattens_to (d d':data)
        := match d, d' with
           | dcoll l, dcoll l' => oflatten l = Some l'
           | _, _ => False
           end.

      Definition flattens_to_op (d d':data)
        : flattens_to d d'
          <-> lift_oncoll (fun l => (lift dcoll (oflatten l))) d = Some d'.
      Proof.
        destruct d; simpl
        ; try (intuition congruence).
        destruct d'; simpl
        ; try solve [destruct (oflatten l); simpl; try intuition congruence].
      Qed.

      Lemma nnrs_imp_expr_unflatten_init_eval e e' h σc σ :
        nnrs_imp_expr_unflatten_init e = Some e' ->
        lift2P flattens_to
               (nnrs_imp_expr_eval h σc σ e)
               (nnrs_imp_expr_eval h σc σ e').
      Proof.
        revert e'.
        nnrs_imp_expr_cases (induction e) Case
        ; simpl ; intros e' eqq
        ; try discriminate.
        - Case "NNRSimpConst"%string.
          destruct d; simpl in *
          ; invcs eqq.
          destruct l; invcs H0; simpl.
          + reflexivity.
          + destruct d; invcs H1.
            destruct l; invcs H0.
            simpl.
            unfold oflatten; simpl.
            rewrite app_nil_r; trivial.
        - Case "NNRSimpBinop"%string.
          destruct b; try discriminate.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          specialize (IHe1 _ eqq1).
          specialize (IHe2 _ eqq2).
          unfold lift2P in *; simpl.
          repeat match_option_in IHe1
          ; simpl in *
          ; try contradiction.
          repeat match_option_in IHe2
          ; simpl in *
          ; try contradiction.

          destruct d; simpl in *; try contradiction
          ; destruct d0; simpl in *; try contradiction
          ; trivial
          ; destruct d1; simpl in *; try contradiction
          ; destruct d2; simpl in *; try contradiction
          ; trivial.
          unfold bunion.
          apply oflatten_app; trivial.
        - Case "NNRSimpUnop"%string.
          destruct u; simpl; try discriminate.
          destruct e; simpl; try discriminate.
          + destruct d; simpl; try discriminate.
            invcs eqq; simpl.
            unfold oflatten, lift_flat_map; simpl.
            rewrite app_nil_r; trivial.
          + destruct u; simpl; try discriminate.
            invcs eqq; simpl.
            destruct (nnrs_imp_expr_eval h σc σ e); simpl; trivial.
      Qed.

      Lemma nnrs_imp_expr_unflatten_read_eval e e' v h σc σ d d' :
        nnrs_imp_expr_unflatten_read e v = Some e' ->
        lookup equiv_dec σ v = Some d ->
        lift2P flattens_to d d' ->
        nnrs_imp_expr_eval h σc σ e =
        nnrs_imp_expr_eval h σc (update_first equiv_dec σ v d') e'.
      Proof.
        revert e' d d'.
        nnrs_imp_expr_cases (induction e) Case
        ; simpl ; intros e' dd dd' eqq inn ft
        ; try discriminate.
        - Case "NNRSimpGetConstant"%string.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpVar"%string.
          match_destr_in eqq.
          invcs eqq; simpl.
          rewrite lookup_update_neq; trivial.
          eauto.
        - Case "NNRSimpConst"%string.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpBinop"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          simpl.
          erewrite IHe1, IHe2; eauto.
        - Case "NNRSimpUnop"%string.
          destruct u
          ; try solve [apply some_lift in eqq
                       ; destruct eqq as [eqq1 eqq2]
                       ; subst; simpl
                       ; erewrite IHe; eauto].
          destruct e
          ; try solve [apply some_lift in eqq
                       ; destruct eqq as [eqq1 eqq2]
                       ; subst; simpl in *
                       ; invcs eqq2
                       ; simpl; trivial
                       ; erewrite IHe; eauto].
          match_destr_in eqq.
          + invcs eqq; simpl.
            rewrite e.
            rewrite lookup_update_eq_in.
            * unfold var in *. rewrite inn; simpl.
              unfold id.
              unfold lift2P in ft.
              repeat match_destr_in ft; simpl; try contradiction.
              apply flattens_to_op; trivial.
            * apply lookup_in_domain in inn; trivial.
          + invcs eqq; simpl.
            rewrite lookup_update_neq; eauto.
        - Case "NNRSimpGroupBy"%string.
          apply some_lift in eqq.
          destruct eqq as [??]; subst; simpl.
          erewrite IHe; eauto.
      Qed.              

    End eval.

    
    Section free_vars.
      
      Lemma nnrs_imp_expr_unflatten_init_free_vars e e' :
        nnrs_imp_expr_unflatten_init e = Some e' ->
        nnrs_imp_expr_free_vars e = nnrs_imp_expr_free_vars e'.
      Proof.
        revert e'.
        nnrs_imp_expr_cases (induction e) Case
        ; simpl ; intros e' eqq
        ; try discriminate.
        - Case "NNRSimpConst"%string.
          destruct d; simpl in *
          ; invcs eqq.
          destruct l; simpl in *.
          + invcs H0; simpl; trivial.
          + destruct d; simpl; try discriminate.
            destruct l; simpl; try discriminate.
            invcs H0.
            simpl; trivial.
        - Case "NNRSimpBinop"%string.
          destruct b; try discriminate.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          erewrite IHe1 by eauto.
          erewrite IHe2 by eauto.
          simpl; congruence.
        - Case "NNRSimpUnop"%string.
          destruct u; try discriminate.
          destruct e; try discriminate.
          + destruct d; try discriminate.
            invcs eqq; trivial.
          + destruct u; try discriminate.
            invcs eqq.
            simpl; trivial.
      Qed.
      
      Lemma nnrs_imp_expr_unflatten_read_free_vars e e' v :
        nnrs_imp_expr_unflatten_read e v = Some e' ->
        nnrs_imp_expr_free_vars e = nnrs_imp_expr_free_vars e'.
      Proof.
        revert e'
        ; nnrs_imp_expr_cases (induction e) Case
        ; simpl ; intros e' eqq
        ; try discriminate.
        - Case "NNRSimpGetConstant"%string.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpVar"%string.
          match_destr_in eqq.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpConst"%string.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpBinop"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          erewrite IHe1 by eauto.
          erewrite IHe2 by eauto.
          simpl; congruence.
        - Case "NNRSimpUnop"%string.
          destruct u
          ; try solve [apply some_lift in eqq
                       ; destruct eqq as [? eqq1 ?]; subst
                       ; erewrite IHe by eauto; simpl; trivial].
          destruct e
          ; try solve [apply some_lift in eqq
                       ; destruct eqq as [? eqq1 ?]; subst
                       ; erewrite IHe by eauto; simpl; trivial].
          match_destr_in eqq.
          + invcs eqq; trivial.
          + invcs eqq; trivial.
        - Case "NNRSimpGroupBy"%string.
          apply some_lift in eqq
          ; destruct eqq as [? eqq1 ?]; subst
          ; erewrite IHe by eauto; simpl; trivial.
      Qed.

      Lemma nnrs_imp_expr_unflatten_write_free_vars e e' v :
        nnrs_imp_expr_unflatten_write e v = Some e' ->
        nnrs_imp_expr_free_vars e = nnrs_imp_expr_free_vars e'.
      Proof.
        revert e'
        ; nnrs_imp_expr_cases (induction e) Case
        ; simpl ; intros e' eqq
        ; try discriminate.
        - Case "NNRSimpVar"%string.
          match_destr_in eqq.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpConst"%string.
          destruct d; simpl in *
          ; invcs eqq.
          destruct l; simpl in *.
          + invcs H0; simpl; trivial.
          + destruct d; simpl; try discriminate.
            destruct l; simpl; try discriminate.
            invcs H0.
            simpl; trivial.
        - Case "NNRSimpBinop"%string.
          destruct b; simpl; try discriminate.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          erewrite IHe1 by eauto.
          erewrite IHe2 by eauto.
          simpl; congruence.
        - Case "NNRSimpUnop"%string.
          destruct u; try discriminate.
          match_destr_in eqq.
          invcs eqq; trivial.
      Qed.

      Lemma nnrs_imp_stmt_unflatten_free_vars s s' v :
        nnrs_imp_stmt_unflatten s v = Some s' ->
        nnrs_imp_stmt_free_vars s = nnrs_imp_stmt_free_vars s'.
      Proof.
        revert s'
        ; nnrs_imp_stmt_cases (induction s) Case
        ; simpl ; intros s' eqq.
        - Case "NNRSimpSkip"%string.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpSeq"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          erewrite IHs1 by eauto.
          erewrite IHs2 by eauto.
          simpl; congruence.
        - Case "NNRSimpAssign"%string.
          apply some_lift in eqq.
          destruct eqq as [? eqq ?]; subst.
          match_destr_in eqq; simpl.
          + eapply nnrs_imp_expr_unflatten_write_free_vars in eqq; congruence.
          + eapply nnrs_imp_expr_unflatten_read_free_vars in eqq; congruence.
        - Case "NNRSimpLet"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          simpl.
          f_equal.
          + destruct o; simpl in *.
            * apply some_lift in eqq1.
              destruct eqq1 as [? eqq1 ?]; subst.
              eapply nnrs_imp_expr_unflatten_read_free_vars in eqq1; congruence.
            * invcs eqq1; trivial.
          + match_destr_in eqq2.
            * invcs eqq2; trivial.
            * eapply IHs in eqq2; congruence.
        - Case "NNRSimpFor"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          simpl.
          eapply nnrs_imp_expr_unflatten_read_free_vars in eqq1.
          f_equal; trivial.
          match_destr_in eqq2.
          + invcs eqq2; trivial.
          + eapply IHs in eqq2; congruence.
        - Case "NNRSimpIf"%string.
          unfold lift3 in eqq.
          repeat match_option_in eqq.
          invcs eqq.
          simpl.
          eapply nnrs_imp_expr_unflatten_read_free_vars in eqq0.
          rewrite eqq0.
          f_equal.
          f_equal; eauto.
        - Case "NNRSimpEither"%string.
          unfold lift3 in eqq.
          repeat match_option_in eqq.
          invcs eqq.
          simpl.
          eapply nnrs_imp_expr_unflatten_read_free_vars in eqq0.
          rewrite eqq0.
          f_equal.
          f_equal.
          + match_destr_in eqq1.
            * invcs eqq1; trivial.
            * eapply IHs1 in eqq1; congruence.
          + match_destr_in eqq2.
            * invcs eqq2; trivial.
            * eapply IHs2 in eqq2; congruence.
      Qed.

    End free_vars.

    Section usage.

      Lemma nnrs_imp_stmt_unflatten_var_usage {s s' v}:
        nnrs_imp_stmt_unflatten s v = Some s' ->
        forall v',
          nnrs_imp_stmt_var_usage s v' = nnrs_imp_stmt_var_usage s' v'.
      Proof.
        revert s'
        ; nnrs_imp_stmt_cases (induction s) Case
        ; simpl ; intros s' eqq v'.
        - Case "NNRSimpSkip"%string.
          invcs eqq; simpl; trivial.
        - Case "NNRSimpSeq"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          erewrite IHs1 by eauto.
          erewrite IHs2 by eauto.
          simpl; congruence.
        - Case "NNRSimpAssign"%string.
          apply some_lift in eqq.
          destruct eqq as [? eqq ?]; subst.
          match_destr_in eqq; simpl.
          + eapply nnrs_imp_expr_unflatten_write_free_vars in eqq.
            rewrite (nnrs_imp_expr_may_use_free_vars_eq eqq); trivial.
          + eapply nnrs_imp_expr_unflatten_read_free_vars in eqq.
            rewrite (nnrs_imp_expr_may_use_free_vars_eq eqq); trivial.
        - Case "NNRSimpLet"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          destruct o; simpl in *.
          + apply some_lift in eqq1.
            destruct eqq1 as [? eqq1 ?]; subst.
            eapply nnrs_imp_expr_unflatten_read_free_vars in eqq1.
            rewrite (nnrs_imp_expr_may_use_free_vars_eq eqq1); trivial.
            match_destr.
            unfold equiv_decb.
            match_destr_in eqq2.
            * invcs eqq2; trivial.
            * rewrite (IHs _ eqq2); trivial.
          + invcs eqq1.
            unfold equiv_decb.
            match_destr_in eqq2.
            * invcs eqq2; trivial.
            * rewrite (IHs _ eqq2); trivial.
        - Case "NNRSimpFor"%string.
          apply some_lift2 in eqq.
          destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
          simpl.
          eapply nnrs_imp_expr_unflatten_read_free_vars in eqq1.
          rewrite (nnrs_imp_expr_may_use_free_vars_eq eqq1); trivial.
          match_destr.
          unfold equiv_decb.
          match_destr_in eqq2.
          * invcs eqq2; trivial.
          * rewrite (IHs _ eqq2); trivial.
        - Case "NNRSimpIf"%string.
          unfold lift3 in eqq.
          repeat match_option_in eqq.
          invcs eqq; simpl.
          eapply nnrs_imp_expr_unflatten_read_free_vars in eqq0.
          rewrite (nnrs_imp_expr_may_use_free_vars_eq eqq0); trivial.
          match_destr.
          rewrite (IHs1 _ eqq1).
          rewrite (IHs2 _ eqq2).
          trivial.
        - Case "NNRSimpEither"%string.
          unfold lift3 in eqq.
          repeat match_option_in eqq.
          invcs eqq; simpl.
          eapply nnrs_imp_expr_unflatten_read_free_vars in eqq0.
          rewrite (nnrs_imp_expr_may_use_free_vars_eq eqq0); trivial.
          match_destr.
          match_destr_in eqq1.                         
          + invcs eqq1.
            match_destr_in eqq2.
            * invcs eqq2; trivial.
            * rewrite (IHs2 _ eqq2); trivial.
          + rewrite (IHs1 _ eqq1).
            match_destr_in eqq2.
            * invcs eqq2; trivial.
            * rewrite (IHs2 _ eqq2); trivial.
      Qed.

      Lemma nnrs_imp_stmt_unflatten_var_usage_sub {s x s'} :
        nnrs_imp_stmt_unflatten s x = Some s' ->
        stmt_var_usage_sub s s'.
      Proof.
        intros eqq1 v.
        eapply nnrs_imp_stmt_unflatten_var_usage in eqq1.
        rewrite eqq1.
        reflexivity.
      Qed.

    End usage.
    
  End unflatten.
  
End NNRSimpUnflatten.