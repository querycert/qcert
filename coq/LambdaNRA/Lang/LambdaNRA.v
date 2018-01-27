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
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonRuntime.

Section LambdaNRA.

  Context {fruntime:foreign_runtime}.

  Unset Elimination Schemes.

  (** Lambda NRA AST *)
  Inductive lambda_nra : Set :=
  | LNRAVar : string -> lambda_nra (* Variable access *)
  | LNRATable : string -> lambda_nra
  | LNRAConst : data -> lambda_nra
  | LNRABinop : binary_op -> lambda_nra -> lambda_nra -> lambda_nra
  | LNRAUnop : unary_op -> lambda_nra -> lambda_nra
  | LNRAMap : lnra_lambda -> lambda_nra -> lambda_nra (* 'dependent operators' use lambdas *)
  | LNRAMapProduct : lnra_lambda -> lambda_nra -> lambda_nra
  | LNRAProduct : lambda_nra -> lambda_nra -> lambda_nra
  | LNRAFilter : lnra_lambda -> lambda_nra -> lambda_nra
  with lnra_lambda : Set :=
  | LNRALambda : string -> lambda_nra -> lnra_lambda (* Lambda is (\var.alg) *)
  .

  Tactic Notation "lambda_nra_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LNRAVar"%string
  | Case_aux c "LNRATable"%string
  | Case_aux c "LNRAConst"%string
  | Case_aux c "LNRABinop"%string
  | Case_aux c "LNRAUnop"%string
  | Case_aux c "LNRAMap"%string
  | Case_aux c "LNRAMapProduct"%string
  | Case_aux c "LNRAProduct"%string
  | Case_aux c "LNRAFilter"%string
  ].
  
  Set Elimination Schemes.

  (* The language is defined via mutual recursion, but it is easier to 
     unfold it for reasoning. *)
  Definition  lambda_nra_rect
              (P : lambda_nra -> Type)
              (fvar : forall s : string, P (LNRAVar s))
              (ftable : forall t : string, P (LNRATable t))
              (fconst : forall d : data, P (LNRAConst d))
              (fbinop : forall (b : binary_op) (l0 l1: lambda_nra), P l0 -> P l1 -> P (LNRABinop b l0 l1))
              (funop : forall (u : unary_op) (l : lambda_nra), P l -> P (LNRAUnop u l))
              (fmap : forall (s:string) (l0 l1 : lambda_nra), P l0 -> P l1 -> P (LNRAMap (LNRALambda s l0) l1))
              (fmapconcat : forall (s:string) (l0 l1 : lambda_nra), P l0 -> P l1 -> P (LNRAMapProduct (LNRALambda s l0) l1))
              (fproduct : forall l : lambda_nra, P l -> forall l0 : lambda_nra, P l0 -> P (LNRAProduct l l0))
              (ffilter : forall (s:string) (l0 l1 : lambda_nra), P l0 -> P l1 -> P (LNRAFilter (LNRALambda s l0) l1)) :
    forall l, P l
    := 
      fix F (l : lambda_nra) : P l :=
        match l as l0 return (P l0) with
        | LNRAVar s => fvar s
        | LNRATable t => ftable t
        | LNRAConst d => fconst d
        | LNRABinop b l0 l1 => fbinop b l0 l1 (F l0) (F l1)
        | LNRAUnop u l0 => funop u l0 (F l0)
        | LNRAMap (LNRALambda s l0) l1 => fmap s l0 l1 (F l0) (F l1)
        | LNRAMapProduct (LNRALambda s l0) l1 => fmapconcat s l0 l1 (F l0) (F l1)
        | LNRAProduct l0 l1 => fproduct l0 (F l0) l1 (F l1)
        | LNRAFilter (LNRALambda s l0) l1 => ffilter s l0 l1 (F l0) (F l1)
        end.

  Definition lambda_nra_ind (P : lambda_nra -> Prop) := lambda_nra_rect P.
  Definition lambda_nra_rec (P:lambda_nra->Set) := lambda_nra_rect P.

  (** Semantics of Lambda NRA *)

  Context (h:brand_relation_t).
  Section Semantics.
    Context (global_env:list (string*data)).

    Fixpoint lambda_nra_eval (env: bindings) (op:lambda_nra) : option data :=
      match op with
      | LNRAVar x => edot env x
      | LNRATable t => edot global_env t
      | LNRAConst d => Some (normalize_data h d)
      | LNRABinop b op1 op2 =>
        olift2 (fun d1 d2 => binary_op_eval h b d1 d2) (lambda_nra_eval env op1) (lambda_nra_eval env op2)
      | LNRAUnop u op1 =>
        olift (fun d1 => unary_op_eval h u d1) (lambda_nra_eval env op1)
      | LNRAMap lop1 op2 =>
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (lift_map (lnra_lambda_eval env lop1) c1)) d
        in olift aux_map (lambda_nra_eval env op2)
      | LNRAMapProduct lop1 op2 =>
        let aux_mapconcat d :=
            lift_oncoll (fun c1 => lift dcoll (omap_product (lnra_lambda_eval env lop1) c1)) d
        in olift aux_mapconcat (lambda_nra_eval env op2)
      | LNRAProduct op1 op2 =>
        (* Note: it's even clearer from this formulation that both branches take the same environment *)
        let aux_product d :=
            lift_oncoll (fun c1 => lift dcoll (omap_product (fun _ => lambda_nra_eval env op2) c1)) d
        in olift aux_product (lambda_nra_eval env op1)
      | LNRAFilter lop1 op2 =>
        let pred x' :=
            match lnra_lambda_eval env lop1 x' with
            | Some (dbool b) => Some b
            | _ => None
            end
        in
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
        in
        olift aux_map (lambda_nra_eval env op2)
      end
    with lnra_lambda_eval (env:bindings)
                          (lop:lnra_lambda) (d:data)
         : option data :=
           match lop with
           | LNRALambda x op =>
             (lambda_nra_eval (rec_sort (env++((x,d)::nil))) op)
           end.

    Lemma lnra_lambda_eval_lambda_eq env x lop d:
      lnra_lambda_eval env (LNRALambda x lop) d =
      (lambda_nra_eval (rec_sort (env++((x,d)::nil))) lop).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_var_eq env s :
      lambda_nra_eval env (LNRAVar s) = 
      edot env s.
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_table_eq env s :
      lambda_nra_eval env (LNRATable s) = 
      edot global_env s.
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_const_eq env c :
      lambda_nra_eval env (LNRAConst c) = 
      Some (normalize_data h c).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_binary_op_eq env b op1 op2 :
      lambda_nra_eval env (LNRABinop b op1 op2) = 
      olift2 (fun d1 d2 => binary_op_eval h b d1 d2) (lambda_nra_eval env op1) (lambda_nra_eval env op2).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_unop_eq env u op1 :
      lambda_nra_eval env (LNRAUnop u op1) = 
      olift (fun d1 => unary_op_eval h u d1) (lambda_nra_eval env op1).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_map_eq env lop1 op2 :
      lambda_nra_eval env (LNRAMap lop1 op2) = 
      let aux_map d :=
          lift_oncoll (fun c1 => lift dcoll (lift_map (lnra_lambda_eval env lop1) c1)) d
      in olift aux_map (lambda_nra_eval env op2).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_map_concat_eq env lop1 op2 :
      lambda_nra_eval env (LNRAMapProduct lop1 op2) = 
      let aux_mapconcat d :=
          lift_oncoll (fun c1 => lift dcoll (omap_product (lnra_lambda_eval env lop1) c1)) d
      in olift aux_mapconcat (lambda_nra_eval env op2).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_product_eq env op1 op2 :
      lambda_nra_eval env (LNRAProduct op1 op2) = 
      let aux_product d :=
          lift_oncoll (fun c1 => lift dcoll (omap_product (fun _ => lambda_nra_eval env op2) c1)) d
      in olift aux_product (lambda_nra_eval env op1).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_filter_eq env lop1 op2 :
      lambda_nra_eval env (LNRAFilter lop1 op2) = 
      let pred x' :=
          match lnra_lambda_eval env lop1 x' with
          | Some (dbool b) => Some b
          | _ => None
          end
      in
      let aux_map d :=
          lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
      in
      olift aux_map (lambda_nra_eval env op2).
    Proof.
      reflexivity.
    Qed.

    Lemma lambda_nra_eval_normalized {op:lambda_nra} {env:bindings} {o} :
      lambda_nra_eval env op= Some o ->
      Forall (fun x => data_normalized h (snd x)) env ->
      Forall (fun x => data_normalized h (snd x)) global_env ->
      data_normalized h o.
    Proof.
      revert env o.
      lambda_nra_cases (induction op) Case
      ; intros; simpl in *.
      - Case "LNRAVar"%string.
        unfold edot in H.
        apply assoc_lookupr_in in H.
        rewrite Forall_forall in H0.
        specialize (H0 _ H).
        simpl in H0.
        trivial.
      - Case "LNRATable"%string.
        unfold edot in H.
        apply assoc_lookupr_in in H.
        rewrite Forall_forall in H1.
        specialize (H1 _ H).
        simpl in H1.
        trivial.
      - Case "LNRAConst"%string.
        invcs H.
        apply normalize_normalizes.
      - Case "LNRABinop"%string.
        unfold olift2 in H.
        match_case_in H; intros; rewrite H2 in H; try discriminate.
        match_case_in H; intros; rewrite H3 in H; try discriminate.
        eapply binary_op_eval_normalized; eauto.
      - Case "LNRAUnop"%string.
        unfold olift in H.
        match_case_in H; intros; rewrite H2 in H; try discriminate.
        eapply unary_op_eval_normalized; eauto.
      - Case "LNRAMap"%string.
        unfold olift in H.
        match_case_in H; intros; rewrite H2 in H; try discriminate.
        specialize (IHop2 _ _ H2 H0 H1).
        unfold lift_oncoll in H.
        match_destr_in H.
        apply some_lift in H.
        destruct H as [? ? ?]; subst.
        constructor.
        invcs IHop2.
        eapply (lift_map_Forall e).
        + apply H3.
        + intros. eapply IHop1; eauto.
          apply Forall_sorted.
          apply Forall_app; auto.
      - Case "LNRAMapProduct"%string.
        unfold olift in H.
        match_case_in H; intros; rewrite H2 in H; try discriminate.
        specialize (IHop2 _ _ H2 H0 H1).
        unfold lift_oncoll in H.
        match_destr_in H.
        apply some_lift in H.
        destruct H as [? ? ?]; subst.
        constructor.
        invcs IHop2.
        unfold omap_product in e.
        eapply (lift_flat_map_Forall e).
        + apply H3.
        + intros.
          unfold oncoll_map_concat in H.
          match_case_in H; intros; rewrite H5 in H; try discriminate.
          match_destr_in H.
          unfold omap_concat in H.
          specialize (IHop1 _ _ H5).
          cut_to IHop1.
          { invcs IHop1.
            eapply (lift_map_Forall H).
            - eapply H7.
            - intros.
              simpl in *.
              unfold orecconcat in H6.
              match_destr_in H6.
              match_destr_in H6.
              invcs H6.
              constructor.
              + apply Forall_sorted.
                apply Forall_app.
                * invcs H4; trivial.
                * invcs H8; trivial.
              + eauto.
          }
          apply Forall_sorted.
          apply Forall_app; trivial.
          constructor; trivial.
          trivial.
      - Case "LNRAProduct"%string.
        unfold olift in H.
        match_case_in H; intros; rewrite H2 in H; try discriminate.
        specialize (IHop1 _ _ H2 H0 H1).
        unfold lift_oncoll in H.
        match_destr_in H.
        apply some_lift in H.
        destruct H as [? ? ?]; subst.
        constructor.
        invcs IHop1.
        unfold omap_product in e.
        eapply (lift_flat_map_Forall e).
        + apply H3.
        + intros.
          unfold oncoll_map_concat in H.
          match_case_in H; intros; rewrite H5 in H; try discriminate.
          match_destr_in H.
          unfold omap_concat in H.
          specialize (IHop2 _ _ H5).
          cut_to IHop2.
          { invcs IHop2.
            eapply (lift_map_Forall H).
            - eapply H7.
            - intros.
              simpl in *.
              unfold orecconcat in H6.
              match_destr_in H6.
              match_destr_in H6.
              invcs H6.
              constructor.
              + apply Forall_sorted.
                apply Forall_app.
                * invcs H4; trivial.
                * invcs H8; trivial.
              + eauto.
          }
          trivial.
          trivial.
      - Case "LNRAFilter"%string.
        unfold olift in H.
        match_case_in H; intros; rewrite H2 in H; try discriminate.
        specialize (IHop2 _ _ H2 H0 H1).
        unfold lift_oncoll in H.
        match_destr_in H.
        apply some_lift in H.
        destruct H as [? ? ?]; subst.
        constructor.
        invcs IHop2.
        eapply (lift_filter_Forall e).
        trivial.
    Qed.
  End Semantics.

  Section LambdaNRAScope.

    Fixpoint lambda_nra_free_vars (e:lambda_nra) :=
      match e with
      | LNRAConst d => nil
      | LNRAVar v => v :: nil
      | LNRATable t => nil
      | LNRABinop bop e1 e2 => lambda_nra_free_vars e1 ++ lambda_nra_free_vars e2
      | LNRAUnop uop e1 => lambda_nra_free_vars e1
      | LNRAMap (LNRALambda x e1) e2 =>
        (remove string_eqdec x (lambda_nra_free_vars e1)) ++ (lambda_nra_free_vars e2)
      | LNRAMapProduct (LNRALambda x e1) e2 =>
        (remove string_eqdec x (lambda_nra_free_vars e1)) ++ (lambda_nra_free_vars e2)
      | LNRAProduct e1 e2 =>
        (lambda_nra_free_vars e1) ++ (lambda_nra_free_vars e2)
      | LNRAFilter (LNRALambda x e1) e2 =>
        (remove string_eqdec x (lambda_nra_free_vars e1)) ++ (lambda_nra_free_vars e2)
      end.

    (* capture avoiding substitution *)
    Fixpoint lambda_nra_subst (e:lambda_nra) (x:string) (e':lambda_nra) : lambda_nra :=
      match e with
      | LNRAConst d => LNRAConst d
      | LNRAVar y => if y == x then e' else LNRAVar y
      | LNRATable t => LNRATable t
      | LNRABinop bop e1 e2 => LNRABinop bop
                                   (lambda_nra_subst e1 x e') 
                                   (lambda_nra_subst e2 x e')
      | LNRAUnop uop e1 => LNRAUnop uop (lambda_nra_subst e1 x e')
      | LNRAMap (LNRALambda y e1) e2 =>
        if (y == x)
        then LNRAMap (LNRALambda y e1) (lambda_nra_subst e2 x e')
        else LNRAMap (LNRALambda y (lambda_nra_subst e1 x e')) (lambda_nra_subst e2 x e')
      | LNRAMapProduct (LNRALambda y e1) e2 =>
        if (y == x)
        then LNRAMapProduct (LNRALambda y e1) (lambda_nra_subst e2 x e')
        else LNRAMapProduct (LNRALambda y (lambda_nra_subst e1 x e')) (lambda_nra_subst e2 x e')
      | LNRAProduct e1 e2 =>
        LNRAProduct (lambda_nra_subst e1 x e') (lambda_nra_subst e2 x e')
      | LNRAFilter (LNRALambda y e1) e2 =>
        if (y == x)
        then LNRAFilter (LNRALambda y e1) (lambda_nra_subst e2 x e')
        else LNRAFilter (LNRALambda y (lambda_nra_subst e1 x e')) (lambda_nra_subst e2 x e')
      end.

  End LambdaNRAScope.

  Hint Rewrite @lnra_lambda_eval_lambda_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_var_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_table_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_const_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_binary_op_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_unop_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_map_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_map_concat_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_product_eq : lambda_nra.
  Hint Rewrite @lambda_nra_eval_filter_eq : lambda_nra.

  Global Instance lambda_nra_eval_lookup_equiv_prop :
    Proper (eq ==> assoc_lookupr_equiv ==> eq ==> eq) lambda_nra_eval.
  Proof.
    unfold Proper, respectful.
    intros ? cenv ? env1 env2 enveq ? e ?; subst.
    revert env1 env2 enveq.
    induction e; intros; subst
    ; autorewrite with lambda_nra
    ; try rewrite (IHe _ _ enveq)
    ; try rewrite (IHe1 _ _ enveq)
    ; try rewrite (IHe2 _ _ enveq)
    ; eauto.
    - apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply lift_map_ext; intros.
      simpl.
      apply IHe1.
      rewrite enveq; reflexivity.
    - apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply omap_product_ext; intros.
      simpl.
      apply IHe1.
      rewrite enveq; reflexivity.
    - apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply lift_filter_ext; intros.
      simpl.
      rewrite (IHe1 (rec_sort (env1 ++ (s, x) :: nil)) (rec_sort (env2 ++ (s, x) :: nil))); trivial.
      rewrite enveq; reflexivity.
  Qed.
    
  
  Section Top.
    (* For top-level: Parametric query *)
    Definition q_to_lambda (Q:lambda_nra -> lambda_nra) : lnra_lambda :=
      (LNRALambda "input" (Q (LNRAVar "input"))).

    Definition lnra_lambda_eval_top (Q:lambda_nra -> lambda_nra)
               (global_env:bindings) (input:data) : option data :=
      lnra_lambda_eval global_env nil (q_to_lambda Q) input.

    Definition lambda_nra_eval_top (q:lambda_nra) (env:bindings) : option data :=
      lambda_nra_eval (rec_sort env) nil q.
  End Top.

 
End LambdaNRA.

Hint Rewrite @lnra_lambda_eval_lambda_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_var_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_table_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_const_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_binary_op_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_unop_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_map_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_map_concat_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_product_eq : lambda_nra.
Hint Rewrite @lambda_nra_eval_filter_eq : lambda_nra.

Tactic Notation "lambda_nra_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LNRAVar"%string
  | Case_aux c "LNRATable"%string
  | Case_aux c "LNRAConst"%string
  | Case_aux c "LNRABinop"%string
  | Case_aux c "LNRAUnop"%string
  | Case_aux c "LNRAMap"%string
  | Case_aux c "LNRAMapProduct"%string
  | Case_aux c "LNRAProduct"%string
  | Case_aux c "LNRAFilter"%string
  ].

