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

Require Import Utils BasicRuntime.
Section LambdaNRA.

  Context {fruntime:foreign_runtime}.

  Unset Elimination Schemes.

  (* Lambda NRA *)
  Inductive lalg : Set :=
  | LAVar : string -> lalg (* Variable access *)
  | LATable : string -> lalg
  | LAConst : data -> lalg
  | LABinop : binOp -> lalg -> lalg -> lalg
  | LAUnop : unaryOp -> lalg -> lalg
  | LAMap : lalg_lambda -> lalg -> lalg (* 'dependent operators' use lambdas *)
  | LAMapConcat : lalg_lambda -> lalg -> lalg
  | LAProduct : lalg -> lalg -> lalg
  | LASelect : lalg_lambda -> lalg -> lalg
  with lalg_lambda : Set :=
  | LALambda : string -> lalg -> lalg_lambda (* Lambda is (\var.alg) *)
  .

  Tactic Notation "lalg_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LAVar"%string
  | Case_aux c "LATable"%string
  | Case_aux c "LAConst"%string
  | Case_aux c "LABinop"%string
  | Case_aux c "LAUnop"%string
  | Case_aux c "LAMap"%string
  | Case_aux c "LAMapConcat"%string
  | Case_aux c "LAProduct"%string
  | Case_aux c "LASelect"%string
  ].
  
  Set Elimination Schemes.

  (* The language is defined via mutual recursion, but it is easier to 
     unfold it for reasoning. *)
  Definition  lalg_rect
              (P : lalg -> Type)
              (fvar : forall s : string, P (LAVar s))
              (ftable : forall t : string, P (LATable t))
              (fconst : forall d : data, P (LAConst d))
              (fbinop : forall (b : binOp) (l : lalg), P l -> forall l0 : lalg, P l0 -> P (LABinop b l l0))
              (funop : forall (u : unaryOp) (l : lalg), P l -> P (LAUnop u l))
              (fmap : forall (s:string) (l0 l1 : lalg), P l0 -> P l1 -> P (LAMap (LALambda s l0) l1))
              (fmapconcat : forall (s:string) (l0 l1 : lalg), P l0 -> P l1 -> P (LAMapConcat (LALambda s l0) l1))
              (fproduct : forall l : lalg, P l -> forall l0 : lalg, P l0 -> P (LAProduct l l0))
              (fselect : forall (s:string) (l0 l1 : lalg), P l0 -> P l1 -> P (LASelect (LALambda s l0) l1)) :
    forall l, P l
    := 
      fix F (l : lalg) : P l :=
        match l as l0 return (P l0) with
        | LAVar s => fvar s
        | LATable t => ftable t
        | LAConst d => fconst d
        | LABinop b l0 l1 => fbinop b l0 (F l0) l1 (F l1)
        | LAUnop u l0 => funop u l0 (F l0)
        | LAMap (LALambda s l0) l1 => fmap s l0 l1 (F l0) (F l1)
        | LAMapConcat (LALambda s l0) l1 => fmapconcat s l0 l1 (F l0) (F l1)
        | LAProduct l0 l1 => fproduct l0 (F l0) l1 (F l1)
        | LASelect (LALambda s l0) l1 => fselect s l0 l1 (F l0) (F l1)
        end.

  Definition lalg_ind (P : lalg -> Prop) := lalg_rect P.
  Definition lalg_rec (P:lalg->Set) := lalg_rect P.

  (** Semantics of Lambda NRA *)

  Context (h:brand_relation_t).
  Context (constant_env:list (string*data)).

  Fixpoint fun_of_lalg (env: bindings) (op:lalg) : option data :=
    match op with
    | LAVar x => edot env x
    | LATable t => edot constant_env t
    | LAConst d => Some (normalize_data h d)
    | LABinop b op1 op2 => olift2 (fun d1 d2 => fun_of_binop h b d1 d2) (fun_of_lalg env op1) (fun_of_lalg env op2)
    | LAUnop u op1 =>
      olift (fun d1 => fun_of_unaryop h u d1) (fun_of_lalg env op1)
    | LAMap lop1 op2 =>
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (fun_of_lalg_lambda env lop1) c1)) d
        in olift aux_map (fun_of_lalg env op2)
    | LAMapConcat lop1 op2 =>
      let aux_mapconcat d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun_of_lalg_lambda env lop1) c1)) d
      in olift aux_mapconcat (fun_of_lalg env op2)
    | LAProduct op1 op2 =>
      (* Note: it's even clearer from this formulation that both branches take the same environment *)
      let aux_product d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => fun_of_lalg env op2) c1)) d
      in olift aux_product (fun_of_lalg env op1)
    | LASelect lop1 op2 =>
      let pred x' :=
          match fun_of_lalg_lambda env lop1 x' with
          | Some (dbool b) => Some b
          | _ => None
          end
      in
      let aux_select d :=
          lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
      in
      olift aux_select (fun_of_lalg env op2)
    end
  with fun_of_lalg_lambda (env:bindings) (lop:lalg_lambda) (d:data) : option data :=
    match lop with
    | LALambda x op =>
      (fun_of_lalg (env++((x,d)::nil)) op)
    end.

  (* For top-level: Parametric query *)
  Definition q_to_lambda (Q:lalg -> lalg) :=
    (LALambda "input" (Q (LAVar "input"))).

  Definition eval_q (Q:lalg -> lalg) (input:data) : option data :=
    fun_of_lalg_lambda nil (q_to_lambda Q) input.


  Lemma fun_of_lalg_lambda_lambda_eq env x lop d:
    fun_of_lalg_lambda env (LALambda x lop) d =
    (fun_of_lalg (env++((x,d)::nil)) lop).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lalg_map_eq env lop1 op2 :
    fun_of_lalg env (LAMap lop1 op2) = 
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (fun_of_lalg_lambda env lop1) c1)) d
        in olift aux_map (fun_of_lalg env op2).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lalg_map_concat_eq env lop1 op2 :
    fun_of_lalg env (LAMapConcat lop1 op2) = 
      let aux_mapconcat d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun_of_lalg_lambda env lop1) c1)) d
      in olift aux_mapconcat (fun_of_lalg env op2).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lalg_product_eq env op1 op2 :
    fun_of_lalg env (LAProduct op1 op2) = 
        let aux_product d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => fun_of_lalg env op2) c1)) d
        in olift aux_product (fun_of_lalg env op1).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lalg_select_eq env lop1 op2 :
    fun_of_lalg env (LASelect lop1 op2) = 
      let pred x' :=
          match fun_of_lalg_lambda env lop1 x' with
          | Some (dbool b) => Some b
          | _ => None
          end
      in
      let aux_select d :=
          lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
      in
      olift aux_select (fun_of_lalg env op2).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lalg_normalized {op:lalg} {env:bindings} {o} :
    fun_of_lalg env op= Some o ->
    Forall (fun x => data_normalized h (snd x)) env ->
    Forall (fun x => data_normalized h (snd x)) constant_env ->
    data_normalized h o.
  Proof.
    revert env o.
    lalg_cases (induction op) Case
    ; intros; simpl in *.
    - Case "LAVar"%string.
      unfold edot in H.
      apply assoc_lookupr_in in H.
      rewrite Forall_forall in H0.
      specialize (H0 _ H).
      simpl in H0.
      trivial.
    - Case "LATable"%string.
      unfold edot in H.
      apply assoc_lookupr_in in H.
      rewrite Forall_forall in H1.
      specialize (H1 _ H).
      simpl in H1.
      trivial.
    - Case "LAConst"%string.
      invcs H.
      apply normalize_normalizes.
    - Case "LABinop"%string.
      unfold olift2 in H.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      match_case_in H; intros; rewrite H3 in H; try discriminate.
      eapply fun_of_binop_normalized; eauto.
    - Case "LAUnop"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      eapply fun_of_unaryop_normalized; eauto.
    - Case "LAMap"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      specialize (IHop2 _ _ H2 H0 H1).
      unfold lift_oncoll in H.
      match_destr_in H.
      apply some_lift in H.
      destruct H as [? ? ?]; subst.
      constructor.
      invcs IHop2.
      eapply (rmap_Forall e).
      + apply H3.
      + intros. eapply IHop1; eauto.
        apply Forall_app; auto.
    - Case "LAMapConcat"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      specialize (IHop2 _ _ H2 H0 H1).
      unfold lift_oncoll in H.
      match_destr_in H.
      apply some_lift in H.
      destruct H as [? ? ?]; subst.
      constructor.
      invcs IHop2.
      unfold rmap_concat in e.
      eapply (oflat_map_Forall e).
      + apply H3.
      + intros.
        unfold oomap_concat in H.
        match_case_in H; intros; rewrite H5 in H; try discriminate.
        match_destr_in H.
        unfold omap_concat in H.
        specialize (IHop1 _ _ H5).
        cut_to IHop1.
        { invcs IHop1.
          eapply (rmap_Forall H).
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
        apply Forall_app; trivial.
        constructor; trivial.
        trivial.
    - Case "LAProduct"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      specialize (IHop1 _ _ H2 H0 H1).
      unfold lift_oncoll in H.
      match_destr_in H.
      apply some_lift in H.
      destruct H as [? ? ?]; subst.
      constructor.
      invcs IHop1.
      unfold rmap_concat in e.
      eapply (oflat_map_Forall e).
      + apply H3.
      + intros.
        unfold oomap_concat in H.
        match_case_in H; intros; rewrite H5 in H; try discriminate.
        match_destr_in H.
        unfold omap_concat in H.
        specialize (IHop2 _ _ H5).
        cut_to IHop2.
        { invcs IHop2.
          eapply (rmap_Forall H).
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
    - Case "LASelect"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      specialize (IHop2 _ _ H2 H0 H1).
      unfold lift_oncoll in H.
      match_destr_in H.
      apply some_lift in H.
      destruct H as [? ? ?]; subst.
      constructor.
      invcs IHop2.
      unfold rmap_concat in e.
      eapply (lift_filter_Forall e).
      trivial.
  Qed.
  
  Section LambdaNRAScope.

    Fixpoint lalg_free_vars (e:lalg) :=
      match e with
      | LAConst d => nil
      | LAVar v => v :: nil
      | LATable t => nil
      | LABinop bop e1 e2 => lalg_free_vars e1 ++ lalg_free_vars e2
      | LAUnop uop e1 => lalg_free_vars e1
      | LAMap (LALambda x e1) e2 =>
        (remove string_eqdec x (lalg_free_vars e1)) ++ (lalg_free_vars e2)
      | LAMapConcat (LALambda x e1) e2 =>
        (remove string_eqdec x (lalg_free_vars e1)) ++ (lalg_free_vars e2)
      | LAProduct e1 e2 =>
        (lalg_free_vars e1) ++ (lalg_free_vars e2)
      | LASelect (LALambda x e1) e2 =>
        (remove string_eqdec x (lalg_free_vars e1)) ++ (lalg_free_vars e2)
      end.

  (* capture avoiding substitution *)
    Fixpoint lalg_subst (e:lalg) (x:string) (e':lalg) : lalg :=
      match e with
      | LAConst d => LAConst d
      | LAVar y => if y == x then e' else LAVar y
      | LATable t => LATable t
      | LABinop bop e1 e2 => LABinop bop
                                   (lalg_subst e1 x e') 
                                   (lalg_subst e2 x e')
      | LAUnop uop e1 => LAUnop uop (lalg_subst e1 x e')
      | LAMap (LALambda y e1) e2 =>
        if (y == x)
        then LAMap (LALambda y e1) (lalg_subst e2 x e')
        else LAMap (LALambda y (lalg_subst e1 x e')) (lalg_subst e2 x e')
      | LAMapConcat (LALambda y e1) e2 =>
        if (y == x)
        then LAMapConcat (LALambda y e1) (lalg_subst e2 x e')
        else LAMapConcat (LALambda y (lalg_subst e1 x e')) (lalg_subst e2 x e')
      | LAProduct e1 e2 =>
        LAProduct (lalg_subst e1 x e') (lalg_subst e2 x e')
      | LASelect (LALambda y e1) e2 =>
        if (y == x)
        then LASelect (LALambda y e1) (lalg_subst e2 x e')
        else LASelect (LALambda y (lalg_subst e1 x e')) (lalg_subst e2 x e')
      end.

  End LambdaNRAScope.
End LambdaNRA.

Hint Rewrite @fun_of_lalg_lambda_lambda_eq : lalg.
Hint Rewrite @fun_of_lalg_map_eq : lalg.
Hint Rewrite @fun_of_lalg_map_concat_eq : lalg.
Hint Rewrite @fun_of_lalg_product_eq : lalg.
Hint Rewrite @fun_of_lalg_select_eq : lalg.

Tactic Notation "lalg_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LAVar"%string
  | Case_aux c "LATable"%string
  | Case_aux c "LAConst"%string
  | Case_aux c "LABinop"%string
  | Case_aux c "LAUnop"%string
  | Case_aux c "LAMap"%string
  | Case_aux c "LAMapConcat"%string
  | Case_aux c "LAProduct"%string
  | Case_aux c "LASelect"%string
  ].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
