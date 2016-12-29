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
  Inductive lnra : Set :=
  | LNRAVar : string -> lnra (* Variable access *)
  | LNRATable : string -> lnra
  | LNRAConst : data -> lnra
  | LNRABinop : binOp -> lnra -> lnra -> lnra
  | LNRAUnop : unaryOp -> lnra -> lnra
  | LNRAMap : lnra_lambda -> lnra -> lnra (* 'dependent operators' use lambdas *)
  | LNRAMapConcat : lnra_lambda -> lnra -> lnra
  | LNRAProduct : lnra -> lnra -> lnra
  | LNRAFilter : lnra_lambda -> lnra -> lnra
  with lnra_lambda : Set :=
  | LNRALambda : string -> lnra -> lnra_lambda (* Lambda is (\var.alg) *)
  .

  Tactic Notation "lnra_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LNRAVar"%string
  | Case_aux c "LNRATable"%string
  | Case_aux c "LNRAConst"%string
  | Case_aux c "LNRABinop"%string
  | Case_aux c "LNRAUnop"%string
  | Case_aux c "LNRAMap"%string
  | Case_aux c "LNRAMapConcat"%string
  | Case_aux c "LNRAProduct"%string
  | Case_aux c "LNRAFilter"%string
  ].
  
  Set Elimination Schemes.

  (* The language is defined via mutual recursion, but it is easier to 
     unfold it for reasoning. *)
  Definition  lnra_rect
              (P : lnra -> Type)
              (fvar : forall s : string, P (LNRAVar s))
              (ftable : forall t : string, P (LNRATable t))
              (fconst : forall d : data, P (LNRAConst d))
              (fbinop : forall (b : binOp) (l : lnra), P l -> forall l0 : lnra, P l0 -> P (LNRABinop b l l0))
              (funop : forall (u : unaryOp) (l : lnra), P l -> P (LNRAUnop u l))
              (fmap : forall (s:string) (l0 l1 : lnra), P l0 -> P l1 -> P (LNRAMap (LNRALambda s l0) l1))
              (fmapconcat : forall (s:string) (l0 l1 : lnra), P l0 -> P l1 -> P (LNRAMapConcat (LNRALambda s l0) l1))
              (fproduct : forall l : lnra, P l -> forall l0 : lnra, P l0 -> P (LNRAProduct l l0))
              (ffilter : forall (s:string) (l0 l1 : lnra), P l0 -> P l1 -> P (LNRAFilter (LNRALambda s l0) l1)) :
    forall l, P l
    := 
      fix F (l : lnra) : P l :=
        match l as l0 return (P l0) with
        | LNRAVar s => fvar s
        | LNRATable t => ftable t
        | LNRAConst d => fconst d
        | LNRABinop b l0 l1 => fbinop b l0 (F l0) l1 (F l1)
        | LNRAUnop u l0 => funop u l0 (F l0)
        | LNRAMap (LNRALambda s l0) l1 => fmap s l0 l1 (F l0) (F l1)
        | LNRAMapConcat (LNRALambda s l0) l1 => fmapconcat s l0 l1 (F l0) (F l1)
        | LNRAProduct l0 l1 => fproduct l0 (F l0) l1 (F l1)
        | LNRAFilter (LNRALambda s l0) l1 => ffilter s l0 l1 (F l0) (F l1)
        end.

  Definition lnra_ind (P : lnra -> Prop) := lnra_rect P.
  Definition lnra_rec (P:lnra->Set) := lnra_rect P.

  (** Semantics of Lambda NRA *)

  Context (h:brand_relation_t).
  Context (constant_env:list (string*data)).

  Fixpoint fun_of_lnra (env: bindings) (op:lnra) : option data :=
    match op with
    | LNRAVar x => edot env x
    | LNRATable t => edot constant_env t
    | LNRAConst d => Some (normalize_data h d)
    | LNRABinop b op1 op2 => olift2 (fun d1 d2 => fun_of_binop h b d1 d2) (fun_of_lnra env op1) (fun_of_lnra env op2)
    | LNRAUnop u op1 =>
      olift (fun d1 => fun_of_unaryop h u d1) (fun_of_lnra env op1)
    | LNRAMap lop1 op2 =>
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (fun_of_lnra_lambda env lop1) c1)) d
        in olift aux_map (fun_of_lnra env op2)
    | LNRAMapConcat lop1 op2 =>
      let aux_mapconcat d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun_of_lnra_lambda env lop1) c1)) d
      in olift aux_mapconcat (fun_of_lnra env op2)
    | LNRAProduct op1 op2 =>
      (* Note: it's even clearer from this formulation that both branches take the same environment *)
      let aux_product d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => fun_of_lnra env op2) c1)) d
      in olift aux_product (fun_of_lnra env op1)
    | LNRAFilter lop1 op2 =>
      let pred x' :=
          match fun_of_lnra_lambda env lop1 x' with
          | Some (dbool b) => Some b
          | _ => None
          end
      in
      let aux_map d :=
          lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
      in
      olift aux_map (fun_of_lnra env op2)
    end
  with fun_of_lnra_lambda (env:bindings) (lop:lnra_lambda) (d:data) : option data :=
    match lop with
    | LNRALambda x op =>
      (fun_of_lnra (env++((x,d)::nil)) op)
    end.

  (* For top-level: Parametric query *)
  Definition q_to_lambda (Q:lnra -> lnra) :=
    (LNRALambda "input" (Q (LNRAVar "input"))).

  Definition eval_q (Q:lnra -> lnra) (input:data) : option data :=
    fun_of_lnra_lambda nil (q_to_lambda Q) input.


  Lemma fun_of_lnra_lambda_lambda_eq env x lop d:
    fun_of_lnra_lambda env (LNRALambda x lop) d =
    (fun_of_lnra (env++((x,d)::nil)) lop).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lnra_map_eq env lop1 op2 :
    fun_of_lnra env (LNRAMap lop1 op2) = 
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (fun_of_lnra_lambda env lop1) c1)) d
        in olift aux_map (fun_of_lnra env op2).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lnra_map_concat_eq env lop1 op2 :
    fun_of_lnra env (LNRAMapConcat lop1 op2) = 
      let aux_mapconcat d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun_of_lnra_lambda env lop1) c1)) d
      in olift aux_mapconcat (fun_of_lnra env op2).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lnra_product_eq env op1 op2 :
    fun_of_lnra env (LNRAProduct op1 op2) = 
        let aux_product d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => fun_of_lnra env op2) c1)) d
        in olift aux_product (fun_of_lnra env op1).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lnra_filter_eq env lop1 op2 :
    fun_of_lnra env (LNRAFilter lop1 op2) = 
      let pred x' :=
          match fun_of_lnra_lambda env lop1 x' with
          | Some (dbool b) => Some b
          | _ => None
          end
      in
      let aux_map d :=
          lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
      in
      olift aux_map (fun_of_lnra env op2).
  Proof.
    reflexivity.
  Qed.

  Lemma fun_of_lnra_normalized {op:lnra} {env:bindings} {o} :
    fun_of_lnra env op= Some o ->
    Forall (fun x => data_normalized h (snd x)) env ->
    Forall (fun x => data_normalized h (snd x)) constant_env ->
    data_normalized h o.
  Proof.
    revert env o.
    lnra_cases (induction op) Case
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
      eapply fun_of_binop_normalized; eauto.
    - Case "LNRAUnop"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      eapply fun_of_unaryop_normalized; eauto.
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
      eapply (rmap_Forall e).
      + apply H3.
      + intros. eapply IHop1; eauto.
        apply Forall_app; auto.
    - Case "LNRAMapConcat"%string.
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
      unfold rmap_concat in e.
      eapply (lift_filter_Forall e).
      trivial.
  Qed.
  
  Section LambdaNRAScope.

    Fixpoint lnra_free_vars (e:lnra) :=
      match e with
      | LNRAConst d => nil
      | LNRAVar v => v :: nil
      | LNRATable t => nil
      | LNRABinop bop e1 e2 => lnra_free_vars e1 ++ lnra_free_vars e2
      | LNRAUnop uop e1 => lnra_free_vars e1
      | LNRAMap (LNRALambda x e1) e2 =>
        (remove string_eqdec x (lnra_free_vars e1)) ++ (lnra_free_vars e2)
      | LNRAMapConcat (LNRALambda x e1) e2 =>
        (remove string_eqdec x (lnra_free_vars e1)) ++ (lnra_free_vars e2)
      | LNRAProduct e1 e2 =>
        (lnra_free_vars e1) ++ (lnra_free_vars e2)
      | LNRAFilter (LNRALambda x e1) e2 =>
        (remove string_eqdec x (lnra_free_vars e1)) ++ (lnra_free_vars e2)
      end.

  (* capture avoiding substitution *)
    Fixpoint lnra_subst (e:lnra) (x:string) (e':lnra) : lnra :=
      match e with
      | LNRAConst d => LNRAConst d
      | LNRAVar y => if y == x then e' else LNRAVar y
      | LNRATable t => LNRATable t
      | LNRABinop bop e1 e2 => LNRABinop bop
                                   (lnra_subst e1 x e') 
                                   (lnra_subst e2 x e')
      | LNRAUnop uop e1 => LNRAUnop uop (lnra_subst e1 x e')
      | LNRAMap (LNRALambda y e1) e2 =>
        if (y == x)
        then LNRAMap (LNRALambda y e1) (lnra_subst e2 x e')
        else LNRAMap (LNRALambda y (lnra_subst e1 x e')) (lnra_subst e2 x e')
      | LNRAMapConcat (LNRALambda y e1) e2 =>
        if (y == x)
        then LNRAMapConcat (LNRALambda y e1) (lnra_subst e2 x e')
        else LNRAMapConcat (LNRALambda y (lnra_subst e1 x e')) (lnra_subst e2 x e')
      | LNRAProduct e1 e2 =>
        LNRAProduct (lnra_subst e1 x e') (lnra_subst e2 x e')
      | LNRAFilter (LNRALambda y e1) e2 =>
        if (y == x)
        then LNRAFilter (LNRALambda y e1) (lnra_subst e2 x e')
        else LNRAFilter (LNRALambda y (lnra_subst e1 x e')) (lnra_subst e2 x e')
      end.

  End LambdaNRAScope.
End LambdaNRA.

Hint Rewrite @fun_of_lnra_lambda_lambda_eq : lnra.
Hint Rewrite @fun_of_lnra_map_eq : lnra.
Hint Rewrite @fun_of_lnra_map_concat_eq : lnra.
Hint Rewrite @fun_of_lnra_product_eq : lnra.
Hint Rewrite @fun_of_lnra_filter_eq : lnra.

Tactic Notation "lnra_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LNRAVar"%string
  | Case_aux c "LNRATable"%string
  | Case_aux c "LNRAConst"%string
  | Case_aux c "LNRABinop"%string
  | Case_aux c "LNRAUnop"%string
  | Case_aux c "LNRAMap"%string
  | Case_aux c "LNRAMapConcat"%string
  | Case_aux c "LNRAProduct"%string
  | Case_aux c "LNRAFilter"%string
  ].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
