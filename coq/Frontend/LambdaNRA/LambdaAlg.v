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

  Context (h:brand_relation_t).

  Fixpoint fun_of_lalg (env: bindings) (op:lalg) : option data :=
    match op with
    | LAVar x => edot env x
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
    - Case "LAConst"%string.
      invcs H.
      apply normalize_normalizes.
    - Case "LABinop"%string.
      unfold olift2 in H.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      match_case_in H; intros; rewrite H2 in H; try discriminate.
      eapply fun_of_binop_normalized; eauto.
    - Case "LAUnop"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      eapply fun_of_unaryop_normalized; eauto.
    - Case "LAMap"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      specialize (IHop2 _ _ H1 H0).
      unfold lift_oncoll in H.
      match_destr_in H.
      apply some_lift in H.
      destruct H as [? ? ?]; subst.
      constructor.
      invcs IHop2.
      eapply (rmap_Forall e).
      + apply H2.
      + intros. eapply IHop1; eauto.
        apply Forall_app; auto.
    - Case "LAMapConcat"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      specialize (IHop2 _ _ H1 H0).
      unfold lift_oncoll in H.
      match_destr_in H.
      apply some_lift in H.
      destruct H as [? ? ?]; subst.
      constructor.
      invcs IHop2.
      unfold rmap_concat in e.
      eapply (oflat_map_Forall e).
      + apply H2.
      + intros.
        unfold oomap_concat in H.
        match_case_in H; intros; rewrite H4 in H; try discriminate.
        match_destr_in H.
        unfold omap_concat in H.
        specialize (IHop1 _ _ H4).
        cut_to IHop1.
        { invcs IHop1.
          eapply (rmap_Forall H).
          - eapply H6.
          - intros.
            simpl in *.
            unfold orecconcat in H5.
            match_destr_in H5.
            match_destr_in H5.
            invcs H5.
            constructor.
            + apply Forall_sorted.
              apply Forall_app.
              * invcs H3; trivial.
              * invcs H7; trivial.
            + eauto.
        }
        apply Forall_app; trivial.
        constructor; trivial.
    - Case "LAProduct"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      specialize (IHop1 _ _ H1 H0).
      unfold lift_oncoll in H.
      match_destr_in H.
      apply some_lift in H.
      destruct H as [? ? ?]; subst.
      constructor.
      invcs IHop1.
      unfold rmap_concat in e.
      eapply (oflat_map_Forall e).
      + apply H2.
      + intros.
        unfold oomap_concat in H.
        match_case_in H; intros; rewrite H4 in H; try discriminate.
        match_destr_in H.
        unfold omap_concat in H.
        specialize (IHop2 _ _ H4).
        cut_to IHop2.
        { invcs IHop2.
          eapply (rmap_Forall H).
          - eapply H6.
          - intros.
            simpl in *.
            unfold orecconcat in H5.
            match_destr_in H5.
            match_destr_in H5.
            invcs H5.
            constructor.
            + apply Forall_sorted.
              apply Forall_app.
              * invcs H3; trivial.
              * invcs H7; trivial.
            + eauto.
        }
        trivial.
    - Case "LASelect"%string.
      unfold olift in H.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      specialize (IHop2 _ _ H1 H0).
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
  
End LambdaNRA.

Hint Rewrite @fun_of_lalg_lambda_lambda_eq : lalg.
Hint Rewrite @fun_of_lalg_map_eq : lalg.
Hint Rewrite @fun_of_lalg_map_concat_eq : lalg.
Hint Rewrite @fun_of_lalg_product_eq : lalg.
Hint Rewrite @fun_of_lalg_select_eq : lalg.

Tactic Notation "lalg_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LAVar"%string
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
