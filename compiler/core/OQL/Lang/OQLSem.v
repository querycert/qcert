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
Require Import Arith.
Require Import EquivDec.
Require Import Permutation.
Require Import Utils.
Require Import DataRuntime.
Require Import OQL.

Section OQLSem.
  Context {fruntime:foreign_runtime}.

  Section Denotation.

    (** Semantics of OQL *)
    Context (h:brand_relation_t).
    Context (constant_env:list (string*data)).

    Inductive filter_cast_sem: brands -> list data -> list data -> Prop :=
    | filter_cast_sem_nil:
        forall b, filter_cast_sem b nil nil               (**r ⇒ [b ⊢〚[]〛ᶜ ⇓ []] *)
    | filter_cast_sem_cons_success:
        forall b1 b2 d1 dl1 dl2,
          filter_cast_sem b2 dl1 dl2 ->                   (**r   [b₂ ⊢〚↑dl₁〛ᶜ ⇓ ↑dl₂] *)
          sub_brands h b1 b2 ->                           (**r ∧ [b₁ <ᵇ b₂] *)
          filter_cast_sem b2                              (**r ⇒ [b₂ ⊢〚(brand b₁ d₁)::↑dl₁〛ᶜ ⇓ (brand b₁ d₁)::↑dl₂] *)
                          ((dbrand b1 d1)::dl1)
                          ((dbrand b1 d1)::dl2)
    | filter_cast_sem_cons_failure:
        forall b1 b2 d1 dl1 dl2,
          filter_cast_sem b2 dl1 dl2 ->                   (**r   [b₂ ⊢〚↑dl₁〛ᶜ ⇓ ↑dl₂] *)
          ~(sub_brands h b1 b2) ->                        (**r ∧ [¬ b₁ <ᵇ b₂] *)
          filter_cast_sem b2 ((dbrand b1 d1)::dl1) dl2    (**r ⇒ [b₂ ⊢〚(brand b₁ d₁)::↑dl₁〛ᶜ ⇓ ↑dl₂] *)
    .

    Lemma filter_cast_correct b l1 l2:
      filter_cast_sem b l1 l2 <->
      filter_cast h b l1 = Some l2.
    Proof.
      intros; split; intros.
      - revert l2 H; induction l1; intros.
        + inversion H; subst; intros.
          reflexivity.
        + inversion H; subst.
          unfold filter_cast; simpl.
          * unfold filter_cast in *; simpl.
            case_eq (sub_brands_dec h b1 b); intros; [|congruence]; simpl.
            rewrite (IHl1 dl2); [reflexivity|apply H3].
          * unfold filter_cast in *; simpl.
            case_eq (sub_brands_dec h b1 b); intros; [congruence| ]; simpl.
            rewrite lift_id; apply (IHl1 l2 H3).
      - revert l2 H; induction l1; intros.
        + inversion H.
          unfold filter_cast in *; simpl in *.
          inversion H; econstructor.
        + unfold filter_cast in *; simpl in *.
          destruct a; simpl in *; try congruence.
          case_eq (sub_brands_dec h b0 b); intros; subst;
            rewrite H0 in H.
          * unfold lift in H.
            case_eq
              (lift_flat_map
                 (fun x : data =>
                    match x with
                    | dbrand b' _ => if sub_brands_dec h b' b then Some (x :: nil) else Some nil
                    | _ => None
                    end) l1); intros;
              rewrite H1 in H; simpl in *; try congruence.
            inversion H; subst.
            econstructor.
            apply (IHl1 l H1).
            assumption.
          * unfold lift in H.
            case_eq
              (lift_flat_map
                 (fun x : data =>
                    match x with
                    | dbrand b' _ => if sub_brands_dec h b' b then Some (x :: nil) else Some nil
                    | _ => None
                    end) l1); intros;
              rewrite H1 in H; simpl in *; try congruence.
            inversion H; subst.
            econstructor.
            apply (IHl1 l2 H1).
            assumption.
    Qed.
    
    Inductive oql_expr_sem: oql_expr -> oql_env -> data -> Prop :=
    | sem_OConst : forall d d1 env,
        normalize_data h d = d1 ->                                            (**r   [normalize(d) = d₁] *)
        oql_expr_sem (OConst d) env d1                                        (**r ⇒ [Γc ; γ ⊢〚d〛⇓ d₁] *)
    | sem_OVar : forall v d env,
        edot env v = Some d ->                                                (**r   [γ(v) = d] *)
        oql_expr_sem (OVar v) env d                                           (**r ⇒ [Γc ; γ ⊢〚v〛⇓ d₁] *)
    | sem_OTable : forall t d env,
        edot constant_env t = Some d ->                                       (**r   [Γc(T) = d] *)
        oql_expr_sem (OTable t) env d                                         (**r ⇒ [Γc ; γ ⊢〚T〛⇓ d] *)
    | sem_OBinop : forall bop e1 e2 d1 d2 d3 env,
        oql_expr_sem e1 env d1 ->                                             (**r   [Γc ; γ ⊢〚e₁〛⇓ d₁] *)
        oql_expr_sem e2 env d2 ->                                             (**r   [Γc ; γ ⊢〚e₂〛⇓ d₂] *)
        binary_op_eval h bop d1 d2 = Some d3 ->                               (**r ∧ [d₁ ⊠ d₂ = d₃] *)
        oql_expr_sem (OBinop bop e1 e2) env d3                                (**r ⇒ [Γc ; γ ⊢〚e₁ ⊠ e₂〛⇓ d₃] *)
    | sem_OUnop : forall uop e d1 d2 env,
        oql_expr_sem e env d1 ->                                              (**r   [Γc ; γ ⊢〚e〛⇓ d₁] *)
        unary_op_eval h uop d1 = Some d2 ->                                   (**r ∧ [⊞ d₁ = d₂] *)
        oql_expr_sem (OUnop uop e) env d2                                     (**r ⇒ [Γc ; γ ⊢〚⊞ e〛⇓ d₂] *)
    | sem_OSFW_true_noorder select_e from_e : forall env tenv d,
        oql_from_sem from_e (env :: nil) tenv ->                              (**r   [Γc; [γ] ⊢〚↑eᶠ〛ᶠ ⇓ ↑γ₁] *)
        oql_select_sem select_e tenv d ->                                     (**r ∧ [Γc; ↑γ₁ ⊢〚eˢ〛ˢ ⇓ d] *)
        oql_expr_sem (OSFW select_e from_e OTrue ONoOrder) env d              (**r ⇒ [Γc; γ ⊢ SELECT eˢ FROM ↑eᶠ] *)
    | sem_OSFW_where_noorder select_e from_e where_e : forall env tenv tenv2 d,
        oql_from_sem from_e (env :: nil) tenv ->                              (**r   [Γc; [γ] ⊢〚↑eᶠ〛ᶠ ⇓ ↑γ₁] *)
        oql_where_sem where_e tenv tenv2 ->                                   (**r ∧ [Γc; ↑γ₁ ⊢〚eʷ〛ʷ ⇓ ↑γ₂] *)
        oql_select_sem select_e tenv2 d ->                                    (**r ∧ [Γc; ↑γ₂ ⊢〚eˢ〛ˢ ⇓ d] *)
        oql_expr_sem (OSFW select_e from_e (OWhere where_e) ONoOrder) env d   (**r ⇒ [Γc; γ ⊢ SELECT eˢ FROM ↑eᶠ WHERE eʷ] *)
    | sem_OSFW_true_order select_e from_e order_e sc : forall env tenv tenv1 d,
        oql_from_sem from_e (env :: nil) tenv ->                              (**r   [Γc; [γ] ⊢〚↑eᶠ〛ᶠ ⇓ ↑γ₁] *)
        oql_order_sem order_e sc tenv tenv1 ->                                (**r ∧ [Γc; ↑γ₁ ⊢〚eᵒ〛ᵒ ⇓ ↑γ₂] *)
        oql_select_sem select_e tenv1 d ->                                    (**r ∧ [Γc; ↑γ₂ ⊢〚eˢ〛ˢ ⇓ d] *)
        oql_expr_sem (OSFW select_e from_e OTrue (OOrderBy order_e sc)) env d (**r ⇒ [Γc; γ ⊢ SELECT eˢ FROM ↑eᶠ ORDER BY e] *)
    | sem_OSFW_where_order select_e from_e where_e order_e sc : forall env tenv tenv1 tenv2 d,
        oql_from_sem from_e (env :: nil) tenv ->                              (**r   [Γc; [γ] ⊢〚↑eᶠ〛ᶠ ⇓ ↑γ₁] *)
        oql_where_sem where_e tenv tenv1 ->                                   (**r ∧ [Γc; ↑γ₁ ⊢〚eʷ〛ʷ ⇓ ↑γ₂] *)
        oql_order_sem order_e sc tenv1 tenv2 ->                               (**r ∧ [Γc; ↑γ₂ ⊢〚eᵒ〛ᵒ ⇓ ↑γ₃] *)
        oql_select_sem select_e tenv2 d ->                                    (**r ∧ [Γc; ↑γ₃ ⊢〚eˢ〛ˢ ⇓ d] *)
        oql_expr_sem (OSFW select_e from_e (OWhere where_e)                   (**r ⇒ [Γc; γ ⊢ SELECT eˢ FROM ↑eᶠ WHERE eʷ ORDER BY eᵒ] *)
                           (OOrderBy order_e sc)) env d
    with oql_from_sem: list oql_in_expr -> list oql_env -> list oql_env -> Prop :=
    | sem_OFrom_Nil : forall tenv,
        oql_from_sem nil tenv tenv                                            (**r   [Γc; [γ] ⊢〚[]〛ᶠ ⇓ []] *)
    | sem_OFrom_In in_v e from_e : forall tenv1 tenv2 tenv3,
        oql_from_in_sem in_v e tenv1 tenv2 ->                                 (**r   [Γc; ↑γ₁; v ⊢〚e₀〛ⁱ ⇓ ↑γ₂] *)
        oql_from_sem from_e tenv2 tenv3 ->                                    (**r ∧ [Γc; ↑γ₂ ⊢〚↑eᶠ〛ᶠ ⇓ ↑γ₃] *)
        oql_from_sem ((OIn in_v e)::from_e) tenv1 tenv3                       (**r ⇒ [Γc; ↑γ₁ ⊢〚(v IN e₀)::↑eᶠ〛ᶠ ⇓ ↑γ₃] *)
    | sem_OFrom_InCast in_v brands e from_e : forall tenv1 tenv2 tenv3,
        oql_from_in_cast_sem in_v brands e tenv1 tenv2 ->                 (**r   [Γc; ↑γ₁; v; b ⊢〚e₀〛ᶜ ⇓ ↑γ₂] *)
        oql_from_sem from_e tenv2 tenv3 ->                                    (**r ∧ [Γc; ↑γ₂ ⊢〚↑eᶠ〛ᶠ ⇓ ↑γ₃] *)
        oql_from_sem ((OInCast in_v brands e)::from_e) tenv1 tenv3        (**r ⇒ [Γc; ↑γ₁ ⊢〚(v IN e₀ AS b)::↑eᶠ〛ᶠ ⇓ ↑γ₃] *)
    with oql_from_in_sem : string -> oql_expr -> list oql_env -> list oql_env -> Prop :=
    | oql_from_in_sem_nil v e :
        oql_from_in_sem v e nil nil                                           (**r   [Γc; []; v ⊢〚e〛ⁱ ⇓ []] *)
    | oql_from_in_sem_cons v e env tenv1 tenv2 tenv3 dl :
        oql_from_in_sem v e tenv1 tenv2 ->                                    (**r   [Γc; ↑γ₁; v ⊢〚e〛ⁱ ⇓ ↑γ₂] *)
        oql_expr_sem e env (dcoll dl) ->                                      (**r ∧ [Γc; γ ⊢〚e〛⇓ ↑dl] *)
        env_map_concat_single env (map (fun x => ((v,x)::nil)) dl) = tenv3 -> (**r ∧ [↑γ₃ = mapc γ v ↑dl] *)
        oql_from_in_sem v e (env :: tenv1) (tenv3 ++ tenv2)                   (**r ⇒ [Γc; γ::↑γ₁; v ⊢〚e〛ⁱ ⇓ ↑γ₃⊕↑γ₂] *)
    with oql_from_in_cast_sem : string -> list string -> oql_expr -> list oql_env -> list oql_env -> Prop :=
    | oql_from_in_cast_sem_nil v brands e :
        oql_from_in_cast_sem v brands e nil nil                           (**r   [Γc; []; v; b ⊢〚e〛ᶜ ⇓ []] *)
    | oql_from_in_cast_sem_cons v brands e env tenv1 tenv2 tenv3 dl dl' :
        oql_from_in_cast_sem v brands e tenv1 tenv2 ->                    (**r   [Γc; ↑γ₁; v; b ⊢〚e〛ᶜ ⇓ ↑γ₂] *)
        oql_expr_sem e env (dcoll dl) ->                                      (**r ∧ [Γc; γ ⊢〚e〛⇓ ↑dl] *)
        filter_cast_sem brands dl dl' ->                           (**r ∧ [b₂ ⊢〚↑dl〛ᶜ ⇓ ↑dl'] *)
        env_map_concat_single env (map (fun x => ((v,x)::nil)) dl') = tenv3 ->(**r ∧ [↑γ₃ = mapc v ↑dl'] *)
        oql_from_in_cast_sem v brands e (env :: tenv1) (tenv3 ++ tenv2)   (**r ⇒ [Γc; γ::↑γ₁; v ⊢〚e〛ᶜ ⇓ ↑γ₃⊕↑γ₂] *)
    with oql_where_sem : oql_expr -> list oql_env -> list oql_env -> Prop :=
    | oql_where_sem_nil e :
        oql_where_sem e nil nil                                               (**r   [Γc; [] ⊢〚e〛ʷ ⇓ []] *)
    | oql_where_sem_true e env tenv1 tenv2 :
        oql_where_sem e tenv1 tenv2 ->                                        (**r   [Γc; ↑γ₁ ⊢〚e〛ʷ ⇓ ↑γ₂] *)
        oql_expr_sem e env (dbool true) ->                                    (**r ∧ [Γc; γ ⊢〚e〛⇓ true] *)
        oql_where_sem e (env :: tenv1) (env :: tenv2)                         (**r ⇒ [Γc; γ::↑γ₁ ⊢〚e〛ʷ ⇓ γ::↑γ₂] *)
    | oql_where_sem_false e env1 tenv1 tenv2 :
        oql_where_sem e tenv1 tenv2 ->                                        (**r   [Γc; ↑γ₁ ⊢〚e〛ʷ ⇓ ↑γ₂] *)
        oql_expr_sem e env1 (dbool false) ->                                  (**r ∧ [Γc; γ ⊢〚e〛⇓ false] *)
        oql_where_sem e (env1 :: tenv1) tenv2                                 (**r ⇒ [Γc; γ::↑γ₁ ⊢〚e〛ʷ ⇓ ↑γ₂] *)
    with oql_order_sem : oql_expr -> SortDesc -> list oql_env -> list oql_env -> Prop :=
    | oql_order_sem_sorting e sc tenv1 tenv2 :
        Permutation tenv1 tenv2 ->                                            (**r ⇒ [↑γ₂ permutation of ↑γ₁] *)
        oql_strongly_sorted e sc tenv2 ->                                     (**r ⇒ [Γc ⊢ ↑γ₂ strongly sorted wrt e+sc] *)
        oql_order_sem e sc tenv1 tenv2                                        (**r ⇒ [Γc; ↑γ₁ ⊢〚e〛ᵒ ⇓ ↑γ₂] *)
    with oql_select_sem: oql_select_expr -> list oql_env -> data -> Prop :=
    | sem_OSelect e : forall tenv dl,
        oql_select_map_sem e tenv dl ->                                       (**r   [Γc; ↑γ ⊢〚e〛ᵐ ⇓ ↑dl] *)
        oql_select_sem (OSelect e) tenv (dcoll dl)                            (**r ⇒ [Γc; ↑γ ⊢〚e〛ˢ ⇓ {↑dl}] *)
    | sem_OSelectDistinct e : forall tenv dl dl',
        oql_select_map_sem e tenv dl ->                                       (**r   [Γc; ↑γ ⊢〚e〛ᵐ ⇓ ↑dl] *)
        bdistinct dl = dl' ->                                                 (**r ∧ [↑dl' = distinct ↑dl] *)
        oql_select_sem (OSelectDistinct e) tenv (dcoll dl')                   (**r ⇒ [Γc; ↑γ ⊢〚e〛ˢ ⇓ {↑dl'}] *)
    with oql_select_map_sem : oql_expr -> list oql_env -> list data -> Prop :=
    | oql_select_map_sem_nil e :
        oql_select_map_sem e nil nil
    | oql_select_map_sem_cons e env tenv1 d dl1:
        oql_expr_sem e env d ->                                               (**r   [Γc; γ ⊢〚e〛⇓ d] *)
        oql_select_map_sem e tenv1 dl1 ->                                     (**r ∧ [Γc; ↑γ₁ ⊢〚e〛ᵐ ⇓ ↑dl] *)
        oql_select_map_sem e (env :: tenv1) (d :: dl1)                        (**r ⇒ [Γc; γ::↑γ₁ ⊢〚e〛ᵐ ⇓ d::↑dl] *)
    with oql_strongly_sorted : oql_expr -> SortDesc -> list oql_env -> Prop :=
    | oql_SSorted_nil e sc : oql_strongly_sorted e sc nil
    | oql_SSorted_cons e sc env1 tenv :
        oql_strongly_sorted e sc tenv ->
        Forall (fun env2 => oql_sort_criteria e env1 env2) tenv ->
        oql_strongly_sorted e sc (env1 :: tenv)
    with oql_sort_criteria : oql_expr -> oql_env -> oql_env -> Prop :=
    (* XXX This looks kind of too complicated ? This is right, though, at the moment. *)
    | oql_sort_criteria_sem e env1 env2 d1 d2 sd1 sd2 :
      oql_expr_sem e env1 d1 ->
      oql_expr_sem e env2 d2 ->
      sdata_of_data d1 = Some sd1 ->
      sdata_of_data d2 = Some sd2 ->
      dict_field_le (sd1::nil, d1) (sd2::nil, d2) ->
      oql_sort_criteria e env1 env2
    .

    (** Note: [oql_strongly_sorted] based on StronglySorted property *)
    
    Lemma oql_from_in_sem_correct in_v e tenv tenv2:
      (forall (tenv : oql_env) (d : data),
          oql_expr_interp h constant_env e tenv = Some d -> oql_expr_sem e tenv d) ->
      env_map_concat in_v (oql_expr_interp h constant_env e) tenv = Some tenv2 ->
      oql_from_in_sem in_v e tenv tenv2.
    Proof.
      intros He.
      intros.
      revert tenv2 H.
      induction tenv; simpl; intros.
      - inversion H; econstructor.
      - inversion H; subst; clear H; simpl.
        unfold env_map_concat in *;
          unfold oenv_map_concat_single in *; unfold lift_flat_map in *; simpl.
        case_eq (oql_expr_interp h constant_env e a); intros;
          rewrite H in H1; simpl; try congruence.
        destruct d; simpl in *; try congruence.
        case_eq ((fix lift_flat_map (A B : Type) (f : A -> option (list B)) (l : list A) {struct l} :
               option (list B) :=
             match l with
             | nil => Some nil
             | x :: t =>
                 match f x with
                 | Some x' => lift (fun t' : list B => x' ++ t') (lift_flat_map A B f t)
                 | None => None
                 end
             end) oql_env oql_env
            (fun a : oql_env =>
             match oql_expr_interp h constant_env e a with
             | Some (dcoll y) =>
                 Some (env_map_concat_single a (map (fun x : data => (in_v, x) :: nil) y))
             | _ => None
             end) tenv); intros;
          rewrite H0 in H1; simpl in *; try congruence.
        specialize (IHtenv l0 H0); clear H0.
        inversion H1; clear H1; intros.
        econstructor.
        assumption.
        apply (He a (dcoll l)) in H.
        apply H.
        reflexivity.
    Qed.

    Lemma oql_from_in_cast_sem_correct in_v brands e tenv tenv2:
      (forall (tenv : oql_env) (d : data),
          oql_expr_interp h constant_env e tenv = Some d -> oql_expr_sem e tenv d) ->
      env_map_concat_cast h in_v brands (oql_expr_interp h constant_env e) tenv = Some tenv2 ->
      oql_from_in_cast_sem in_v brands e tenv tenv2.
    Proof.
      intros He.
      intros.
      revert tenv2 H.
      induction tenv; simpl; intros.
      - inversion H; econstructor.
      - inversion H; subst; clear H; simpl.
        unfold env_map_concat_cast in *;
          unfold oenv_map_concat_single_with_cast in *; unfold lift_flat_map in *; simpl.
        case_eq (oql_expr_interp h constant_env e a); intros;
          rewrite H in H1; simpl; try congruence.
        destruct d; simpl in *; try congruence.
        case_eq (filter_cast h brands l); intros;
          rewrite H0 in H1; simpl in *; try congruence.
        unfold lift in *.
        case_eq ((fix lift_flat_map (A B : Type) (f : A -> option (list B)) (l : list A) {struct l} :
              option (list B) :=
            match l with
            | nil => Some nil
            | x :: t =>
                match f x with
                | Some x' =>
                    match lift_flat_map A B f t with
                    | Some a' => Some (x' ++ a')
                    | None => None
                    end
                | None => None
                end
            end) oql_env oql_env
           (fun a : oql_env =>
            match oql_expr_interp h constant_env e a with
            | Some (dcoll y) =>
                match filter_cast h brands y with
                | Some y0 =>
                    Some (env_map_concat_single a (map (fun x : data => (in_v, x) :: nil) y0))
                | None => None
                end
            | _ => None
            end) tenv); intros;
        rewrite H2 in H1; simpl in *; try congruence.
        inversion H1; clear H1; intros.
        rewrite <- filter_cast_correct in H0.
        econstructor.
        apply (IHtenv); try assumption.
        apply (He a (dcoll l)) in H.
        apply H.
        apply H0.
        reflexivity.
    Qed.
        
    Lemma fold_left_none el :
      fold_left
         (fun (envl : option (list oql_env)) (from_in_expr : oql_in_expr) =>
          match from_in_expr with
          | OIn in_v from_expr =>
              match envl with
              | Some envl' => env_map_concat in_v (oql_expr_interp h constant_env from_expr) envl'
              | None => None
              end
          | OInCast in_v brand_name from_expr =>
              match envl with
              | Some envl' =>
                  env_map_concat_cast h in_v brand_name (oql_expr_interp h constant_env from_expr)
                    envl'
              | None => None
              end
          end) el None = None.
    Proof.
      induction el; simpl in *; [reflexivity| ].
      destruct a; simpl in *;
      rewrite IHel; reflexivity.
    Qed.

    Lemma oql_from_sem_correct el tenv tenv0 :
      (Forall
         (fun ab : oql_in_expr =>
         forall tenv : oql_env,
         forall d : data,
         oql_expr_interp h constant_env (oin_expr ab) tenv = Some d ->
         oql_expr_sem (oin_expr ab) tenv d) el) ->
      fold_left
        (fun (envl : option (list oql_env)) (from_in_expr : oql_in_expr) =>
           match from_in_expr with
           | OIn in_v from_expr =>
             match envl with
             | Some envl' => env_map_concat in_v (oql_expr_interp h constant_env from_expr) envl'
             | None => None
             end
           | OInCast in_v brand_name from_expr =>
             match envl with
             | Some envl' =>
               env_map_concat_cast h in_v brand_name (oql_expr_interp h constant_env from_expr)
                                   envl'
             | None => None
             end
           end) el (Some tenv) = Some tenv0 ->
      oql_from_sem el tenv tenv0.
    Proof.
      intros.
      revert tenv H0.
      induction el; intros; simpl in *.
      - inversion H0; econstructor.
      - inversion H; subst; intros; clear H.
        specialize (IHel H4); clear H4.
        destruct a; simpl in *.
        + case_eq (env_map_concat s (oql_expr_interp h constant_env o) tenv); intros;
          rewrite H in H0; simpl in *.
          * econstructor.
            apply (oql_from_in_sem_correct).
            apply H3.
            apply H.
            apply (IHel l H0).
          * clear H3 H IHel.
            rewrite fold_left_none in H0. congruence.
        + case_eq (env_map_concat_cast h s l (oql_expr_interp h constant_env o) tenv); intros;
          rewrite H in H0; simpl in *.
          * econstructor.
            apply (oql_from_in_cast_sem_correct).
            apply H3.
            apply H.
            apply (IHel l0 H0).
          * clear H3 H IHel.
            rewrite fold_left_none in H0. congruence.
    Qed.

    Lemma oql_select_map_sem_correct o tenv0 dl :
      (forall (tenv: oql_env) (d: data), oql_expr_interp h constant_env o tenv = Some d -> oql_expr_sem o tenv d) ->
      lift_map (oql_expr_interp h constant_env o) tenv0 = Some dl ->
      oql_select_map_sem o tenv0 dl.
    Proof.
      intros.
      revert dl H0.
      induction tenv0; simpl; intros.
      - inversion H0; econstructor.
      - case_eq (oql_expr_interp h constant_env o a); intros; rewrite H1 in H0;
          simpl in *; try congruence.
        unfold lift in H0.
        case_eq (lift_map (oql_expr_interp h constant_env o) tenv0); intros;
          rewrite H2 in H0; try congruence.
        inversion H0. subst.
        econstructor.
        apply (H a d H1).
        apply (IHtenv0 l H2).
    Qed.

    Lemma oql_where_sem_correct e tenv0 tenv2 :
      (forall (tenv : oql_env) (d : data),
         oql_expr_interp h constant_env e tenv = Some d -> oql_expr_sem e tenv d) ->
      lift_filter
        (fun x' : oql_env =>
           match oql_expr_interp h constant_env e x' with
           | Some (dbool b) => Some b
           | _ => None
           end) tenv0 = Some tenv2 ->
      oql_where_sem e tenv0 tenv2.
    Proof.
      intros.
      revert tenv2 H0.
      induction tenv0; intros; simpl in *.
      - inversion H0; econstructor.
      - case_eq (oql_expr_interp h constant_env e a); intros;
          rewrite H1 in H0; try congruence.
        destruct d; simpl in *; try congruence.
        case_eq (lift_filter
           (fun x' : oql_env =>
            match oql_expr_interp h constant_env e x' with
            | Some (dbool b) => Some b
            | _ => None
            end) tenv0); intros;
          rewrite H2 in H0; try congruence.
        destruct b; simpl in *; inversion H0; subst; clear H0.
        + specialize (IHtenv0 l H2).
          econstructor.
          assumption.
          apply (H a (dbool true) H1).
        + specialize (IHtenv0 tenv2 H2).
          econstructor.
          assumption.
          apply (H a (dbool false) H1).
    Qed.

    Lemma exists_permutation_for_input e l l' l1:
      Permutation l l' ->
      fsortable_coll_of_coll
         ((fun env : oql_env =>
           match oql_expr_interp h constant_env e env with
           | Some x' => sdata_of_data x'
           | None => None
           end) :: nil) l1 = Some l ->
      exists l1',
        Permutation l1 l1' /\
        fsortable_coll_of_coll
         ((fun env : oql_env =>
           match oql_expr_interp h constant_env e env with
           | Some x' => sdata_of_data x'
           | None => None
           end) :: nil) l1' = Some l'.
    Proof.
      unfold fsortable_coll_of_coll.
      revert l' l1.
      induction l; intros; simpl in *.
      - destruct l1; simpl in *; try congruence;[|
        destruct (fsortable_data_of_data
                    o ((fun env : oql_env =>
                          match oql_expr_interp h constant_env e env with
                          | Some x' => sdata_of_data x'
                          | None => None
                          end) :: nil)); simpl in H0; try congruence;
          unfold lift in H0;
          destruct (lift_map
                      (fun d : oql_env =>
                         fsortable_data_of_data
                           d ((fun env : oql_env =>
                                 match oql_expr_interp h constant_env e env with
                                 | Some x' => sdata_of_data x'
                                 | None => None
                                 end) :: nil)) l1); try congruence].
        apply Permutation_nil in H; subst; simpl.
        exists nil; split; [constructor|reflexivity].
      - destruct l1; simpl in *; try congruence.
        case_eq (fsortable_data_of_data o
           ((fun env : oql_env =>
             match oql_expr_interp h constant_env e env with
             | Some x' => sdata_of_data x'
             | None => None
             end) :: nil)); intros; rewrite H1 in H0; simpl in *; try congruence.
        unfold lift in H0.
        case_eq (lift_map
           (fun d : oql_env =>
            fsortable_data_of_data d
              ((fun env : oql_env =>
                match oql_expr_interp h constant_env e env with
                | Some x' => sdata_of_data x'
                | None => None
                end) :: nil)) l1); intros; rewrite H2 in H0; simpl in *; try congruence.
        inversion H0; subst; clear H0; simpl in *.
        destruct l'; simpl in *; [
          assert (~Permutation nil (a :: l)) by apply Permutation_nil_cons;
          apply Permutation_sym in H; congruence | ].
        inversion H; intros; subst; rename H into Hperm.
        + elim (IHl l' l1 H3 H2); intros; clear IHl.
          elim H; intros; clear H.
          exists (o :: x).
          split; [constructor; assumption| ].
          simpl.
          rewrite H1; unfold lift; simpl.
          rewrite H4; reflexivity.
        + assert (Permutation (s :: l0) (s :: l0)) by (constructor; apply Permutation_refl).
          destruct l1; simpl in H2; try congruence.
          case_eq (fsortable_data_of_data o0
           ((fun env : oql_env =>
             match oql_expr_interp h constant_env e env with
             | Some x' => sdata_of_data x'
             | None => None
             end) :: nil)); intros; rewrite H0 in H2; try congruence; unfold lift in H2.
          case_eq (lift_map
           (fun d : oql_env =>
            fsortable_data_of_data d
              ((fun env : oql_env =>
                match oql_expr_interp h constant_env e env with
                | Some x' => sdata_of_data x'
                | None => None
                end) :: nil)) l1); intros; rewrite H3 in H2; try congruence.
          inversion H2; subst; clear H2.
          specialize (IHl (s :: l0) (o0 :: l1) H); simpl in IHl.
          rewrite H0 in IHl; simpl in IHl; unfold lift in IHl.
          rewrite H3 in IHl; simpl in IHl.
          elim (IHl eq_refl); intros; clear IHl.
          elim H2; intros; clear H2.
          exists (o0 :: o :: l1).
          split.
          * apply perm_swap.
          * simpl.
            rewrite H0; simpl.
            unfold lift.
            rewrite H1; simpl.
            rewrite H3.
            reflexivity.
        + admit.
    Admitted.

    Lemma exists_sort_for_input e l l1:
      fsortable_coll_of_coll
         ((fun env : oql_env =>
           match oql_expr_interp h constant_env e env with
           | Some x' => sdata_of_data x'
           | None => None
           end) :: nil) l1 = Some l ->
      exists l1',
        fsortable_coll_of_coll
         ((fun env : oql_env =>
           match oql_expr_interp h constant_env e env with
           | Some x' => sdata_of_data x'
           | None => None
           end) :: nil) l1' = Some (dict_sort l).
    Proof.
      intros.
      elim (exists_permutation_for_input e l (dict_sort l) l1); intros; try assumption.
      elim H0; intros.
      exists x; assumption.
      apply Permutation_sym.
      apply dict_sort_permutation.
    Qed.
    
    Lemma some_eval_is_sort_criteria s o0 e l x :
      (forall x : sortable_data, In x l -> dict_field_le (s :: nil, o0) x) ->
      lift_map
        (fun d : oql_env =>
           match
             match
               match oql_expr_interp h constant_env e d with
               | Some x' => sdata_of_data x'
               | None => None
               end
             with
             | Some x' => Some (x' :: nil)
             | None => None
             end
           with
           | Some a' => Some (a', d)
           | None => None
           end) x = Some l
      -> (forall d,
             In d l ->
              exists env sd,
                oql_expr_interp h constant_env e (snd d) = Some env /\ sdata_of_data env = Some sd /\ LexicographicDataOrder.le (s :: nil) (sd :: nil)).
    Proof.
      intro Hlt.
      revert x.
      induction l; intros; simpl in *.
      - contradiction.
      - destruct x; simpl in *; try congruence.
        case_eq (match
                    match
                      match oql_expr_interp h constant_env e o with
                      | Some x' => sdata_of_data x'
                      | None => None
                      end
                    with
                    | Some x' => Some (x' :: nil)
                    | None => None
                    end
                  with
                  | Some a' => Some (a', o)
                  | None => None
                  end); intros;
          rewrite H1 in H; simpl in *; try congruence.
        unfold lift in H.
        case_eq (lift_map
          (fun d : oql_env =>
           match
             match
               match oql_expr_interp h constant_env e d with
               | Some x' => sdata_of_data x'
               | None => None
               end
             with
             | Some x' => Some (x' :: nil)
             | None => None
             end
           with
           | Some a' => Some (a', d)
           | None => None
           end) x); intros; rewrite H2 in H; simpl in H; try congruence.
        inversion H; clear H; subst.
        assert (forall x : sortable_data, In x l -> dict_field_le (s :: nil, o0) x).
        intros.
        assert (a = x0 \/ In x0 l) by (right; assumption).
        specialize (Hlt x0 H3); assumption.
        specialize (IHl H x H2).
        elim H0; intros.
        + subst.
          case_eq (oql_expr_interp h constant_env e o); intros; rewrite H3 in H1;
            try congruence.
          case_eq (sdata_of_data d0); intros; rewrite H4 in H1;
            try congruence.
          destruct d; simpl in *.
          inversion H1; subst; clear H1.
          assert ((s0 :: nil, o1) = (s0 :: nil, o1) \/ In (s0 :: nil, o1) l) by (left; reflexivity).
          specialize (Hlt (s0 :: nil, o1) H1).
          unfold dict_field_le in Hlt; simpl in Hlt.
          exists d0.
          exists s0.
          split; [assumption|split; assumption].
        + apply IHl; assumption.
    Qed.

    Lemma pick_d {A} (d:oql_env) (l: list (A * oql_env)) :
      In d (map snd l) -> exists s, In (s, d) l.
    Proof.
      intros.
      induction l; [contradiction| ].
      simpl in *.
      elim H; intros.
      - destruct a; simpl in *; subst.
        exists a; left; reflexivity.
      - elim (IHl H0); intros.
        exists x; right; assumption.
    Qed.
    
    Lemma lift_Forall_coll e (s:list sdata) o l :
      Forall (fun env2 => oql_sort_criteria e (snd (s :: nil, o)) (snd env2)) l ->
      Forall (fun env2 : oql_env => oql_sort_criteria e (snd (s :: nil, o)) env2)
             (coll_of_sortable_coll l).
    Proof.
      intros.
      rewrite Forall_forall in H.
      rewrite Forall_forall; intros.
      unfold coll_of_sortable_coll in H0.
      simpl in *.
      elim (pick_d x l H0); intros.
      apply (H (x0, x)); assumption.
    Qed.

    Lemma insert_sorted_is_sort_criteria e s o l x :
      (forall (tenv : oql_env) (d : data),
          oql_expr_interp h constant_env e tenv = Some d -> oql_expr_sem e tenv d) ->
      match oql_expr_interp h constant_env e o with
      | Some x' => sdata_of_data x'
      | None => None
      end = Some s ->
      lift_map
        (fun d : oql_env =>
           match
             match
               match oql_expr_interp h constant_env e d with
               | Some x' => sdata_of_data x'
               | None => None
               end
             with
             | Some x' => Some (x' :: nil)
             | None => None
             end
           with
           | Some a' => Some (a', d)
           | None => None
           end) x = Some l ->
      Forall (dict_field_le (s :: nil, o)) l ->
      Forall (fun env2 => (oql_sort_criteria e (snd (s :: nil, o)) (snd env2))) l.
    Proof.
      intro IHe.
      intros.
      unfold coll_of_sortable_coll in *.
      rewrite Forall_forall; intros; simpl.
      rewrite Forall_forall in H1.
      case_eq (oql_expr_interp h constant_env e o); intros; rewrite H3 in H; try congruence.
      generalize (some_eval_is_sort_criteria s o e l x H1 H0); intros; clear H0.
      elim (H4 x0 H2); intros; clear H4.
      elim H0; intros; clear H0.
      elim H4; intros; clear H4.
      elim H5; intros; clear H5.
      assert (oql_expr_sem e o d) by (apply IHe; assumption).
      assert (oql_expr_sem e (snd x0) x1) by (apply IHe; assumption).
      apply (oql_sort_criteria_sem e o (snd x0) d x1 s x2 H5 H7 H H4); intros.
      assumption.
    Qed.

    Lemma sort_sortable_coll_strongly_sorted e sc l l1 :
      (forall (tenv : oql_env) (d : data),
          oql_expr_interp h constant_env e tenv = Some d -> oql_expr_sem e tenv d) ->
      fsortable_coll_of_coll
         ((fun env : oql_env =>
           match oql_expr_interp h constant_env e env with
           | Some x' => sdata_of_data x'
           | None => None
           end) :: nil) l1 = Some l ->
      oql_strongly_sorted e sc (coll_of_sortable_coll (sort_sortable_coll l)).
    Proof.
      intros He.
      intros.
      elim (exists_sort_for_input e l l1 H); clear H l1; intros.
      revert H.
      unfold sort_sortable_coll.
      generalize (dict_sort_StronglySorted l).
      generalize (dict_sort l); clear l; intros.
      revert x H0.
      induction l; simpl in *; intros.
      - constructor.
      - inversion H; intros; subst; clear H.
        unfold fsortable_coll_of_coll in *;
          unfold fsortable_data_of_data in *;
          unfold fget_criterias in *; simpl in *.
        destruct x; simpl in *; try congruence.
        case_eq (match oql_expr_interp h constant_env e o with
             | Some x' => sdata_of_data x'
             | None => None
                 end); intros; rewrite H in *; simpl in H0; [|congruence].
        unfold lift in H0.
        case_eq (@lift_map (@oql_env fruntime) (@sortable_data (@oql_env fruntime))
             (fun d : @oql_env fruntime =>
              match
                match
                  match @oql_expr_interp fruntime h constant_env e d return (option sdata) with
                  | Some x' => @sdata_of_data (@foreign_runtime_data fruntime) x'
                  | None => @None sdata
                  end return (option (list sdata))
                with
                | Some x' => @Some (list sdata) (@cons sdata x' (@nil sdata))
                | None => @None (list sdata)
                end return (option (prod (list sdata) (@oql_env fruntime)))
              with
              | Some a' =>
                  @Some (prod (list sdata) (@oql_env fruntime))
                    (@pair (list sdata) (@oql_env fruntime) a' d)
              | None => @None (prod (list sdata) (@oql_env fruntime))
              end) x); intros; rewrite H1 in *; simpl in *; try congruence.
        inversion H0; intros; subst.
        specialize (IHl H3 x H1).
        constructor.
        apply IHl.
        apply (lift_Forall_coll e (s::nil)).
        apply (insert_sorted_is_sort_criteria e s o l x He); assumption.
    Qed.

    Lemma table_sort_correct e sc l1 l2:
      (forall (tenv : oql_env) (d : data),
          oql_expr_interp h constant_env e tenv = Some d -> oql_expr_sem e tenv d) ->
      table_sort
        ((fun env : oql_env =>
            match oql_expr_interp h constant_env e env with
            | Some x' => sdata_of_data x'
            | None => None
            end) :: nil) l1 = Some l2 ->
      oql_order_sem e sc l1 l2.
    Proof.
      intros He.
      intros.
      unfold table_sort in H.
      unfold lift in H.
      case_eq (fsortable_coll_of_coll
                 ((fun env : oql_env =>
                     match oql_expr_interp h constant_env e env with
                     | Some x' => sdata_of_data x'
                     | None => None
                     end) :: nil) l1); intros; rewrite H0 in H; simpl in H; try congruence.
      inversion H; clear H.
      constructor.
      - apply (sort_sortable_coll_permuation ((fun env : oql_env =>
         match oql_expr_interp h constant_env e env with
         | Some x' => sdata_of_data x'
         | None => None
         end) :: nil) l l1 H0).
      - apply sort_sortable_coll_strongly_sorted with (l1:= l1);
        assumption.
    Qed.
    
    Lemma oql_expr_interp_correct (e:oql_expr) :
      forall tenv d,
        oql_expr_interp h constant_env e tenv = Some d ->
        oql_expr_sem e tenv d.
    Proof.
      intros.
      revert tenv d H; induction e; simpl in *; intros.
      - constructor; inversion H; reflexivity.
      - constructor; assumption.
      - constructor; assumption.
      - unfold olift2 in H.
        case_eq (oql_expr_interp h constant_env e1 tenv); intros;
          rewrite H0 in H; try congruence.
        case_eq (oql_expr_interp h constant_env e2 tenv); intros;
          rewrite H1 in H; try congruence.
        econstructor; [apply (IHe1 tenv d0 H0)|apply (IHe2 tenv d1 H1)|assumption].
      - unfold olift in H.
        case_eq (oql_expr_interp h constant_env e tenv); intros;
          rewrite H0 in H; try congruence.
        econstructor; [apply (IHe tenv d0 H0)|assumption].
      - destruct e1; simpl in *; unfold olift in H0;
          case_eq
            (fold_left
               (fun (envl : option (list oql_env)) (from_in_expr : oql_in_expr) =>
                  match from_in_expr with
                  | OIn in_v from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat in_v (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  | OInCast in_v brand_name from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat_cast h in_v brand_name
                                          (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  end) el (Some (tenv :: nil))); intros;
            rewrite H1 in H0; simpl in *; try congruence.
        + econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| ]; clear H1.
          unfold lift in H0;
            case_eq (lift_map (oql_expr_interp h constant_env o) l); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0;
            econstructor; apply (oql_select_map_sem_correct o l l0 IHe H1).
        + econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| ]; clear H1.
          unfold lift in H0.
            case_eq (lift_map (oql_expr_interp h constant_env o) l); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0;
            econstructor; [apply (oql_select_map_sem_correct o l l0 IHe H1)|reflexivity].
      - destruct e1; simpl in *; unfold olift in H0;
          case_eq
            (fold_left
               (fun (envl : option (list oql_env)) (from_in_expr : oql_in_expr) =>
                  match from_in_expr with
                  | OIn in_v from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat in_v (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  | OInCast in_v brand_name from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat_cast h in_v brand_name
                                          (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  end) el (Some (tenv :: nil))); intros;
            rewrite H1 in H0; simpl in *; try congruence.
        + case_eq (lift_filter
           (fun x' : oql_env =>
            match oql_expr_interp h constant_env e x' with
            | Some (dbool b) => Some b
            | _ => None
            end) l); intros; rewrite H2 in H0; simpl in H0; try congruence.
          econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| | ]; clear H1.
          apply (oql_where_sem_correct e l l0 IHe0 H2).
          unfold lift in H0;
            case_eq (lift_map (oql_expr_interp h constant_env o) l0); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0.
            econstructor; apply (oql_select_map_sem_correct o l0 l1 IHe H1).
        + case_eq (lift_filter
           (fun x' : oql_env =>
            match oql_expr_interp h constant_env e x' with
            | Some (dbool b) => Some b
            | _ => None
            end) l); intros; rewrite H2 in H0; simpl in H0; try congruence.
          econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| | ]; clear H1.
          apply (oql_where_sem_correct e l l0 IHe0 H2).
          unfold lift in H0;
            case_eq (lift_map (oql_expr_interp h constant_env o) l0); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0.
            econstructor; [apply (oql_select_map_sem_correct o l0 l1 IHe H1)|reflexivity].
      - destruct e1; simpl in *; unfold olift in H0;
          case_eq
            (fold_left
               (fun (envl : option (list oql_env)) (from_in_expr : oql_in_expr) =>
                  match from_in_expr with
                  | OIn in_v from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat in_v (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  | OInCast in_v brand_name from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat_cast h in_v brand_name
                                          (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  end) el (Some (tenv :: nil))); intros;
            rewrite H1 in H0; simpl in *; try congruence.
        + case_eq (table_sort
           ((fun env : oql_env =>
             match oql_expr_interp h constant_env e env with
             | Some x' => sdata_of_data x'
             | None => None
             end) :: nil) l); intros; rewrite H2 in H0; simpl in H0; try congruence.
          econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| | ]; clear H1.
          apply (table_sort_correct e sc l l0 IHe0 H2); clear H2.
          unfold lift in H0;
            case_eq (lift_map (oql_expr_interp h constant_env o) l0); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0.
            econstructor; apply (oql_select_map_sem_correct o l0 l1 IHe H1).
        + case_eq (table_sort
           ((fun env : oql_env =>
             match oql_expr_interp h constant_env e env with
             | Some x' => sdata_of_data x'
             | None => None
             end) :: nil) l); intros; rewrite H2 in H0; simpl in H0; try congruence.
          econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| | ]; clear H1.
          apply (table_sort_correct e sc l l0 IHe0 H2); clear H2.
          unfold lift in H0;
            case_eq (lift_map (oql_expr_interp h constant_env o) l0); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0.
            econstructor; [apply (oql_select_map_sem_correct o l0 l1 IHe H1)|reflexivity].
      - destruct e1; simpl in *; unfold olift in H0;
          case_eq
            (fold_left
               (fun (envl : option (list oql_env)) (from_in_expr : oql_in_expr) =>
                  match from_in_expr with
                  | OIn in_v from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat in_v (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  | OInCast in_v brand_name from_expr =>
                    match envl with
                    | Some envl' =>
                      env_map_concat_cast h in_v brand_name
                                          (oql_expr_interp h constant_env from_expr) envl'
                    | None => None
                    end
                  end) el (Some (tenv :: nil))); intros;
            rewrite H1 in H0; simpl in *; try congruence.
        + case_eq (lift_filter
           (fun x' : oql_env =>
            match oql_expr_interp h constant_env e2 x' with
            | Some (dbool b) => Some b
            | _ => None
            end) l); intros; rewrite H2 in H0; simpl in H0; try congruence.
          case_eq (table_sort
           ((fun env : oql_env =>
             match oql_expr_interp h constant_env e3 env with
             | Some x' => sdata_of_data x'
             | None => None
             end) :: nil) l0); intros; rewrite H3 in H0; simpl in H0; try congruence.
          econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| | | ]; clear H1.
          apply (oql_where_sem_correct e2 l l0 IHe2 H2).
          apply (table_sort_correct e3 sc l0 l1 IHe3 H3); clear H3.
          unfold lift in H0;
            case_eq (lift_map (oql_expr_interp h constant_env o) l1); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0.
            econstructor; apply (oql_select_map_sem_correct o l1 l2 IHe1 H1).
        + case_eq (lift_filter
           (fun x' : oql_env =>
            match oql_expr_interp h constant_env e2 x' with
            | Some (dbool b) => Some b
            | _ => None
            end) l); intros; rewrite H2 in H0; simpl in H0; try congruence.
          case_eq (table_sort
           ((fun env : oql_env =>
             match oql_expr_interp h constant_env e3 env with
             | Some x' => sdata_of_data x'
             | None => None
             end) :: nil) l0); intros; rewrite H3 in H0; simpl in H0; try congruence.
          econstructor; [apply (oql_from_sem_correct el (tenv :: nil) l H H1)| | | ]; clear H1.
          apply (oql_where_sem_correct e2 l l0 IHe2 H2).
          apply (table_sort_correct e3 sc l0 l1 IHe3 H3); clear H3.
          unfold lift in H0;
            case_eq (lift_map (oql_expr_interp h constant_env o) l1); intros;
            rewrite H1 in H0; try congruence;
            inversion H0; subst; clear H0.
            econstructor; [apply (oql_select_map_sem_correct o l1 l2 IHe1 H1)|reflexivity].
    Qed.

    Lemma oql_from_in_sem_complete in_v e tenv tenv2:
      (forall (tenv : oql_env) (d : data),
          oql_expr_sem e tenv d -> oql_expr_interp h constant_env e tenv = Some d) ->
      oql_from_in_sem in_v e tenv tenv2 ->
      env_map_concat in_v (oql_expr_interp h constant_env e) tenv = Some tenv2.
    Proof.
      intros He.
      intros.
      revert tenv2 H.
      induction tenv; simpl; intros.
      - inversion H; subst; reflexivity.
      - inversion H; subst; clear H; simpl.
        unfold env_map_concat in *; unfold oenv_map_concat_single in *; simpl.
        assert (oql_expr_interp h constant_env e a = Some (dcoll dl))
          by apply (He a (dcoll dl) H5).
        rewrite H; simpl; clear H.
        specialize (IHtenv tenv0 H2).
        rewrite IHtenv; reflexivity.
    Qed.

    Lemma oql_from_in_cast_sem_complete in_v brand_name e tenv tenv2:
      (forall (tenv : oql_env) (d : data),
          oql_expr_sem e tenv d -> oql_expr_interp h constant_env e tenv = Some d) ->
      oql_from_in_cast_sem in_v brand_name e tenv tenv2 ->
      env_map_concat_cast h in_v brand_name (oql_expr_interp h constant_env e) tenv = Some tenv2.
    Proof.
      intros He.
      intros.
      revert tenv2 H.
      induction tenv; simpl; intros.
      - inversion H; subst; reflexivity.
      - inversion H; subst; clear H; simpl.
        unfold env_map_concat_cast in *; unfold oenv_map_concat_single_with_cast in *; simpl.
        assert (oql_expr_interp h constant_env e a = Some (dcoll dl))
          by apply (He a (dcoll dl) H3).
        rewrite H; simpl; clear H.
        specialize (IHtenv tenv0 H2).
        rewrite IHtenv; try reflexivity.
        rewrite filter_cast_correct in H7.
        rewrite H7; reflexivity.
    Qed.

    Lemma oql_from_sem_complete el tenv tenv0 :
      (Forall
        (fun ab : oql_in_expr =>
         forall (tenv : oql_env) (d : data),
         oql_expr_sem (oin_expr ab) tenv d ->
         oql_expr_interp h constant_env (oin_expr ab) tenv = Some d) el) ->
      oql_from_sem el tenv tenv0 ->
      fold_left
        (fun (envl : option (list oql_env)) (from_in_expr : oql_in_expr) =>
           match from_in_expr with
           | OIn in_v from_expr =>
             match envl with
             | Some envl' => env_map_concat in_v (oql_expr_interp h constant_env from_expr) envl'
             | None => None
             end
           | OInCast in_v brand_name from_expr =>
             match envl with
             | Some envl' =>
               env_map_concat_cast h in_v brand_name (oql_expr_interp h constant_env from_expr)
                                   envl'
             | None => None
             end
           end) el (Some tenv) = Some tenv0.
    Proof.
      intro Hforall.
      intros.
      revert tenv tenv0 H.
      induction el; simpl; intros.
      - inversion H; reflexivity.
      - inversion H; subst; simpl in *; clear H.
        + inversion Hforall; subst.
          specialize (IHel H3 tenv2 tenv0 H5).
          simpl in H1.
          rewrite (oql_from_in_sem_complete in_v e tenv tenv2 H1 H2).
          assumption.
        + inversion Hforall; subst.
          specialize (IHel H3 tenv2 tenv0 H5).
          simpl in H1.
          rewrite (oql_from_in_cast_sem_complete in_v brands e tenv tenv2 H1 H2).
          assumption.
    Qed.

    Lemma oql_select_map_sem_complete o tenv0 dl :
      (forall (tenv: oql_env) (d: data), oql_expr_sem o tenv d -> oql_expr_interp h constant_env o tenv = Some d) ->
      oql_select_map_sem o tenv0 dl ->
      lift_map (oql_expr_interp h constant_env o) tenv0 = Some dl.
    Proof.
      intros.
      revert dl H0.
      induction tenv0; simpl; intros.
      - inversion H0; reflexivity.
      - inversion H0; subst; clear H0.
        rewrite (H a d H4); simpl.
        unfold lift.
        rewrite (IHtenv0 dl1 H6).
        reflexivity.
    Qed.

    Lemma oql_where_sem_complete e tenv0 tenv2 :
      (forall (tenv : oql_env) (d : data),
         oql_expr_sem e tenv d -> oql_expr_interp h constant_env e tenv = Some d) ->
      oql_where_sem e tenv0 tenv2 ->
      lift_filter
        (fun x' : oql_env =>
           match oql_expr_interp h constant_env e x' with
           | Some (dbool b) => Some b
           | _ => None
           end) tenv0 = Some tenv2.
    Proof.
      intros.
      revert tenv2 H0.
      induction tenv0; intros; simpl.
      - inversion H0; reflexivity.
      - inversion H0; subst; simpl in *.
        + rewrite (H a (dbool true) H6).
          rewrite (IHtenv0 tenv3 H4).
          reflexivity.
        + rewrite (H a (dbool false) H6).
          rewrite (IHtenv0 tenv2 H4).
          reflexivity.
    Qed.

    (* XXX Is that even true?!?! *)
    Lemma table_sort_complete e sc l1 l2:
      oql_order_sem e sc l1 l2 ->
      table_sort
        ((fun env : oql_env =>
            match oql_expr_interp h constant_env e env with
            | Some x' => sdata_of_data x'
            | None => None
            end) :: nil) l1 = Some l2.
    Proof.
      admit.
    Admitted.
    
    Lemma oql_expr_interp_complete (e:oql_expr) :
      forall d tenv,
        oql_expr_sem e tenv d ->
        oql_expr_interp h constant_env e tenv = Some d.
    Proof.
      intros.
      revert tenv d H. induction e; simpl in *; intros.
      - inversion H; subst; reflexivity.
      - inversion H; subst; assumption.
      - inversion H; subst; assumption.
      - inversion H; subst.
        unfold olift2.
        rewrite (IHe1 tenv d1 H3); rewrite (IHe2 tenv d2 H6); assumption.
      - inversion H; subst.
        unfold olift.
        rewrite (IHe tenv d1 H2); assumption.
      - inversion H0; subst; clear H0.
        destruct e1; inversion H6; subst; clear H6; unfold olift; simpl in *.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H3); unfold lift.
          rewrite (oql_select_map_sem_complete o tenv0 dl IHe H1); reflexivity.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H3); unfold lift.
          rewrite (oql_select_map_sem_complete o tenv0 dl IHe H1); reflexivity.
      - inversion H0; subst; clear H0.
        destruct e1; inversion H8; subst; clear H8; unfold olift; simpl in *.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H4); unfold lift.
          rewrite (oql_where_sem_complete e tenv0 tenv2 IHe0 H7).
          rewrite (oql_select_map_sem_complete o tenv2 dl IHe H1).
          reflexivity.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H4); unfold lift.
          rewrite (oql_where_sem_complete e tenv0 tenv2 IHe0 H7).
          rewrite (oql_select_map_sem_complete o tenv2 dl IHe H1).
          reflexivity.
      - inversion H0; subst; clear H0.
        destruct e1; inversion H9; subst; clear H9; unfold olift; simpl in *.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H7); unfold lift.
          rewrite (table_sort_complete e sc tenv0 tenv1 H8).
          rewrite (oql_select_map_sem_complete o tenv1 dl IHe H1); reflexivity.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H7); unfold lift.
          rewrite (table_sort_complete e sc tenv0 tenv1 H8).
          rewrite (oql_select_map_sem_complete o tenv1 dl IHe H1); reflexivity.
      - inversion H0; subst; clear H0.
        destruct e1; inversion H11; subst; clear H11; unfold olift; simpl in *.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H8); unfold lift.
          rewrite (oql_where_sem_complete e2 tenv0 tenv1 IHe2 H9).
          rewrite (table_sort_complete e3 sc tenv1 tenv2 H10).
          rewrite (oql_select_map_sem_complete o tenv2 dl IHe1 H1); reflexivity.
        + rewrite (oql_from_sem_complete el (tenv::nil) tenv0 H H8); unfold lift.
          rewrite (oql_where_sem_complete e2 tenv0 tenv1 IHe2 H9).
          rewrite (table_sort_complete e3 sc tenv1 tenv2 H10).
          rewrite (oql_select_map_sem_complete o tenv2 dl IHe1 H1); reflexivity.
    Qed.
      
    Lemma oql_expr_interp_correct_and_complete (e:oql_expr) :
      forall tenv d,
        oql_expr_interp h constant_env e tenv = Some d <-> oql_expr_sem e tenv d.
    Proof.
      intros; split.
      - apply oql_expr_interp_correct.
      - apply oql_expr_interp_complete.
    Qed.
      
  End Denotation.

  Section ProgramDenotation.
    Context (h:brand_relation_t).
    Context (constant_env:list (string*data)).

    Inductive oql_query_program_sem : list (string*data) -> oql_query_program -> data -> Prop :=
    | sem_ODefineQuery defls s e rest d d':
        oql_expr_sem h (rec_concat_sort constant_env defls) e nil d ->
        oql_query_program_sem (rec_concat_sort defls ((s,d)::nil)) rest d' ->
        oql_query_program_sem defls (ODefineQuery s e rest) d'
    | sem_OUndefineQuery defls s rest d:
        oql_query_program_sem (rremove defls s) rest d ->
        oql_query_program_sem defls (OUndefineQuery s rest) d
    | sem_OQuery defls e d:
        oql_expr_sem h (rec_concat_sort constant_env defls) e nil d ->
        oql_query_program_sem defls (OQuery e) d.

    Lemma oql_query_program_interp_correct oq:
      forall defls d,
        oql_query_program_interp h constant_env defls oq = Some d ->
        oql_query_program_sem defls oq d.
    Proof.
      intros.
      revert defls d H.
      induction oq; simpl in *; intros.
      - unfold olift in H.
        case_eq (oql_expr_interp h (rec_concat_sort constant_env defls) o nil); intros;
          rewrite H0 in *; simpl in *; [|congruence].
        econstructor.
        rewrite <- oql_expr_interp_correct_and_complete.
        apply H0.
        apply IHoq; assumption.
      - econstructor.
        apply IHoq; assumption.
      - econstructor.
        rewrite <- oql_expr_interp_correct_and_complete; assumption.
    Qed.

    Lemma oql_query_program_interp_complete oq:
      forall defls d,
        oql_query_program_sem defls oq d ->
        oql_query_program_interp h constant_env defls oq = Some d.
    Proof.
      intros.
      revert defls d H.
      induction oq; simpl in *; intros.
      - inversion H; subst.
        unfold olift.
        rewrite <- oql_expr_interp_correct_and_complete in H5.
        rewrite H5; simpl.
        apply IHoq; assumption.
      - inversion H; subst.
        apply IHoq; assumption.
      - inversion H; subst.
        rewrite <- oql_expr_interp_correct_and_complete in H2; assumption.
    Qed.

    Lemma oql_query_program_interp_correct_and_complete oq:
      forall defls d,
        oql_query_program_interp h constant_env defls oq = Some d <->
        oql_query_program_sem defls oq d.
    Proof.
      intros; split.
      - apply oql_query_program_interp_correct.
      - apply oql_query_program_interp_complete.
    Qed.

    Definition oql_sem (oq:oql) (d:data) : Prop := oql_query_program_sem nil oq d.

    Lemma oql_interp_correct oq:
      forall d,
        oql_interp h constant_env oq = Some d ->
        oql_sem oq d.
    Proof.
      intros.
      apply oql_query_program_interp_correct.
      assumption.
    Qed.

    Lemma oql_interp_complete oq:
      forall d,
        oql_sem oq d ->
        oql_interp h constant_env oq = Some d.
    Proof.
      intros.
      apply oql_query_program_interp_complete.
      assumption.
    Qed.

    Lemma oql_interp_correct_and_complete oq:
      forall d,
        oql_interp h constant_env oq = Some d <->
        oql_sem oq d.
    Proof.
      intros; split.
      - apply oql_interp_correct.
      - apply oql_interp_complete.
    Qed.

  End ProgramDenotation.

End OQLSem.
