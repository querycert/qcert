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

(** Imp is a simpl imperative intermediate language. *)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import Utils.
Require Import JsAst.JsNumber.
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpEJson.
Require Import ImpEJsonVars.
Require Import ImpEJsonEval.

Section ImpEJsonRewrite.
  Import ListNotations.

  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {fejruntime:foreign_ejson_runtime foreign_ejson_runtime_op}.

  Lemma imp_ejson_stmt_eval_env_simpl h stmt l1 x v l2:
    ~ In x (domain l2) ->
    imp_ejson_stmt_eval h stmt (l1 ++ (x, v) :: l2) = imp_ejson_stmt_eval h stmt (l1 ++ l2).
  Proof.
    admit.
  Admitted.

  Section ForRewrite.

    (* Rewriting functional for into imperative for loop is now isolated *)
    Definition imp_ejson_stmt_for_rewrite (stmt: @imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op): imp_ejson_stmt :=
      match stmt with
      | ImpStmtFor v e s =>
        (**
              for(v in e) do s done
              (i,src) fresh in v::s
              ============================
              { let src = e;
                for(i = 0 to length(e)-1) do
                  { let v = src[i];
                    s }
                done }
         *)
        let avoid := v :: imp_ejson_stmt_free_vars stmt in
        let i_id := fresh_var "i" avoid in
        let avoid := i_id :: avoid in
        let src_id := fresh_var "src" avoid in
        let src := ImpExprVar src_id in
        let i := ImpExprVar i_id in
        ImpStmtBlock
          [ (src_id, Some e) ]
          [ ImpStmtForRange
              i_id
              (ImpExprConst (cejbigint 0))
              (* XXX Use src.length - 1, consistent with semantic of 'for i1 to i2 do ... done' loop *)
              (ImpExprRuntimeCall EJsonRuntimeNatMinus
                                  [ ImpExprRuntimeCall EJsonRuntimeArrayLength [ src ] ; ImpExprConst (cejbigint 1) ])
              (ImpStmtBlock
                 [ (v, Some (ImpExprRuntimeCall EJsonRuntimeArrayAccess [ src; i ])) ]
                 [ s ]) ]
      | _ => stmt
      end.
  End ForRewrite.

  Section CorrectnessForRewrite.

    Lemma number_iterations A (l: list A):
      (ImpEval.nb_iter 0 (BinInt.Z.sub (BinInt.Z.of_nat (List.length l)) 1)) = length l.
    Proof.
      unfold ImpEval.nb_iter; simpl.
      induction (Datatypes.length l); [ simpl; reflexivity | ].
      rewrite BinInt.Z.sub_1_r.
      rewrite Znat.Nat2Z.inj_succ.
      rewrite <- BinInt.Zpred_succ.
      case n; [ simpl; reflexivity | ].
      intros.
      rewrite <- BinInt.Zminus_0_l_reverse.
      rewrite Znat.Nat2Z.id.
      simpl; reflexivity.
    Qed.

    Fixpoint list_n_nat {A} (n:nat) (l:list A) :=
      match n with
      | 0 => nil
      | S n' =>
        match l with
        | nil => nil
        | x :: l' => x :: (list_n_nat n' l')
        end
      end.

    Definition list_tail_n_nat {A} n (l: list A) :=
      List.rev (list_n_nat n (List.rev l)).

    (*
    Lemma for_corr_aux
      (l_init : list ejson)
      (j: nat)
      (v : var)
      (e : imp_expr)
      (stmt : imp_stmt)
      (h : BrandRelation.brand_relation_t)
      (l : list ejson)
      (σ : pd_jbindings) :
      let i := fresh_var "i"
                         (v :: imp_ejson_expr_free_vars e ++
                            remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
      in
      let src := fresh_var "src"
                           (i :: v :: imp_ejson_expr_free_vars e ++
                              remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
      in
      (lookup string_eqdec σ src = Some (Some (ejarray l_init))) ->
      (list_tail_n_nat (List.length l) l_init = l) ->
      (j + Datatypes.length l = List.length l_init) ->
      (fix for_fun (dl : list imp_ejson_model) (σ₁ : list (var * option imp_ejson_model)) {struct dl} :
         option (list (var * option imp_ejson_model)) :=
         match dl with
         | [] => Some σ₁
         | d :: dl' =>
           match imp_ejson_stmt_eval h stmt ((v, Some d) :: σ₁) with
           | Some (_ :: σ₂) => for_fun dl' σ₂
           | _ => None
           end
         end) l σ =
       match
         (fix for_range (n : nat) (n1 : BinNums.Z) (σ₁ : list (var * option imp_ejson_model)) {struct n} :
            option (list (var * option imp_ejson_model)) :=
            match n with
            | 0 => Some σ₁
            | S n' =>
                match
                  match
                    match
                      match
                        olift (imp_ejson_runtime_eval h EJsonRuntimeArrayAccess)
                          match
                            olift (fun x : option imp_ejson_model => x)
                              ((fix
                                lookup (l0 : list (string * option imp_ejson_model)) (a : string) {struct l0} :
                                  option (option imp_ejson_model) :=
                                  match l0 with
                                  | [] => None
                                  | (f', v') :: os => if EquivDec.equiv_dec a f' then Some v' else lookup os a
                                  end) σ₁
                                 src)
                          with
                          | Some x' => Some [x'; imp_ejson_Z_to_data n1]
                          | None => None
                          end
                      with
                      | Some d =>
                          Some
                            ((v, Some d)
                             :: (i, Some (imp_ejson_Z_to_data n1))
                             :: σ₁)
                      | None => None
                      end
                    with
                    | Some x' => imp_ejson_stmt_eval h stmt x'
                    | None => None
                    end
                  with
                  | Some (_ :: σ') => Some σ'
                  | _ => None
                  end
                with
                | Some (_ :: σ₂) => for_range n' (BinInt.Z.add n1 1) σ₂
                | _ => None
                end
            end) (j + Datatypes.length l) (BinInt.Z_of_nat j)
           ((src, Some (ejarray l)) :: σ)
       with
       | Some (_ :: σ') => Some σ'
       | _ => None
       end.
    Proof.
      admit.
    Admitted.
     *)

    (* Lemma for_range_ind h src i j n s σ : *)
    (*   let for_range_stmt := ImpStmtForRange i j n s in *)
    (*   j <= n -> *)
    (*   imp_ejson_expr_eval h (ImpExprVar src) σ = Some l_init -> *)
      


    Lemma for_corr v e stmt :
      forall h σ,
      let for_stmt := ImpStmtFor v e stmt in
      let for_range_stmt :=
        let avoid := v :: imp_ejson_stmt_free_vars (ImpStmtFor v e stmt) in
        let i_id := fresh_var "i" avoid in
        let avoid := i_id :: avoid in
        let src_id := fresh_var "src" avoid in
        let src := ImpExprVar src_id in
        let i := ImpExprVar i_id in
        ImpStmtBlock
          [ (src_id, Some e) ]
          [ ImpStmtForRange
              i_id
              (ImpExprConst (cejbigint 0))
              (* XXX Use src.length - 1, consistent with semantic of 'for i1 to i2 do ... done' loop *)
              (ImpExprRuntimeCall EJsonRuntimeNatMinus
                                  [ ImpExprRuntimeCall EJsonRuntimeArrayLength [ src ] ; ImpExprConst (cejbigint 1) ])
              (ImpStmtBlock
                 [ (v, Some (ImpExprRuntimeCall EJsonRuntimeArrayAccess [ src; i ])) ]
                 [ stmt ]) ]
      in
      imp_ejson_stmt_eval h for_stmt σ =
      imp_ejson_stmt_eval h for_range_stmt σ.
    Proof.
      simpl.
      intros.
      unfold ImpEval.imp_decls_eval.
      unfold olift.
      simpl.
      match_destr.
      unfold lookup.
      case (EquivDec.equiv_dec
              (fresh_var "src"
                 (fresh_var "i"
                    (v
                     :: ImpVars.imp_expr_free_vars e ++
                        remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                  :: v
                     :: ImpVars.imp_expr_free_vars e ++
                        remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
              (fresh_var "src"
                 (fresh_var "i"
                    (v
                     :: ImpVars.imp_expr_free_vars e ++
                        remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                  :: v
                     :: ImpVars.imp_expr_free_vars e ++
                        remove string_eqdec v (imp_ejson_stmt_free_vars stmt))));
        [ intro Eq; clear Eq | congruence ].
      case (EquivDec.equiv_dec
               (fresh_var "i"
                  (v
                   :: ImpVars.imp_expr_free_vars e ++
                      remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
               (fresh_var "i"
                  (v
                   :: ImpVars.imp_expr_free_vars e ++
                      remove string_eqdec v (imp_ejson_stmt_free_vars stmt))));
        try congruence; intro Eq; clear Eq.
      unfold imp_ejson_model_to_list.
      case i; simpl; try reflexivity.
      intros l.
      rewrite number_iterations.
      generalize σ; clear σ.


      induction l; [ simpl; reflexivity | ].
      intros.
      simpl.

        unfold olift.
        case (EquivDec.equiv_dec
                (fresh_var "src"
                   (fresh_var "i"
                      (v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                    :: v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
                (fresh_var "src"
                   (fresh_var "i"
                      (v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                    :: v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))));
          [ intro Eq; clear Eq | congruence].
        simpl.
        rewrite (imp_ejson_stmt_eval_env_simpl _ _
                   ((v, Some a)
                    :: (fresh_var "i"
                          (v
                           :: ImpVars.imp_expr_free_vars e ++ remove string_eqdec v (imp_ejson_stmt_free_vars stmt)),
                       Some (imp_ejson_Z_to_data 0)) :: [])
                   (fresh_var "src"
                     (fresh_var "i"
                        (v
                         :: ImpVars.imp_expr_free_vars e ++
                            remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                      :: v
                         :: ImpVars.imp_expr_free_vars e ++
                            remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
                   (Some (ejarray (a :: l)))
                   σ);
          [ | admit ].
        rewrite (imp_ejson_stmt_eval_env_simpl _ _
                   ((v, Some a) :: [])
                   (fresh_var "i"
                     (v :: ImpVars.imp_expr_free_vars e ++ remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
                   (Some (imp_ejson_Z_to_data 0))
                   σ);
          [ | admit ].
        simpl.
        unfold var.
        unfold imp_ejson_model.
        case (@imp_ejson_stmt_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime h stmt
            (@cons (prod string (option (@ejson foreign_ejson_model)))
               (@pair string (option (@ejson foreign_ejson_model)) v (@Some (@ejson foreign_ejson_model) a)) σ));
          [ | simpl; reflexivity].
        intros σ'.
        clear i a σ.
        match_destr.
        rewrite IHl; clear IHl.
        unfold olift.
        simpl.
        admit.
    Admitted.

    Lemma for_body h src i v n n' a stmt σ1:
      (* match *)
      (*   ImpEval.imp_decls_eval *)
      (*     ((fresh_var "i" *)
      (*         (fresh_var "src" *)
      (*            ((ImpVars.imp_expr_free_vars e ++ *)
      (*              remove string_eqdec v (imp_ejson_stmt_free_vars stmt)) ++ *)
      (*             v :: imp_ejson_stmt_bound_vars stmt) *)
      (*          :: (ImpVars.imp_expr_free_vars e ++ *)
      (*              remove string_eqdec v (imp_ejson_stmt_free_vars stmt)) ++ *)
      (*             v :: imp_ejson_stmt_bound_vars stmt), Some (imp_ejson_Z_to_data n1)) *)
      (*      :: σ₁) *)
      (*     [(v, *)
      (*      Some *)
      (*        (ImpExprOp EJsonRuntimeArrayAccess *)
      (*           [ImpExprVar *)
      (*              (fresh_var "src" *)
      (*                 ((ImpVars.imp_expr_free_vars e ++ *)
      (*                   remove string_eqdec v (imp_ejson_stmt_free_vars stmt)) ++ *)
      (*                  v :: imp_ejson_stmt_bound_vars stmt)); *)
      (*           ImpExprVar *)
      (*             (fresh_var "i" *)
      (*                (fresh_var "src" *)
      (*                   ((ImpVars.imp_expr_free_vars e ++ *)
      (*                     remove string_eqdec v (imp_ejson_stmt_free_vars stmt)) ++ *)
      (*                    v :: imp_ejson_stmt_bound_vars stmt) *)
      (*                 :: (ImpVars.imp_expr_free_vars e ++ *)
      (*                     remove string_eqdec v (imp_ejson_stmt_free_vars stmt)) ++ *)
      (*                    v :: imp_ejson_stmt_bound_vars stmt))]))] *)
      (* with *)
      (* | Some x'0 => imp_ejson_stmt_eval h (imp_ejson_stmt_for_rewrite stmt) x'0 *)
      (* | None => None *)
      (* end *)
      imp_ejson_decls_eval h
        ((i, Some (imp_ejson_Z_to_data n)) :: σ1)
        [(v, Some (ImpExprRuntimeCall EJsonRuntimeArrayAccess [ImpExprVar src; ImpExprVar i]))]
      =
      Some ((v, a) :: (i, n') :: σ1)
      ->
      match
        imp_ejson_decls_eval h
          ((i, Some (imp_ejson_Z_to_data n)) :: σ1)
          [(v, Some (ImpExprRuntimeCall EJsonRuntimeArrayAccess [ImpExprVar src; ImpExprVar i]))]
      with
      | Some σ2 => imp_ejson_stmt_eval h (imp_ejson_stmt_for_rewrite stmt) σ2
      | None => None
      end
      =
      imp_ejson_stmt_eval h stmt ((v, a) :: (i, n') :: σ1).
    Proof.
      admit.
    Admitted.

    Lemma imp_ejson_stmt_for_rewrite_correct h (σ : pd_jbindings) (stmt:imp_ejson_stmt) :
        imp_ejson_stmt_eval h stmt σ =
        imp_ejson_stmt_eval h (imp_ejson_stmt_for_rewrite stmt) σ.
    Proof.
      revert σ.
      imp_stmt_cases (induction stmt) Case; try reflexivity; intros.
      - Case "ImpStmtFor"%string.
        simpl in *.
        unfold ImpEval.imp_decls_eval.
        unfold olift.
        simpl.
        match_destr.
        unfold lookup.
        (* case (EquivDec.equiv_dec (fresh_var "src" (v :: avoid)) (fresh_var "src" (v :: avoid))); *)
        (*   try congruence; intro Eq; clear Eq. *)
Set Printing Depth 100.
        case (EquivDec.equiv_dec
                (fresh_var "src"
                   (fresh_var "i"
                      (v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                    :: v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
                (fresh_var "src"
                   (fresh_var "i"
                      (v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                    :: v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))));
          [ intro Eq; clear Eq | congruence ].
        case (EquivDec.equiv_dec
                 (fresh_var "i"
                    (v
                     :: ImpVars.imp_expr_free_vars e ++
                        remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
                 (fresh_var "i"
                    (v
                     :: ImpVars.imp_expr_free_vars e ++
                        remove string_eqdec v (imp_ejson_stmt_free_vars stmt))));
          try congruence; intro Eq; clear Eq.
        unfold imp_ejson_model_to_list.
        case i; simpl; try reflexivity.
        intros l.
        rewrite number_iterations.
        revert σ.
        induction l; [ simpl; reflexivity | ].
        intros.
        simpl.
        unfold olift.
        case (EquivDec.equiv_dec
                (fresh_var "src"
                   (fresh_var "i"
                      (v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                    :: v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt)))
                (fresh_var "src"
                   (fresh_var "i"
                      (v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))
                    :: v
                       :: ImpVars.imp_expr_free_vars e ++
                          remove string_eqdec v (imp_ejson_stmt_free_vars stmt))));
          [ intro Eq; clear Eq | congruence].
        simpl.
        admit.
    Admitted.

  End CorrectnessForRewrite.

End ImpEJsonRewrite.
