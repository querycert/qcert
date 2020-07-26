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
Require Import Permutation.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Arith.
Require Import Max.
Require Import Bool.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.

Require Import Utils.
Require Import DataRuntime.
Require Import Imp.

Section ImpVars.
  Import ListNotations.

  (* Context {fruntime:foreign_runtime}. *)
  (* Context (h:brand_relation_t). *)

  Context {Constant: Set}.
  Context {Op: Set}.
  Context {Runtime: Set}.


  Fixpoint imp_expr_free_vars (e:@imp_expr Constant Op Runtime) : list var
    := match e with
       | ImpExprError _ => nil
       | ImpExprVar v => v :: nil
       | ImpExprConst _ => nil
       | ImpExprOp _ l => List.fold_left (fun acc e => imp_expr_free_vars e ++ acc) l []
       | ImpExprRuntimeCall _ l => List.fold_left (fun acc e => imp_expr_free_vars e ++ acc) l []
       end.


  Fixpoint imp_stmt_free_vars (stmt:imp_stmt) : list var
    := match stmt with
       | ImpStmtBlock decls stmts =>
         List.fold_right
           (fun decl acc =>
              match decl with
              | (v, None) => remove string_eqdec v acc
              | (v, Some e) => imp_expr_free_vars e ++ (remove string_eqdec v acc)
              end)
           (List.fold_right (fun s acc => imp_stmt_free_vars s ++ acc) [] stmts)
           decls
       | ImpStmtAssign x e =>
         x :: imp_expr_free_vars e
       | ImpStmtFor v e s =>
         imp_expr_free_vars e ++ remove string_eqdec v (imp_stmt_free_vars s)
       | ImpStmtForRange v e1 e2 s =>
         imp_expr_free_vars e1 ++ imp_expr_free_vars e2 ++ remove string_eqdec v (imp_stmt_free_vars s)
       | ImpStmtIf e s1 s2 =>
         imp_expr_free_vars e ++ imp_stmt_free_vars s1 ++ imp_stmt_free_vars s2
       end.

  Fixpoint imp_stmt_bound_vars (stmt:@imp_stmt Constant Op Runtime) : list var
    := match stmt with
       | ImpStmtBlock decls stmts =>
         List.fold_left
           (fun acc decl =>
              match decl with
              | (v, None) => v :: acc
              | (v, Some e) => v :: acc
              end)
           decls
           (List.fold_left (fun acc s => imp_stmt_bound_vars s ++ acc) stmts [])
       | ImpStmtAssign x e => nil
       | ImpStmtFor v e s => v :: imp_stmt_bound_vars s
       | ImpStmtForRange v e1 e2 s => v :: imp_stmt_bound_vars s
       | ImpStmtIf e s1 s2 => imp_stmt_bound_vars s1 ++ imp_stmt_bound_vars s2
       end.

    Global Instance remove_perm_proper {A} dec v :
      Proper ((@Permutation A) ==> (@Permutation A)) (remove dec v).
    Proof.
      unfold Proper, respectful.
      apply Permutation_ind_bis; simpl; intros.
      - trivial.
      - match_destr.
        eauto.
      - repeat match_destr; eauto.
        rewrite H0.
        apply perm_swap.
      - etransitivity; eauto.
    Qed.


End ImpVars.
