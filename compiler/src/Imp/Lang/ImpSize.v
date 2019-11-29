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
Require Import Omega.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import Imp.

Section ImpSize.

  Context {Data: Type}.
  Context {Op: Type}.
  Context {Runtime: Type}.

  Definition imp_expr := @Imp.imp_expr Data Op Runtime.
  Definition imp_stmt := @Imp.imp_stmt Data Op Runtime.
  Definition imp_function := @Imp.imp_function Data Op Runtime.
  Definition imp := @Imp.imp Data Op Runtime.


  Fixpoint imp_expr_size (e:imp_expr) : nat
    := match e with
       | ImpExprError v => 1
       | ImpExprVar v => 1
       | ImpExprConst v => 1
       | ImpExprOp op l => S (List.fold_left (fun acc e => acc + imp_expr_size e ) l 0)
       | ImpExprRuntimeCall f args => S (List.fold_left (fun acc e => acc + imp_expr_size e) args 0)
       end.

    Fixpoint imp_stmt_size (stmt:imp_stmt) : nat
      := match stmt with
         | ImpStmtBlock decls stmts =>
           S (List.fold_left
                (fun acc (decl: var * option imp_expr) =>
                   let (x, eopt) := decl in
                   acc + match eopt with
                         | None => 1
                         | Some e => 1 + imp_expr_size e
                         end)
                decls
                (List.fold_left
                   (fun acc s => acc + imp_stmt_size s)
                   stmts 0))
         | ImpStmtAssign x e => 1 + imp_expr_size e
         | ImpStmtFor i e s => 1 + imp_expr_size e + imp_stmt_size s
         | ImpStmtForRange i e1 e2 s =>
           1 + imp_expr_size e1  + imp_expr_size e2  + imp_stmt_size s
         | ImpStmtIf e s1 s2 =>
           1 + imp_expr_size e + imp_stmt_size s1 + imp_stmt_size s2
         end.

    Definition imp_function_size (q:imp_function) : nat :=
      match q with
      | ImpFun args s ret => imp_stmt_size s
      end.

    Fixpoint imp_size (q: imp) : nat :=
      match q with
      | ImpLib l =>
        List.fold_left
          (fun acc (decl: string * imp_function) =>
             let (fname, fdef) := decl in acc + imp_function_size fdef)
          l 0
      end.

    Lemma imp_expr_size_nzero (e:imp_expr) : imp_expr_size e <> 0.
    Proof.
      induction e; simpl; try omega.
    Qed.

    Lemma imp_stmt_size_nzero (s:imp_stmt) : imp_stmt_size s <> 0.
    Proof.
      induction s; simpl; try destruct o; try omega.
    Qed.

    Corollary imp_function_size_nzero (q:imp_function) : imp_function_size q <> 0.
    Proof.
      destruct q.
      apply imp_stmt_size_nzero.
    Qed.

    (* Corollary imp_size_nzero (q:imp) : imp_size q <> 0. *)
    (* Proof. *)
    (*   induction q; simpl; try destruct o; try omega. *)
    (*   apply imp_stmt_size_nzero. *)
    (* Qed. *)

End ImpSize.
