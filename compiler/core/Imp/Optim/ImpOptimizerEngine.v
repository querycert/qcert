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

(* This is an optimizer for Imp{A} *)

Require Import String.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import DataSystem.
Require Import Imp.

Section ImpOptimizerEngine.
  Local Open Scope imp.
  Local Open Scope string.

  Context {Constant: Type}.
  Context {Op: Type}.
  Context {Runtime: Type}.

  Section map.
    Fixpoint imp_expr_map_deep
             (fe : imp_expr -> imp_expr)
             (e : imp_expr) : @imp_expr Constant Op Runtime
      := match e with
         | ImpExprError v =>
           fe (ImpExprError v)
         | ImpExprVar v =>
           fe (ImpExprVar v)
         | ImpExprConst d =>
           fe (ImpExprConst d)
         | ImpExprOp op el =>
           fe (ImpExprOp op
                         (map (imp_expr_map_deep fe) el))
         | ImpExprRuntimeCall op el =>
           fe (ImpExprRuntimeCall op
                                  (map (imp_expr_map_deep fe) el))
         end.

    Definition imp_var_decl_deep
               (fe : imp_expr -> imp_expr)
               (ve : var * option imp_expr) : var * option (@imp_expr Constant Op Runtime)
      := match ve with
         | (vname,None) => (vname,None)
         | (vname, Some e) => (vname, Some (imp_expr_map_deep fe e))
         end.

    Fixpoint imp_stmt_map_deep
             (fe : imp_expr -> imp_expr)
             (fs : imp_stmt -> imp_stmt)
             (s : imp_stmt) : imp_stmt
      := match s with
         | ImpStmtBlock vl sl =>
           fs (ImpStmtBlock
                 (map (imp_var_decl_deep fe) vl)
                 (map (imp_stmt_map_deep fe fs) sl))
         | ImpStmtAssign v e =>
           fs (ImpStmtAssign v
                             (imp_expr_map_deep fe e))
         | ImpStmtFor v e s₀ =>
           fs (ImpStmtFor v
                          (imp_expr_map_deep fe e)
                          (imp_stmt_map_deep fe fs s₀))
         | ImpStmtForRange v e₁ e₂ s₀ =>
           fs (ImpStmtForRange v
                          (imp_expr_map_deep fe e₁)
                          (imp_expr_map_deep fe e₂)
                          (imp_stmt_map_deep fe fs s₀))
         | ImpStmtIf e s₁ s₂ =>
           fs (ImpStmtIf 
                 (imp_expr_map_deep fe e)
                 (imp_stmt_map_deep fe fs s₁)
                 (imp_stmt_map_deep fe fs s₂))
         end.
    End map.

End ImpOptimizerEngine.
