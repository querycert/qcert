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
Require Import Arith.
Require Import ZArith.
Require Import Max.
Require Import Bool.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import Imp.

Section ImpEval.
  Context {Data: Type}.
  Context {Op: Type}.
  Context {Runtime: Type}.

  Context {DataNormalize: Data -> Data}.
  Context {DataToBool: Data -> option bool}.
  Context {DataToZ: Data -> option Z}.
  Context {DataToList: Data -> option (list Data)}.

  Context {RuntimeEval: Runtime -> list Data -> option Data}.
  Context {OpEval: Op -> list Data -> option Data}.

  Definition imp_expr := @imp_expr Data Op Runtime.
  Definition imp_stmt := @imp_stmt Data Op Runtime.
  
  Definition rbindings := list (string * Data).
  Definition pd_rbindings := list (string * option Data).

  Section Util.
    Definition apply_unary (f: Data -> option Data) (dl: list Data) : option Data :=
      match dl with
      | d :: nil => f d
      | _ => None
      end.
    Definition apply_binary (f: Data -> Data -> option Data) (dl: list Data) : option Data :=
      match dl with
      | d1 :: d2 :: nil => f d1 d2
      | _ => None
      end.
  End Util.
  
  (** ** Evaluation Semantics *)
  Section Evaluation.
    Fixpoint imp_expr_eval
             (σ:pd_rbindings) (e:imp_expr) {struct e} : option Data
      :=
        match e with
        | ImpExprError msg =>
          None
        | ImpExprVar v =>
          olift (fun x => x) (lookup equiv_dec σ v)
        | ImpExprConst d =>
          Some (DataNormalize d)
        | ImpExprOp op el =>
          olift (OpEval op) (lift_map (fun x => x) (map (imp_expr_eval σ) el))
        | ImpExprRuntimeCall rt el =>
          olift (RuntimeEval rt) (lift_map (fun x => x) (map (imp_expr_eval σ) el))
        end.

    Fixpoint imp_stmt_eval
             (s:imp_stmt) (σ:pd_rbindings) : option pd_rbindings :=
      match s with
      | ImpStmtBlock vl sl =>
        let proc_one_decl c vd :=
            match c with
            | None => None
            | Some σ' =>
              match vd with
              | (v, None) =>
                Some ((v, None) :: σ')
              | (v, Some e) =>
                match imp_expr_eval σ' e with
                | None => None
                | Some d =>
                  Some ((v, Some d) :: σ')
              end
              end
            end
        in
        let σdeclared := fold_left proc_one_decl vl (Some σ) in
        let proc_one_stmt c s :=
            match c with
            | None => None
            | Some σ' =>
              imp_stmt_eval s σ'
            end
        in
        let σblock := fold_left proc_one_stmt sl σdeclared in
        let proc_one_var v c :=
            match c with
            | None => None
            | Some (_::σ') =>
              Some σ'
            | Some nil =>
              None
            end
        in
        let σerased := fold_right proc_one_var σblock vl in
        σerased
      | ImpStmtAssign v e =>
        match imp_expr_eval σ e, lookup string_dec σ v with
        | Some d, Some _ => Some (update_first string_dec σ v (Some d))
        | _, _ => None
        end
      | ImpStmtFor v e s =>
        match imp_expr_eval σ e with
        | Some d =>
          match DataToList d with
          | Some c1 =>
            let fix for_fun (dl:list Data) σ₁ :=
                match dl with
                | nil => Some σ₁
                | d::dl' =>
                  match imp_stmt_eval s ((v,Some d)::σ₁) with
                  | Some (_::σ₂) => for_fun dl' σ₂
                  | _ => None
                  end
                end in
            for_fun c1 σ
          | None =>  None
          end
        | _ => None
        end
      | ImpStmtForRange v e1 e2 s => None (* XXX TBD *)
      | ImpStmtIf e1 s1 s2 =>
        match imp_expr_eval σ e1 with
        | None => None
        | Some d =>
          match DataToBool d with
          | None => None
          | Some b =>
            if b then imp_stmt_eval s1 σ
            else imp_stmt_eval s2 σ
          end
        end
      end.

    Definition imp_function_eval f (v: Data)  : option Data :=
      match f with
      | ImpFun x s ret =>
        let σ := (x, Some v) :: nil in
        match imp_stmt_eval s σ with
        | Some σ' =>
          olift (fun x => x) (lookup equiv_dec σ ret)
        | None => None
        end
      end.

  End Evaluation.
End ImpEval.
