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

  Context {RuntimeEval: Runtime -> list Data -> option Data}.
  Context {OpEval: Op -> list Data -> option Data}.

  Definition imp_expr := @imp_expr Data Op Runtime.
  Definition imp_stmt := @imp_stmt Data Op Runtime.
  
  Definition rbindings := list (string * Data).
  Definition pd_rbindings := list (string * option Data).

  (** ** Evaluation Semantics *)
  Section Evaluation.
    
    Fixpoint imp_expr_eval
             (σc:rbindings) (σ:pd_rbindings) (e:imp_expr) {struct e} : option Data
      :=
        match e with
        | ImpExprGetConstant v =>
          edot σc v
        | ImpExprVar v =>
          olift id (lookup equiv_dec σ v)
        | ImpExprConst d =>
          Some (DataNormalize d)
        | ImpExprOp op el =>
          let fix lift_map (l : list imp_expr) {struct l} : option (list Data) :=
              match l with
              | nil => Some nil
              | x :: t =>
                match imp_expr_eval σc σ x with
                | Some x' => lift (fun t' : list Data => x' :: t') (lift_map t)
                | None => None
                end
              end
          in
          let x := lift_map el in
          olift (OpEval op) x
        | ImpExprRuntimeCall rt el =>
          let fix lift_map (l : list imp_expr) {struct l} : option (list Data) :=
              match l with
              | nil => Some nil
              | x :: t =>
                match imp_expr_eval σc σ x with
                | Some x' => lift (fun t' : list Data => x' :: t') (lift_map t)
                | None => None
                end
              end
          in
          let x := lift_map el in
          olift (RuntimeEval rt) x
        end.

    Fixpoint imp_stmt_eval
             (σc:rbindings) (s:imp_stmt) (σ:pd_rbindings) : option pd_rbindings :=
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
                match imp_expr_eval σc σ' e with
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
              imp_stmt_eval σc s σ'
            end
        in
        fold_left proc_one_stmt sl σdeclared
      | ImpStmtAssign v e =>
        match imp_expr_eval σc σ e, lookup string_dec σ v with
        | Some d, Some _ => Some (update_first string_dec σ v (Some d))
        | _, _ => None
        end
      | ImpStmtFor v e s => None (* XXX TBD *)
      | ImpStmtForRange v e1 e2 s => None (* XXX TBD *)
      | ImpStmtIf e1 s1 s2 =>
        match imp_expr_eval σc σ e1 with
        | None => None
        | Some d =>
          match DataToBool d with
          | None => None
          | Some b =>
            if b then imp_stmt_eval σc s1 σ
            else imp_stmt_eval σc s2 σ
          end
        end
      end.

  End Evaluation.
End ImpEval.
