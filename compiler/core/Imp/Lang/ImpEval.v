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
Require Import ZArith.
Require Import Bool.
Require Import EquivDec.
Require Import Utils.
Require Import Imp.

Section ImpEval.
  Import ListNotations.

  Context {Model: Type}.
  Context {Constant: Set}.
  Context {Op: Set}.
  Context {Runtime: Set}.

  Context {ConstantNormalize: Constant -> Model}.
  Context {ModelToBool: Model -> option bool}.
  Context {ModelToZ: Model -> option Z}.
  Context {ModelToList: Model -> option (list Model)}.
  Context {ZToModel: Z -> Model}.

  Context {RuntimeEval: Runtime -> list Model -> option Model}.
  Context {OpEval: Op -> list Model -> option Model}.

  Definition imp_expr := @imp_expr Constant Op Runtime.
  Definition imp_stmt := @imp_stmt Constant Op Runtime.
  
  Definition rbindings := list (string * Model).
  Definition pd_rbindings := list (string * option Model).

  (** ** Evaluation Semantics *)
  Section Evaluation.
    Fixpoint imp_expr_eval
             (σ:pd_rbindings) (e:imp_expr) {struct e} : option Model
      :=
        match e with
        | ImpExprError msg =>
          None
        | ImpExprVar v =>
          olift (fun x => x) (lookup equiv_dec σ v)
        | ImpExprConst d =>
          Some (ConstantNormalize d)
        | ImpExprOp op el =>
          olift (OpEval op) (lift_map (fun x => x) (map (imp_expr_eval σ) el))
        | ImpExprRuntimeCall rt el =>
          olift (RuntimeEval rt) (lift_map (fun x => x) (map (imp_expr_eval σ) el))
        end.

    Local Open Scope Z_scope.

    Definition nb_iter (n1: Z) (n2: Z) :=
      if n1 <=? n2 then S (Z.to_nat (n2 - n1))
      else 0%nat.

    (* Auxiliary function to eval all the variable declarations in a block *)
    Definition imp_decls_eval (σ:pd_rbindings) (vl:list (string * option imp_expr)) : option pd_rbindings :=
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
      fold_left proc_one_decl vl (Some σ).

    (* Auxiliary function to erase all the variable declarations in a block *)
    Definition imp_decls_erase (σ:option pd_rbindings) {A} (vl:list A) : option pd_rbindings :=
      let proc_one_var v c :=
          match c with
          | None => None
          | Some (_::σ') =>
            Some σ'
          | Some nil =>
            None
          end
      in
      fold_right proc_one_var σ vl.

    Lemma imp_decls_erase_none {A} (vl:list A) :
      imp_decls_erase None vl = None.
    Proof.
      induction vl; simpl; [|rewrite IHvl]; reflexivity.
    Qed.

    Lemma imp_decls_erase_remove_map {A B} σ (vl:list A) (f:A -> B) :
      imp_decls_erase σ (map f vl) = imp_decls_erase σ vl.
    Proof.
      induction vl; simpl; [|rewrite IHvl]; reflexivity.
    Qed.

    Fixpoint imp_stmt_eval
             (s:imp_stmt) (σ:pd_rbindings) { struct s } : option pd_rbindings :=
      match s with
      | ImpStmtBlock vl sl =>
        let σdeclared := imp_decls_eval σ vl in
        let proc_one_stmt c s :=
            match c with
            | None => None
            | Some σ' => imp_stmt_eval s σ'
            end
        in
        let σblock :=
            olift (fun σ' => fold_left proc_one_stmt sl (Some σ')) σdeclared
        in
        let σerased := imp_decls_erase σblock vl in
        σerased
      | ImpStmtAssign v e =>
        match imp_expr_eval σ e, lookup string_dec σ v with
        | Some d, Some _ => Some (update_first string_dec σ v (Some d))
        | _, _ => None
        end
      | ImpStmtFor v e s =>
        match imp_expr_eval σ e with
        | Some d =>
          match ModelToList d with
          | Some c1 =>
            let fix for_fun (dl:list Model) σ₁ :=
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
      | ImpStmtForRange v e1 e2 s =>
        match olift ModelToZ (imp_expr_eval σ e1), olift ModelToZ (imp_expr_eval σ e2) with
        | Some n1, Some n2 =>
          let fix for_range n n1 σ₁ :=
             match n with
             | O => Some σ₁
             | S n' =>
               match imp_stmt_eval s ((v, Some (ZToModel n1)) :: σ₁) with
               | Some (_::σ₂) => for_range n' (n1 + 1) σ₂
               | _ => None
               end
             end
          in
          for_range (nb_iter n1 n2) n1 σ
        | _, _ => None
        end
      | ImpStmtIf e1 s1 s2 =>
        match imp_expr_eval σ e1 with
        | None => None
        | Some d =>
          match ModelToBool d with
          | None => None
          | Some b =>
            if b then imp_stmt_eval s1 σ
            else imp_stmt_eval s2 σ
          end
        end
      end.

    Definition imp_function_eval f (v:Model) : option Model :=
      match f with
      | ImpFun x s ret =>
        let σ := [ (ret, None); (x, Some v) ] in
        match imp_stmt_eval s σ with
        | Some σ' =>
          olift (fun x => x) (lookup equiv_dec σ' ret)
        | None => None
        end
      end.

    Definition imp_eval (q:imp) (d:Model) : option (option Model)
      := match q with
         | ImpLib [ (fname, f) ] => Some (imp_function_eval f d)
         (* XXX What happens when more than one functions ? XXX *)
         | _ => None
         end.

  End Evaluation.
End ImpEval.
