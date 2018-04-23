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

Require Import RUtil.
Require Import RData.
Require Import RRelation.
Require Import RAlg.
Require Import ROps.

Section UDelta.
  Require Import Program.

  Inductive Δ : Set :=
  | Δid : Δ
  | Δconst : data -> Δ
  | Δcoll : Δ -> Δ
  | Δbinop : binOp -> data -> Δ
  | Δunop : unaryOp -> Δ
  | Δmap : Δ -> Δ
  | Δselect : alg -> Δ
  | Δrec : list (string*Δ) -> Δ
  | Δcompose : Δ -> Δ -> Δ
  .

  Fixpoint map2 {A B C} (f:A -> B -> option C) (l1:list A) (l2:list B) : option (list C) :=
    match l1,l2 with
      | nil,nil => Some nil
      | a1::l1',a2::l2' =>
        match (f a1 a2) with
          | None => None
          | Some a' =>
            match map2 f l1' l2' with
              | None => None
              | Some l' => Some (a'::l')
            end
        end
      | _,_ => None
    end.

  Definition update_rec_att
             {A B C} (f:A -> B -> option C)
             (a1:(string*A)) (a2:(string*B)) : option (string*C) :=
    let at1 := (fst a1) in
    let at2 := (fst a2) in
    if string_dec (fst a1) (fst a2)
    then
      match (f (snd a1) (snd a2)) with
        | Some a => Some (at1,a)
        | None => None
      end
    else None.

  Fixpoint update (p:Δ) (ud:data) : option data :=
    match p with
      | Δid => Some ud
      | Δconst c => Some c
      | Δcoll d1 =>
        match update d1 ud with
          | Some ud' =>
            Some (dcoll (ud' :: nil))
          | None => None
        end
      | Δbinop b d1 =>
        (fun_of_binop b d1 ud)
      | Δunop u =>
        (fun_of_unaryop u ud)
      | Δmap d1 =>
        match ud with
          | dcoll udl =>
            match rmap (update d1) udl with
              | None => None
              | Some c2 => Some (dcoll c2)
            end
          | _ => None
        end
      | Δselect op =>
        match ud with
          | dcoll c1 =>
            let pred :=
                fun x' =>
                  match fun_of_alg op x' with
                    | Some (dbool b) => b
                    | _ => false
                  end
            in
            let c2 := filter pred c1 in
            Some (dcoll c2)
          | _ => None
        end
      | Δrec lr =>
        match ud with
          | drec dr =>
            match
              ((fix F2 l1 l2 :=
                 match l1,l2 with
                   | nil,nil => Some nil
                   | a1::l1',a2::l2' =>
                     match ((fun a1 a2 =>
                               let at1 := (fst a1) in
                               let at2 := (fst a2) in
                               if string_dec (fst a1) (fst a2)
                               then
                                 match (update (snd a1) (snd a2)) with
                                   | Some a => Some (at1,a)
                                   | None => None
                                 end
                               else None) a1 a2) with
                       | None => None
                       | Some a' =>
                         match F2 l1' l2' with
                           | None => None
                           | Some l' => Some (a'::l')
                         end
                     end
                   | _,_ => None
                 end) lr dr) with
              | Some l => Some (drec l)
              | None => None
            end
          | _ => None
        end
      | Δcompose d1 d2 =>
        match (update d1 ud) with
          | None => None
          | Some ud' => update d2 ud'
        end
    end.

  Definition update_opt (p:Δ) (od:option data) : option data :=
    match od with
      | Some ud => update p ud
      | None => None
    end.

  Lemma update_dist (Δ₁ Δ₂:Δ) (d:option data): 
    update_opt (Δcompose Δ₁ Δ₂) d = update_opt Δ₂ (update_opt Δ₁ d).
  Proof.
    destruct d; reflexivity.
  Qed.

  Fixpoint delta_to_query_aux (Δ₀:Δ) (idalg:alg) : alg :=
    match Δ₀ with
      | Δid => idalg
      | Δconst c => AConst c
      | Δcoll Δ₁ => (AUnop AColl) (delta_to_query_aux Δ₁ idalg)
      | Δbinop b d => ABinop b (AConst d) idalg
      | Δunop u => AUnop u idalg
      | Δmap Δ₁ => AMap (delta_to_query_aux Δ₁ AID) idalg
      | Δselect op1 => ASelect op1 idalg
      | Δrec Δrl => AConst dunit
      | Δcompose Δ₁ Δ₂ => (delta_to_query_aux Δ₁ (delta_to_query_aux Δ₂ idalg))
    end.

  Definition delta_to_query (Δ₀:Δ) : alg := delta_to_query_aux Δ₀ AID.

  Fixpoint substitute (op:alg) (idalg:alg) : alg :=
    match op with
      | AID => idalg
      | AConst d => op
      | ABinop b op1 op2 => ABinop b (substitute op1 idalg) (substitute op2 idalg)
      | AUnop u op1 => AUnop u (substitute op1 idalg)
      | AMap op1 op2 => AMap op1 (substitute op2 idalg)
      | AMapConcat op1 op2 => AMapConcat op1 (substitute op2 idalg)
      | AProduct op1 op2 => AProduct (substitute op1 idalg) (substitute op2 idalg)
      | ASelect op1 op2 => ASelect op1 (substitute op2 idalg)
      | ADefault op1 op2 => ADefault (substitute op1 idalg) (substitute op2 idalg)
    end.

  Lemma substitute_id (op:alg) :
    substitute op AID = op.
  Proof.
    induction op; simpl; try reflexivity;
    try (rewrite IHop; reflexivity);
    try (rewrite IHop2; reflexivity);
    try (rewrite IHop1; rewrite IHop2; reflexivity).
  Qed.

 (*
  Lemma delta_to_query_substitutes (Δ₀:Δ) (op:alg) :
    (delta_to_query_aux Δ₀ op) = substitute (delta_to_query_aux Δ₀ AID) op.
  Proof.
    induction Δ₀; simpl; try reflexivity.
    rewrite IHΔ₀; reflexivity.
    rewrite IHΔ₀2. rewrite substitute_id in *; reflexivity.
    rewrite IHΔ₀1; ; reflexivity.
    rewrite substitute_id.
 *)    
  
  (*
  Lemma delta_to_query_equiv (Δ₀:Δ) d : 
    (delta_to_query Δ₀) @ d = update Δ₀ d.
  Proof.
    revert d.
    unfold delta_to_query.
    induction Δ₀; try reflexivity; intros.
    - simpl; rewrite IHΔ₀; reflexivity.
    - simpl; destruct d; try reflexivity.
      induction l; try reflexivity.
      simpl in *. rewrite (IHΔ₀ a); destruct (update Δ₀ a); try reflexivity.
      assert (rmap (fun_of_alg (delta_to_query_aux Δ₀ AID)) l = rmap (update Δ₀) l).
      revert IHl.
      elim (rmap (fun_of_alg (delta_to_query_aux Δ₀ AID)) l);
      elim (rmap (update Δ₀) l); intros; congruence.
      rewrite H.
      destruct (rmap (update Δ₀) l); reflexivity.
    - addddmit.  (* still need work on record update – no easy corresponding query *)
    - simpl. addddmit.  (* still need work on compose – possibly showing an intermediate lemma that does substitute with AID. *)
  Qed.
   *)



(* Eventual lemma: Q @ (update Δ₀ d) = update (maint d Δ₀) (Q @ d) *)
(* Eventual lemma: Q @ (Δ₀[@d]) = (maint d Δ₀)[@(Q @ d)] *)

End UDelta.

