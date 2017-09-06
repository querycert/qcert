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

Section RBinaryOpsSem.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import ZArith.
  Require Import Utils.
  Require Import RData.
  Require Import RDataNorm.
  Require Import RRelation.
  Require Import RUtilOps.
  Require Export RBinaryOps.
  Require Import BrandRelation.
  Require Import ForeignData.
  Require Import ForeignOps.
  
  (* Algebra Unary/Binary Ops *)

  Definition fun_of_arithbop (op:ArithBOp) : Z -> Z -> Z
    := match op with
       | ArithPlus => Z.add
       | ArithMinus=> Z.sub
       | ArithMult => Z.mul
       | ArithMin => Z.min
       | ArithMax => Z.max
       | ArithDivide=> Z.quot
       | ArithRem => Z.rem
       end.

  Context {fdata:foreign_data}.
  Context {fbop:foreign_binary_op}.
  Context (h:brand_relation_t).

  Definition fun_of_binop (bop:binOp) : data -> data -> option data :=
    match bop with
    | ABArith op =>
      fun d1 d2 =>
        match d1, d2 with
        | dnat n1, dnat n2 => Some (dnat (fun_of_arithbop op n1 n2))
        | _, _ => None
        end
    | AAnd => fun d1 d2 => unbdbool andb d1 d2
    | AOr => fun d1 d2 => unbdbool orb d1 d2
    | AEq => fun d1 d2 => unbdata (fun x y => if data_eq_dec x y then true else false) d1 d2
    | ALt => fun d1 d2 => unbdnat (fun x y => if Z_lt_dec x y then true else false) d1 d2
    | ALe => fun d1 d2 => unbdnat (fun x y => if Z_le_dec x y then true else false) d1 d2
    | AUnion => fun d1 d2 => rondcoll2 bunion d1 d2
    | AMinus => fun d1 d2 => rondcoll2 (@bminus data data_eq_dec) d1 d2
    | AMin => fun d1 d2 => rondcoll2 (@bmin data data_eq_dec) d1 d2
    | AMax => fun d1 d2 => rondcoll2 (@bmax data data_eq_dec) d1 d2
    | AContains => fun d1 d2 => ondcoll (fun l =>
                                           if in_dec data_eq_dec d1 l
                                           then dbool true else dbool false) d2
    | ASConcat => fun d1 d2 => unsdstring append d1 d2
    | AConcat =>
      fun d1 d2 =>
        match d1, d2 with
        | (drec r1), (drec r2) => Some (drec (rec_sort (r1++r2)))
        | _, _ => None
        end
    | AMergeConcat =>
      fun d1 d2 =>
        match d1, d2 with
        | (drec r1), (drec r2) =>
          match merge_bindings r1 r2 with
          | Some x => Some (dcoll ((drec x) :: nil))
          | None => Some (dcoll nil)
          end
        | _, _ => None
        end
    | AForeignBinaryOp fb => foreign_binary_op_interp h fb
    end.

  Lemma fun_of_binop_normalized {b d1 d2 o} :
    fun_of_binop b d1 d2 = Some o ->
    data_normalized h d1 -> data_normalized h d2 ->
    data_normalized h o.
  Proof.
    Hint Constructors data_normalized Forall.
    destruct b; simpl; intros;
    try solve [
          unfold rondcoll2 in *;
          destruct d1; simpl in *; try discriminate;
          destruct d2; simpl in *; try discriminate;
          inversion H; subst;
          eauto 1;
          inversion H; subst;
          constructor;
          inversion H0; inversion H1; subst;
          solve [apply bunion_Forall; trivial
                | apply bminus_Forall; trivial
                | apply bmin_Forall; trivial
                | apply bmax_Forall; trivial]
        ].
    - do 2 match_destr_in H.
      inversion H; clear H; subst.
      apply data_normalized_rec_sort_app; trivial.
    - do 2 match_destr_in H.
      unfold merge_bindings in H.
      destruct (Compat.compatible l l0); inversion H; eauto 2.
      constructor. constructor; trivial.
      apply data_normalized_rec_concat_sort; trivial.
    - destruct d2; simpl in *; try discriminate.
      match_destr_in H; inversion H; eauto.
    - eapply foreign_binary_op_normalized; eauto.
  Qed.
  
End RBinaryOpsSem.

(* 
 *** Local Variables: ***
 *** coq-load-path: (("../../../coq" "Qcert")) ***
 *** End: ***
 *)
