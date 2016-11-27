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

Section RUnaryOpsSem.

  Require Import String List Compare_dec ZArith.
  
  Require Import Utils.
  Require Import RBag RData RDataNorm RDataSort RRelation.
  Require Import RUtilOps.
  Require Export RUnaryOps.
  Require Import BrandRelation.
  Require Import ForeignData.
  Require Import ForeignOps.

  Require Import ZArith.

  Context {fdata:foreign_data}.
  
  Definition lifted_zbag (l : list data) : option (list Z) :=
    rmap (ondnat (fun x => x)) l.
  Definition lifted_min (l : list data) : option data :=
    lift dnat (lift bnummin (lifted_zbag l)).
  Definition lifted_max (l : list data) : option data :=
    lift dnat (lift bnummax (lifted_zbag l)).

  Definition fun_of_arithuop (op:ArithUOp) : Z -> Z
  := match op with
         | ArithAbs => Z.abs
         | ArithLog2 => Z.log2
         | ArithSqrt => Z.sqrt
     end.

  Context {fuop:foreign_unary_op}.

  Context (h:brand_relation_t).

  Definition fun_of_unaryop (uop:unaryOp) : data -> option data :=
    match uop with
    | AIdOp =>
      fun d => Some d
    | ANeg =>
      fun d => unudbool negb d
    | AColl =>
      fun d => Some (dcoll (d :: nil))
    | ASingleton =>
      fun d =>
        match d with
        | dcoll (d'::nil) => Some (dsome d')
        | dcoll _ => Some dnone
        | _ => None
        end
    | AFlatten => 
      fun d => lift_oncoll (fun l => (lift dcoll (rflatten l))) d
    | ADistinct =>
      fun d => rondcoll (@bdistinct data data_eq_dec) d
    | AOrderBy sc =>
      fun d => data_sort sc d (* XXX Some very limited/hackish sorting XXX *)
    | ARec s =>
      fun d => Some (drec ((s,d) :: nil))
    | ADot s =>
      fun d =>
        match d with
        | drec r => edot r s
        | _ => None
        end
    | ARecRemove s =>
      fun d =>
        match d with
        | drec r => Some (drec (rremove r s))
        | _ => None
        end
    | ARecProject sl =>
      fun d =>
        match d with
        | drec r => Some (drec (rproject r sl))
        | _ => None
        end
    | ACount =>
      fun d => lift dnat (ondcoll (fun z => Z_of_nat (bcount z)) d)
    | ASum => 
      fun d => lift dnat (lift_oncoll dsum d)
    | ANumMin =>
      fun d => match d with
               | dcoll l => lifted_min l
               | _ => None
               end
    | ANumMax =>
      fun d => match d with
               | dcoll l => lifted_max l
               | _ => None
               end
    | AArithMean => 
      fun d => lift dnat (lift_oncoll darithmean d)
    | AToString =>
      fun d => Some (dstring (dataToString d))
    | ASubstring start olen =>
      fun d =>
                (match d with
                 | dstring s =>
                   Some (dstring (
                   let real_start :=
                       (match start with
                        | 0%Z => 0
                     | Z.pos p => Pos.to_nat p
                     | Z.neg n => (String.length s) - (Pos.to_nat n)
                        end) in
                   let real_olen :=
                       match olen with
                       | Some len =>
                         match len with
                         | 0%Z => 0
                         | Z.pos p => Pos.to_nat p
                         | Z.neg n => 0
                         end
                       | None => (String.length s) - real_start
                       end in
                   (substring real_start real_olen s)))
                 | _ => None
                 end)
    | ALike pat oescape =>
      fun d =>
        match d with
        | dstring s => Some (dbool (string_like s pat oescape))
        | _ => None
        end
    | ALeft =>
      fun d => Some (dleft d)
    | ARight =>
      fun d => Some (dright d)
    | ABrand b =>
      fun d => Some (dbrand (canon_brands h b) d)
    | AUnbrand =>
      fun d => match d with
               | dbrand _ d' => Some d'
               | _ => None
               end
    | ACast b =>
      fun d =>
        match d with
        | dbrand b' _ =>
          if (sub_brands_dec h b' b)
          then
            Some (dsome d)
          else
            Some (dnone)
        | _ => None
        end
    | AUArith op =>
      fun d =>
        match d with
        | dnat n => Some (dnat (fun_of_arithuop op n))
        | _ => None
        end
    | AForeignUnaryOp fu => foreign_unary_op_interp h fu
    end.

  Lemma data_normalized_edot l s o :
    edot l s = Some o ->
    data_normalized h (drec l) ->
    data_normalized h o.
  Proof.
    unfold edot.
    inversion 2; subst.
    apply assoc_lookupr_in in H.
    rewrite Forall_forall in H2.
    specialize (H2 _ H).
    simpl in *; trivial.
  Qed.

  Lemma data_normalized_filter l :
    data_normalized h (drec l) ->
    forall f, data_normalized h (drec (filter f l)).
  Proof.
    inversion 1; subst; intros.
    constructor.
    - apply Forall_filter; trivial.
    - apply (@sorted_over_filter string ODT_string); trivial.
  Qed.

  Lemma data_normalized_rremove l :
    data_normalized h (drec l) ->
    forall s, data_normalized h (drec (rremove l s)).
  Proof.
    unfold rremove; intros.
    apply data_normalized_filter; trivial.
  Qed.

   Lemma data_normalized_rproject l :
    data_normalized h (drec l) ->
    forall l2, data_normalized h (drec (rproject l l2)).
  Proof.
    unfold rremove; intros.
    unfold rproject.
    apply data_normalized_filter; trivial.
  Qed.

  Lemma data_normalized_bdistinct l :
    data_normalized h (dcoll l) -> data_normalized h (dcoll (bdistinct l)).
  Proof.
    inversion 1; subst.
    constructor.
    apply bdistinct_Forall; trivial.
  Qed.

  Lemma dnnone : data_normalized h dnone.
  Proof.
    repeat constructor.
  Qed.

  Lemma dnsome d :
    data_normalized h d ->
    data_normalized h (dsome d).
  Proof.
    repeat constructor; trivial.
  Qed.

  Lemma fun_of_unaryop_normalized {u d o} :
    fun_of_unaryop u d = Some o ->
    data_normalized h d ->
    data_normalized h o.
  Proof.
    Hint Constructors data_normalized Forall.
    Hint Resolve dnnone dnsome.

    unaryOp_cases (destruct u) Case; simpl;
    try solve [inversion 1; subst; eauto 3
              | destruct d; inversion 1; subst; eauto 3].
    - Case "ASingleton"%string.
      destruct d; simpl; try discriminate.
      destruct l.
      + inversion 1. inversion 1; subst; eauto.
      + destruct l; inversion 1; subst; eauto 2.
        rewrite <- data_normalized_dcoll; intros [??]; eauto.
    - Case "AFlatten"%string.
      destruct d; simpl; try discriminate.
      unfold rflatten.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      intros.
      inversion H; subst.
      constructor.
      apply (oflat_map_Forall e H1); intros.
      match_destr_in H0.
      inversion H0; subst.
      inversion H2; trivial.
    - Case "ADistinct"%string.
      destruct d; try discriminate.
      unfold rondcoll.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      simpl in *. inversion e; subst.
      intros; apply data_normalized_bdistinct; trivial.
    - Case "AOrderBy"%string.
      apply data_sort_normalized.
    - Case "ADot"%string.
      destruct d; try discriminate.
      intros. eapply data_normalized_edot; eauto.
    - Case "ARecRemove"%string.
      destruct d; try discriminate.
      inversion 1; subst.
      intros; apply data_normalized_rremove; eauto.
    - Case "ARecProject"%string.
      destruct d; try discriminate.
      inversion 1; subst.
      intros; apply data_normalized_rproject; eauto.
    - Case "ASum"%string.
      destruct d; simpl; try discriminate.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "ANumMin"%string.
      destruct d; simpl; try discriminate.
      unfold lifted_min.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "ANumMax"%string.
      destruct d; simpl; try discriminate.
      unfold lifted_min.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "AArithMean"%string.
      destruct d; simpl; try discriminate.
      intros.
      apply some_lift in H.
      destruct H as [???]; subst.
      eauto.
    - Case "AUnbrand"%string.
      destruct d; simpl; try discriminate.
      inversion 1; subst.
      inversion 1; subst; trivial.
    - Case "ACast"%string.
      destruct d; simpl; try discriminate.
      match_destr; inversion 1; subst; eauto.
    - Case "AForeignUnaryOp"%string.
      intros eqq dn.
      eapply foreign_unary_op_normalized in eqq; eauto.
  Qed.

End RUnaryOpsSem.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
