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
Require Import Compare_dec.
Require Import ZArith.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import Data.
Require Import DataLift.
Require Import DataNorm.
Require Import DataSort.
Require Import DatatoJSON.
Require Import ForeignDataToJSON.
Require Import ForeignOperators.
Require Import Iterators.
Require Import RecOperators.
Require Import OperatorsUtils.
Require Import SortBy.
Require Export UnaryOperators.

Section UnaryOperatorsSem.
  Context {fdata:foreign_data}.
  Context {ftojson:foreign_to_JSON}.

  Definition nat_arith_unary_op_eval (op:nat_arith_unary_op) (z:Z) :=
    match op with
    | NatAbs => Z.abs z
    | NatLog2 => Z.log2 z
    | NatSqrt => Z.sqrt z
    end.

  Definition float_arith_unary_op_eval (op:float_arith_unary_op) (f:float) :=
    match op with
    | FloatNeg => float_neg f
    | FloatSqrt => float_sqrt f
    | FloatExp => float_exp f
    | FloatLog => float_log f
    | FloatLog10 => float_log10 f
    | FloatCeil => float_ceil f
    | FloatFloor => float_floor f
    | FloatAbs => float_absolute f
    end.

  Context (h:brand_relation_t).
  Context {fuop:foreign_unary_op}.

  Global Instance ToString_data : ToString data
    := { toString := foreign_unary_op_data_tostring }.

  Fixpoint defaultDataToString (d:data) : string
    := match d with
       | dunit => "unit"%string
       | dnat n => toString n
       | dfloat n => toString n
       | dbool b => toString b
       | dstring s => stringToString s
       | dcoll l => bracketString 
                      "["%string
                      (String.concat ", "%string
                              (string_sort (map defaultDataToString l)))
                      "]"%string
       | drec lsd => bracketString
                       "{"%string
                       (String.concat ", "%string 
                               (map (fun xy => let '(x,y):=xy in 
                                               (append (stringToString x) (append "->"%string
                                                                                  (defaultDataToString y)))
                                    ) lsd))
                       "}"%string
       | dleft d => bracketString
                      "Left("%string
                      (defaultDataToString d)
                      ")"%string
       | dright d => bracketString
                       "Right("%string
                       (defaultDataToString d)
                       ")"%string
       | dbrand b d => (bracketString
                          "<"
                          (append (@toString _ ToString_brands b)
                                  (append ":" (defaultDataToString d)))
                          ">")
       | dforeign fd => toString fd
       end.

  Definition unary_op_eval (uop:unary_op) (d:data) : option data :=
    match uop with
    | OpIdentity => Some d
    | OpNeg => unudbool negb d
    | OpRec s => Some (drec ((s,d) :: nil))
    | OpDot s =>
      match d with
      | drec r => edot r s
      | _ => None
      end
    | OpRecRemove s =>
      match d with
      | drec r => Some (drec (rremove r s))
      | _ => None
      end
    | OpRecProject sl =>
      match d with
      | drec r => Some (drec (rproject r sl))
      | _ => None
      end
    | OpBag => Some (dcoll (d :: nil))
    | OpSingleton =>
      match d with
      | dcoll (d'::nil) => Some (dsome d')
      | dcoll _ => Some dnone
      | _ => None
      end
    | OpFlatten => 
      lift_oncoll (fun l => (lift dcoll (oflatten l))) d
    | OpDistinct =>
      rondcoll (@bdistinct data data_eq_dec) d
    | OpOrderBy sc =>
      data_sort sc d (* XXX Some very limited/hackish sorting XXX *)
    | OpCount =>
      lift dnat (ondcoll (fun z => Z_of_nat (bcount z)) d)
    | OpToString =>
      Some (dstring (foreign_unary_op_data_tostring d))
    | OpToText =>
      Some (dstring (foreign_unary_op_data_totext d))
    | OpLength =>
      unndstring (fun s => Z_of_nat (String.length s)) d
    | OpSubstring start olen =>
      match d with
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
      end
    | OpLike pat oescape =>
      match d with
      | dstring s => Some (dbool (string_like s pat oescape))
      | _ => None
      end
    | OpLeft => Some (dleft d)
    | OpRight => Some (dright d)
    | OpBrand b => Some (dbrand (canon_brands h b) d)
    | OpUnbrand =>
      match d with
      | dbrand _ d' => Some d'
      | _ => None
      end
    | OpCast b =>
      match d with
      | dbrand b' _ =>
        if (sub_brands_dec h b' b)
        then
          Some (dsome d)
        else
          Some (dnone)
      | _ => None
      end
    | OpNatUnary op =>
      match d with
      | dnat n => Some (dnat (nat_arith_unary_op_eval op n))
      | _ => None
      end
    | OpNatSum => 
      lift dnat (lift_oncoll dsum d)
    | OpNatMin =>
      match d with
      | dcoll l => lifted_min l
      | _ => None
      end
    | OpNatMax =>
      match d with
      | dcoll l => lifted_max l
      | _ => None
      end
    | OpNatMean => 
      lift dnat (lift_oncoll darithmean d)
    | OpFloatOfNat =>
      match d with
      | dnat n => Some (dfloat (float_of_int n))
      | _ => None
      end
    | OpFloatUnary op =>
      match d with
      | dfloat n => Some (dfloat (float_arith_unary_op_eval op n))
      | _ => None
      end
    | OpFloatTruncate =>
      match d with
      | dfloat f => Some (dnat (float_truncate f))
      | _ => None
      end
    | OpFloatSum =>
      lift_oncoll lifted_fsum d
    | OpFloatMean =>
      lift_oncoll lifted_farithmean d
    | OpFloatBagMin =>
      lift_oncoll lifted_fmin d
    | OpFloatBagMax =>
      lift_oncoll lifted_fmax d
    | OpForeignUnary fu => foreign_unary_op_interp h fu d
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

  Lemma unary_op_eval_normalized {u d o} :
    unary_op_eval u d = Some o ->
    data_normalized h d ->
    data_normalized h o.
  Proof.
    Hint Constructors data_normalized Forall.
    Hint Resolve dnnone dnsome.

    unary_op_cases (destruct u) Case; simpl;
    try solve [inversion 1; subst; eauto 3
              | destruct d; inversion 1; subst; eauto 3].
    - Case "OpDot"%string.
      destruct d; try discriminate.
      intros. eapply data_normalized_edot; eauto.
    - Case "OpRecRemove"%string.
      destruct d; try discriminate.
      inversion 1; subst.
      intros; apply data_normalized_rremove; eauto.
    - Case "OpRecProject"%string.
      destruct d; try discriminate.
      inversion 1; subst.
      intros; apply data_normalized_rproject; eauto.
    - Case "OpSingleton"%string.
      destruct d; simpl; try discriminate.
      destruct l.
      + inversion 1. inversion 1; subst; eauto.
      + destruct l; inversion 1; subst; eauto 2.
        rewrite <- data_normalized_dcoll; intros [??]; eauto.
    - Case "OpFlatten"%string.
      destruct d; simpl; try discriminate.
      unfold oflatten.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      intros.
      inversion H; subst.
      constructor.
      apply (lift_flat_map_Forall e H1); intros.
      match_destr_in H0.
      inversion H0; subst.
      inversion H2; trivial.
    - Case "OpDistinct"%string.
      destruct d; try discriminate.
      unfold rondcoll.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      simpl in *. inversion e; subst.
      intros; apply data_normalized_bdistinct; trivial.
    - Case "OpOrderBy"%string.
      apply data_sort_normalized.
    - Case "OpUnbrand"%string.
      destruct d; simpl; try discriminate.
      inversion 1; subst.
      inversion 1; subst; trivial.
    - Case "OpCast"%string.
      destruct d; simpl; try discriminate.
      match_destr; inversion 1; subst; eauto.
    - Case "OpNatSum"%string.
      destruct d; simpl; try discriminate.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "OpNatMin"%string.
      destruct d; simpl; try discriminate.
      unfold lifted_min.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "OpNatMax"%string.
      destruct d; simpl; try discriminate.
      unfold lifted_min.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "OpNatMean"%string.
      destruct d; simpl; try discriminate.
      intros.
      apply some_lift in H.
      destruct H as [???]; subst.
      eauto.
    - Case "OpFloatSum"%string.
      destruct d; simpl; try discriminate.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "OpFloatMean"%string.
      destruct d; simpl; try discriminate.
      intros.
      apply some_lift in H.
      destruct H as [???]; subst.
      eauto.
    - Case "OpFloatBagMin"%string.
      destruct d; simpl; try discriminate.
      unfold lifted_min.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "OpFloatBagMax"%string.
      destruct d; simpl; try discriminate.
      unfold lifted_min.
      intros ll; apply some_lift in ll.
      destruct ll; subst.
      eauto.
    - Case "OpForeignUnary"%string.
      intros eqq dn.
      eapply foreign_unary_op_normalized in eqq; eauto.
  Qed.

End UnaryOperatorsSem.

