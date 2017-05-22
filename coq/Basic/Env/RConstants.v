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

Section RConstants.

  Require Import String.
  Require Import EquivDec.
  Require Import List.
  Require Import RUtil RList RSublist RFresh RBindings RAssoc. 
  
  (* Java equivalent: NraToNnrc inline in cnraenv_to_nnrc *)
  Definition CONST_PREFIX:string := "CONST$"%string.

  Definition mkConstantName (n:string) :=
    append CONST_PREFIX n.
  Definition mkConstant {A} (b:string*A)
    := (mkConstantName (fst b),(snd b)).
  Definition mkConstants {A} (l:list (string*A))
    := map mkConstant l.

  Section ConstantsProp.
    Definition filterConstants {A} (l:list (string*A))
      := filter (fun xy => prefix CONST_PREFIX (fst xy)) l.

    Lemma filterConstants_lookup_pre {A} (l:list (string*A)) s :
      lookup equiv_dec (filterConstants l) (append CONST_PREFIX s)
      = lookup equiv_dec l (append CONST_PREFIX s).
    Proof.
      revert s.
      induction l; simpl; trivial.
      destruct a; simpl.
      intros.
      match_case; intros; simpl.
      - dest_eqdec; trivial.
        apply IHl.
      - specialize (IHl s0).
        simpl in IHl; rewrite IHl.
        dest_eqdec.
        + simpl in *.
          rewrite prefix_nil in H.
          congruence.
        + trivial.
    Qed.

    Lemma filter_rev {A} (f:A->bool) l :
      filter f (rev l) = rev (filter f l).
    Proof.
      induction l; simpl; trivial.
      rewrite filter_app, IHl.
      simpl.
      match_destr.
      rewrite app_nil_r.
      trivial.
    Qed.
    
    Lemma filterConstants_rev {A} (l:list (string*A)) :
      filterConstants (rev l) = rev (filterConstants l).
    Proof.
      unfold filterConstants.
      rewrite filter_rev.
      trivial.
    Qed.

    Lemma mkConstants_rev {A} (l:list (string*A)) :
      mkConstants (rev l) = rev (mkConstants l).
    Proof.
      unfold mkConstants.
      rewrite map_rev.
      trivial.
    Qed.

    Lemma filterConstants_assoc_lookupr_pre {A} (l:list (string*A)) s :
      assoc_lookupr equiv_dec (filterConstants l) (append CONST_PREFIX s)
      = assoc_lookupr equiv_dec l (append CONST_PREFIX s).
    Proof.
      rewrite (assoc_lookupr_lookup equiv_dec _ (filterConstants l)).
      rewrite (assoc_lookupr_lookup equiv_dec _ l).
      rewrite <- filterConstants_rev.
      rewrite filterConstants_lookup_pre.
      trivial.
    Qed.

    Lemma filterConstants_mkConstants {A} (l:list (string*A)) :
      filterConstants (mkConstants l) = mkConstants l.
    Proof.
      induction l; simpl; trivial.
      rewrite IHl.
      rewrite prefix_nil.
      trivial.
    Qed.
  
    Lemma mkConstants_NoDup  {A} (l:list (string*A)) :
      NoDup (domain l) <-> NoDup (domain (mkConstants l)).
    Proof.
      Opaque append.
      unfold mkConstants, domain.
      rewrite map_map; simpl.
      rewrite <- (map_map (@fst _ A) (append CONST_PREFIX)).
      split; intros.
      - apply map_inj_NoDup; trivial.
        intros.
        apply append_eq_inv1 in H0; trivial.
      - apply unmap_NoDup in H.
        trivial.
        Transparent append.
    Qed.

    Lemma filterConstants_NoDup  {A} (l:list (string*A)) :
      NoDup (domain l) -> NoDup (domain (filterConstants l)).
    Proof.
      unfold filterConstants, domain.
      apply sublist_NoDup.
      apply sublist_map.
      simpl.
      apply filter_sublist.
    Qed.

    Lemma mkConstants_indom {A} (l:list (string*A)) x :
      In x (domain (mkConstants l)) ->
      prefix CONST_PREFIX x = true.
    Proof.
      intros inn.
      unfold domain, mkConstants in inn.
      rewrite map_map in inn; simpl in inn.
      apply in_map_iff in inn.
      destruct inn as [? [? ?]]; subst.
      simpl.
      apply prefix_nil.
    Qed.

    Lemma mkConstants_nindom {A} (l:list (string*A)) x :
      prefix CONST_PREFIX x = false ->
      ~ (In x (domain (mkConstants l))).
    Proof.
      intros pre inn.
      apply mkConstants_indom in inn.
      congruence.
    Qed.

    Lemma mkConstants_lookup_pre {A} l x (y:A) :
      lookup string_eqdec (mkConstants l) x = Some y ->
      prefix CONST_PREFIX x = true.
    Proof.
      intros inn.
      apply lookup_in in inn.
      apply in_dom in inn.
      eapply mkConstants_indom; eauto.
    Qed.

    Lemma mkConstants_lookup {A} (l:list (string*A)) x :
      lookup string_eqdec (mkConstants l) (append CONST_PREFIX x) = 
      lookup string_eqdec l x.
    Proof.
      Opaque append.
      induction l; simpl; trivial.
      unfold mkConstantName.
      destruct a; simpl.
      repeat match_destr; unfold Equivalence.equiv in * .
      - apply append_eq_inv1 in e.
        congruence.
      - congruence.
        Transparent append.
    Qed.

    Lemma mkConstants_assoc_lookupr {A} (l:list (string*A)) x :
      assoc_lookupr string_eqdec (mkConstants l) (append CONST_PREFIX x) = 
      assoc_lookupr string_eqdec l x.
    Proof.
      rewrite (assoc_lookupr_lookup string_eqdec _ (mkConstants l)).
      rewrite (assoc_lookupr_lookup string_eqdec _ l).
      rewrite <- mkConstants_rev.
      rewrite mkConstants_lookup.
      trivial.
    Qed.

    Lemma rec_sort_mkConstants_comm {A} (l:list (string*A)) :
      rec_sort (mkConstants l) = mkConstants (rec_sort l).
    Proof.
      unfold mkConstants.
      rewrite <- map_rec_sort.
      reflexivity.
      intros.
      unfold mkConstant; simpl.
      destruct x; destruct y; simpl.
      unfold mkConstantName.
      split; intros; auto.
    Qed.

  End ConstantsProp.

  Section World.
    Require Import RData.
    Require Import ForeignData.

    Context {fdata:foreign_data}.

    Definition WORLD:string := "WORLD"%string.
    
    (* Declares single input collection containing world *)
    Definition mkWorld (world:list data) : list (string*data)
      := (WORLD,(dcoll world))::nil.

  End World.

  Section unConst.
    Require Import String.
    Definition unConstVar (fv:string) : string :=
      if (prefix "CONST$" fv)
      then
        substring 6 ((length fv) - 6) fv
      else fv.
  End unConst.
  
End RConstants.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
