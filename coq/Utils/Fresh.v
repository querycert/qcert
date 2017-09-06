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

(** Support for creating and reasoning about fresh names (represented
as strings). *)

Section Fresh.
  Require Import String.
  Require Import List.
  Require Import Arith Min.
  Require Import EquivDec.
  Require Import Omega.
  Require Import CoqLibAdd.
  Require Import ListAdd.
  Require Import StringAdd.
  Require Import Digits.
  Require Import Lift.
  Require Import Sublist.

  Section finder.
    Context {A:Type}.
    Context (incr:A->A).
    Context (f:A->bool).
    
    Fixpoint find_bounded (bound:nat) (init:A)
      := match bound with
           | O => None
           | S n =>
             if f init
             then Some init
             else find_bounded n (incr init)
         end.

    Lemma find_bounded_correct bound init y :
      find_bounded bound init = Some y ->
      f y = true.
    Proof.
      revert init.
      induction bound; simpl; intros.
      - discriminate.
      - match_case_in H; intros eqq; rewrite eqq in H.
        + inversion H; congruence.
        + eauto.
    Qed.
    
  End finder.

  Lemma find_bounded_S_ge f bound init y :
    find_bounded S f bound init = Some y ->
    y >= init.
  Proof.
    revert init y.
    induction bound; simpl; intros.
    - discriminate.
    - match_destr_in H.
      + inversion H; subst; omega.
      + specialize (IHbound (S init) _ H).
        omega.
  Qed.

  Lemma find_bounded_S_seq f bound init :
    find_bounded S f bound init = find f (seq init bound).
  Proof.
    revert init.
    induction bound; simpl; trivial; intros.
    match_destr; auto.
  Qed.

  Require Import Permutation.
  
  Lemma incl_NoDup_sublist_perm {A} {dec:EqDec A eq} {l1 l2:list A} :
    NoDup l1 ->
    incl l1 l2 ->
    exists l1', Permutation l1 l1' /\ sublist l1' l2.
  Proof.
    unfold incl.
    revert l1.
    induction l2; simpl.
    - destruct l1; simpl; eauto 3.
      intros ? inn.
      specialize (inn a); intuition.
    - intros.
      case_eq (In_dec dec a l1); intros.
      + destruct (in_split _ _ i) as [x [y ?]]; subst.
        assert (perm:Permutation (x ++ a :: y) (a::x ++ y))
          by (rewrite Permutation_middle; reflexivity).
        rewrite perm in H.
        inversion H; clear H; subst.
        destruct (IHl2 (x++y)) as [l1' [l1'perm l1'incl]]; trivial.
        * intros ? inn.
          { destruct (H0 a0); trivial.
            - rewrite perm; simpl; intuition.
            - subst. intuition.
          } 
        * exists (a::l1').
           { split.
             - rewrite perm.
               eauto.
             - apply sublist_cons.
               trivial.
           } 
      + destruct (IHl2 l1 H) as [x [perm subl]].
        * intros ? inn.
          destruct (H0 _ inn); subst; intuition.
        * exists x; split; trivial.
            apply sublist_skip.
            trivial.
  Qed.

    Lemma incl_NoDup_length_le {A} {dec:EqDec A eq} {l1 l2:list A} :
    NoDup l1 ->
    incl l1 l2 ->
    length l1 <= length l2.
    Proof.
      intros nd inc.
      destruct (incl_NoDup_sublist_perm nd inc) as [l1' [perm subl]].
      rewrite (Permutation_length perm).
      apply sublist_length.
      trivial.
    Qed.

  Lemma find_fresh_from {A:Type} {dec:EqDec A eq} (bad l:list A) :
    length l > length bad ->
    NoDup l ->
    {y | find (fun x : A => if in_dec equiv_dec x bad then false else true) l = Some y}.
  Proof.
    rewrite find_filter.
    unfold hd_error.
    match_case; eauto; intros.
    generalize (filter_nil_implies_not_pred _ l H); intros.
    cut (length l <= length bad); [intuition|].
    apply incl_NoDup_length_le; trivial.
    intros ? inn.
    specialize (H2 _ inn).
    match_destr_in H2.
  Defined.

  Lemma find_over_map {A B} f (g:A->B) (l:list A) :
    find f (map g l) = lift g (find (fun x => f (g x)) l).
  Proof.
    induction l; simpl; trivial.
    match_destr.
  Qed.

  Lemma seq_ge init bound :
    forall x, In x (seq init bound) -> x >= init.
  Proof.
    revert init.
    induction bound; simpl; intuition.
    specialize (IHbound (S init) x H0).
    omega.
  Qed.
    
  Lemma seq_NoDup init bound :
    NoDup (seq init bound).
  Proof.
    revert init.
    induction bound; simpl; intros.
    - constructor.
    - econstructor; eauto.
      intro inn.
      apply seq_ge in inn.
      omega.
  Qed.
    
  Lemma find_bounded_S_nin_finds' {A:Type} f {dec:EqDec A eq} (dom:list A)
        (bound:nat) (pf:bound > length dom)
        (inj:forall x y, f x = f y -> x = y) :
        {y:A | lift f (find_bounded S
                 (fun x =>
                    if in_dec equiv_dec (f x) dom
                    then false else true)
                 bound 0) = Some y}.
  Proof.
    rewrite find_bounded_S_seq.
    rewrite <- (find_over_map (fun x  => if in_dec equiv_dec x dom then false else true) f).
    apply find_fresh_from.
    - rewrite map_length.
      rewrite seq_length.
      trivial.
    - apply map_inj_NoDup; trivial.
      apply seq_NoDup.
  Defined.

  (* This version has better computational properties *)
  Definition find_bounded_S_nin_finds {A:Type} f {dec:EqDec A eq} (dom:list A)
        (bound:nat) (pf:bound > length dom)
        (inj:forall x y, f x = f y -> x = y) :
        {y:A | lift f (find_bounded S
                 (fun x =>
                    if in_dec equiv_dec (f x) dom
                    then false else true)
                 bound 0) = Some y}.
  Proof.
    case_eq (find_bounded S
        (fun x : nat => if in_dec equiv_dec (f x) dom then false else true)
        bound 0).
    - intros; simpl.
      exists (f n); reflexivity.
    - destruct (find_bounded_S_nin_finds' f dom bound pf inj); intros.
      rewrite H in e.
      simpl in e. discriminate.
  Defined.
  
  Lemma compose_inj {A B C} (f:B->C) (g:A->B) :
    (forall x y, f x = f y -> x = y) ->
    (forall x y, g x = g y -> x = y) ->
    (forall x y, f (g x) = f (g y) -> x = y).
  Proof.
    intuition.
  Qed.
    
  Definition find_fresh_inj_f {A:Type} {dec:EqDec A eq} f (inj:forall x y, f x = f y -> x = y) (dom:list A) : A
    := proj1_sig (find_bounded_S_nin_finds f dom (S (length dom)) (gt_Sn_n _) inj).

  Lemma find_fresh_inj_f_fresh {A:Type} {dec:EqDec A eq} f (inj:forall x y, f x = f y -> x = y) (dom:list A) :
    ~ In (find_fresh_inj_f f inj dom) dom.
  Proof.
    unfold find_fresh_inj_f.
    match goal with
      | [|- context[ proj1_sig ?x ]] => destruct x
    end; simpl.
    apply some_lift in e.
    destruct e as [? e ?]; subst.
    apply find_bounded_correct in e.
    match_destr_in e.
  Qed.

  Definition find_fresh_string (dom:list string)
    := find_fresh_inj_f
         nat_to_string16
         nat_to_string16_inj
         dom.
  
  Lemma find_fresh_string_is_fresh (dom:list string) : 
    ~ In (find_fresh_string dom) dom.
  Proof.
    unfold find_fresh_string.
    apply find_fresh_inj_f_fresh.
  Qed.

  Lemma append_eq_inv1 x y z : append x y = append x z -> y = z.
  Proof.
    revert y z.
    induction x; simpl; trivial; intros.
    inversion H; subst.
    auto.
  Qed.

  Lemma prefix_refl y : prefix y y = true.
  Proof.
    induction y; simpl; trivial.
    match_destr; congruence.
  Qed.
    
  Lemma substring_append_cancel x y :
    substring (String.length x) (String.length y) (append x y) = y.
  Proof.
    revert y.
    induction x; simpl; intros.
    - apply prefix_correct. apply prefix_refl.
    - trivial.
  Qed.

  Lemma string_length_append x y :
    String.length (append x y) = String.length x + String.length y.
  Proof.
    revert y.
    induction x; simpl; auto.
  Qed.

  Lemma prefix_nil post : prefix ""%string post = true.
  Proof.
    destruct post; trivial.
  Qed.

  Lemma prefix_app pre post : prefix pre (append pre post) = true.
  Proof.
    revert post.
    induction pre; intros; simpl.
    - apply prefix_nil.
    - match_destr; intuition.
  Qed.

  Lemma prefix_break {pre x} :
    prefix pre x = true ->
    {y | x = append pre y}.
  Proof.
    revert x.
    induction pre; simpl.
    - eauto.
    - destruct x; simpl; try discriminate.
      match_destr.
      subst; intros p.
      destruct (IHpre _ p).
      subst.
      eauto.
  Qed.

  
  Lemma substring_split s n m l :
    append (substring s n l) (substring (s+n) m l) = substring s (n+m) l.
  Proof.
    revert n m s.
    induction l; simpl; destruct s; destruct n; simpl; trivial.
    - f_equal.
      apply IHl.
    - rewrite IHl; simpl; trivial.
    - rewrite IHl. simpl; trivial.
  Qed.

  Lemma substring_all l :
    substring 0 (String.length l) l = l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma substring_bounded s n l :
    substring s n l = substring s (min n (String.length l - s)) l.
  Proof.
    revert s n.
    induction l; destruct s; destruct n; simpl; trivial.
    - rewrite IHl; simpl.
      f_equal.
      f_equal.
      f_equal.
      omega.
    - rewrite IHl.
      match_case.
  Qed.

  Lemma substring_le_prefix s n m l :
    n <= m ->
    prefix (substring s n l) (substring s m l) = true.
  Proof.
    revert s n m.
    induction l; destruct s; destruct n; destruct m; simpl; trivial;
    try omega; intuition.
    match_destr; intuition.
  Qed.

  Lemma substring_prefix n l :
    prefix (substring 0 n l) l = true.
  Proof.
    rewrite substring_bounded.
    rewrite <- (substring_all l) at 3.
    apply substring_le_prefix.
    replace (String.length l - 0) with (String.length l) by omega.
    apply le_min_r.
  Qed.

  Lemma in_of_append pre y l :
      In (append pre y) l <->
      In y (map
              (fun x => substring (String.length pre) (String.length x - String.length pre) x)
              (filter (prefix pre) l)).
  Proof.
    rewrite in_map_iff.
    split; intros.
    - exists (append pre y).
      rewrite string_length_append.
      replace ((String.length pre + String.length y - String.length pre))
      with (String.length y) by omega.
      rewrite substring_append_cancel.
      split; trivial.
      apply filter_In.
      split; trivial.
      apply prefix_app.
      - destruct H as [x [subx inx]]; subst.
        apply filter_In in inx.
        destruct inx as [inx prex].
        destruct (prefix_break prex).
        subst.
        rewrite string_length_append.
        replace ((String.length pre + String.length x0 - String.length pre))
        with (String.length x0) by omega.
        rewrite substring_append_cancel.
        trivial.
  Qed.

  (* Java equivalent: NnrcOptimizer.fresh_var (serves same purpose, not an exact translation) *)
  Definition fresh_var (pre:string) (dom:list string) :=
    let problems:=filter (prefix pre) dom in
    let problemEnds:=
        map (fun x => substring (String.length pre) (String.length x - String.length pre) x) problems in
    append pre (find_fresh_string problemEnds).

  Lemma fresh_var_fresh pre (dom:list string) : 
    ~ In (fresh_var pre dom) dom.
  Proof.
    unfold fresh_var.
    intros inn.
    rewrite in_of_append in inn.
    apply find_fresh_string_is_fresh in inn.
    trivial.
  Qed.

  Lemma fresh_var_fresh1 x1 pre dom :
    x1 <> fresh_var pre (x1::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

  Lemma fresh_var_fresh2 x1 x2 pre dom :
    x2 <> fresh_var pre (x1::x2::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::x2::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

   Lemma fresh_var_fresh3 x1 x2 x3 pre dom :
    x3 <> fresh_var pre (x1::x2::x3::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::x2::x3::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

  Lemma fresh_var_fresh4 x1 x2 x3 x4 pre dom :
    x4 <> fresh_var pre (x1::x2::x3::x4::dom).
  Proof.
    intro inn.
    apply (fresh_var_fresh pre (x1::x2::x3::x4::dom)).
    rewrite <- inn.
    simpl; intuition.
  Qed.

  Definition fresh_var2 pre1 pre2 (dom:list string) :=
    let fresh_var1 := fresh_var pre1 dom in
    (fresh_var1, fresh_var pre2 (fresh_var1::dom)).
  
  Lemma fresh_var2_distinct pre1 pre2 dom :
    (fst (fresh_var2 pre1 pre2 dom)) <>
    (snd (fresh_var2 pre1 pre2 dom)).
  Proof.
    unfold fresh_var2; simpl.
    apply fresh_var_fresh1.
  Qed.

  (* given a variable, gets the "base": the part before the last seperator *)
  Definition get_var_base (sep:string) (var:string)
    := match index 0 (string_reverse sep) (string_reverse var) with
         | Some n => substring 0 (String.length var - (S n)) var
         | None => var
       end.

  Lemma get_var_base_pre sep var :
    prefix (get_var_base sep var) var = true.
  Proof.
    unfold get_var_base.
    match_destr; simpl.
    - apply substring_prefix.
    - apply prefix_refl.
  Qed.

  Definition fresh_var_from sep (oldvar:string) (dom:list string) : string
    := if in_dec string_dec oldvar dom
       then fresh_var (append (get_var_base sep oldvar) sep) dom
       else oldvar.

  Lemma fresh_var_from_fresh sep oldvar (dom:list string) : 
    ~ In (fresh_var_from sep oldvar dom) dom.
  Proof.
    unfold fresh_var_from.
    match_destr.
    apply fresh_var_fresh.
  Qed.
  
  Lemma append_ass s1 s2 s3 : ((s1 ++ s2) ++ s3 = s1 ++ s2 ++ s3)%string.
  Proof.
    revert s2 s3.
    induction s1; simpl.
    - trivial.
    - intros. rewrite IHs1; trivial.
  Qed.

  (*
Eval vm_compute in 
      fresh_var_from "$"%string "cat_var$5"%string ("cat_var$0"::"i"::"cat_var$5"::"tmp1"::"tmp2"::"cat_var1"::nil)%string.
*)

End Fresh.

Ltac prove_fresh_nin
  := match goal with
     | [ |- ~ In (fresh_var ?pre ?l) _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ |- In (fresh_var ?pre ?l) _ -> False] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ |- ~ (fresh_var ?pre ?l) = _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ |-  (fresh_var ?pre ?l) <> _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ H:In (fresh_var ?pre ?l) _ |- _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     | [ H:(fresh_var ?pre ?l) = _ |- _ ] =>
       solve[generalize (fresh_var_fresh pre l); simpl; intuition]
     end.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
