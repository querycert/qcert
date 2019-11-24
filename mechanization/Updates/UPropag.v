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
Require Import RBag.
Require Import RData.
Require Import RRelation.

Require Import Permutation.
Require Import Equivalence.
Require Import Morphisms.

Section UPropag.
  Local Open Scope rbag_scope.

  (* Figure 2 in [Griffin and Libkin 95].
     Equations for change propagation. *)

  (* P1. Sigma_p(S-dS) =b Sigma_p(S) - Sigma_p(dS) *)

  Lemma maint_select_minus (s:list data) (ds:list data) (p:data -> bool):
      (filter p (s ⊖ ds)) ≅ ((filter p s) ⊖ (filter p ds)).
  Proof.
    rewrite bminus_filter; reflexivity.
  Qed.

  (* P2. Sigma_p(S+dS) =b Sigma_p(S) + Sigma_p(dS) *)

  Lemma maint_select_plus (s:list data) (ds:list data) (p:data -> bool):
      (filter p (s ⊎ ds)) = ((filter p s) ⊎ (filter p ds)).
  Proof.
    rewrite bunion_filter; reflexivity.
  Qed.

  (* P5. (S-dS)+T =b (S+T)-(dS min S) *)

  Lemma maint_union_minus_l (s t:list data) (ds:list data):
      ((s ⊖ ds) ⊎ t) ≅ ((s ⊎ t) ⊖ (ds min-b s)).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bminus_mult.
    rewrite bmin_mult.
    repeat rewrite bunion_mult.
    rewrite bminus_mult.
    generalize (mult s a).
    generalize (mult t a).
    generalize (mult ds a).
    intros.
    generalize (compare_either n n1); intro.
    elim H; intro; clear H.
    - rewrite min_l; omega.
    - rewrite min_r. omega.
      assumption.
  Qed.

  (* P5'. S+(T-dT) =b (S+T)-(dT min T) *)

  Lemma maint_union_minus_r (s t:list data) (dt:list data):
      (s ⊎ (t ⊖ dt)) ≅ ((s ⊎ t) ⊖ (dt min-b t)).
  Proof.
    intros.
    rewrite bunion_comm.
    rewrite maint_union_minus_l.
    rewrite bunion_comm.
    reflexivity.
  Qed.

  (* P6. (S+dS)+T =b (S+T)+dS *)

  Lemma maint_union_plus_l (s t:list data) (ds:list data):
    ((s ⊎ ds) ⊎ t) ≅ ((s ⊎ t) ⊎ ds).
  Proof.
    intros.
    rewrite <- bunion_assoc.
    rewrite <- bunion_assoc.
    assert ((ds ⊎ t) ≅ (t ⊎ ds)).
    rewrite bunion_comm; reflexivity.
    rewrite H; reflexivity.
  Qed.

  (* P6'. S+(T+dT) =b (S+T)+dT *)

  Lemma maint_union_plus_r (s t:list data) (dt:list data):
    (s ⊎ (t ⊎ dt)) ≅ ((s ⊎ t) ⊎ dt).
  Proof.
    intros.
    rewrite bunion_assoc; reflexivity.
  Qed.

  (* P7. (S-dS)-T =b (S-T)-dS *)

  Lemma remove_one_flip_bminus:
    forall (t s:list data), forall (a:data),
      (remove_one a s ⊖ t) = (remove_one a (s ⊖ t)).
  Proof.
    induction t.
    simpl; reflexivity.
    intros.
    simpl.
    rewrite remove_one_comm.
    rewrite IHt.
    reflexivity.
  Qed.

  Lemma maint_minus_minus_l_eq:
    forall (ds s t:list data),
      ((s ⊖ ds) ⊖ t) = ((s ⊖ t) ⊖ ds).
  Proof.
    induction ds.
    intros; simpl; reflexivity.
    intros; simpl; rewrite IHds.
    rewrite remove_one_flip_bminus; reflexivity.
  Qed.

  Lemma maint_minus_minus_l (ds s t:list data):
      ((s ⊖ ds) ⊖ t) ≅ ((s ⊖ t) ⊖ ds).
  Proof.
    intros.
    rewrite maint_minus_minus_l_eq.
    reflexivity.
  Qed.

  (* P8. S-(T-dT) =b (S-T)+((dT min T)-(T-S)) *)

  Lemma maint_minus_minus_r (dt s t:list data):
      (s ⊖ (t ⊖ dt)) ≅ ((s ⊖ t) ⊎ ((dt min-b t) ⊖ (t ⊖ s))).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bunion_mult.
    repeat rewrite bminus_mult.
    rewrite bmin_mult.
    generalize (mult s a).
    generalize (mult t a).
    generalize (mult dt a).
    intros.
    generalize (compare_either n n0); intro.
    elim H; intro; clear H.
    rewrite min_l; omega.
    rewrite min_r; omega.
  Qed.

  (* P9. (S+dS)-T =b (S-T)+(dS-(T-S)) *)

  Lemma maint_minus_plus_l (ds s t:list data):
      ((s ⊎ ds) ⊖ t) ≅ ((s ⊖ t) ⊎ (ds ⊖ (t ⊖ s))).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bunion_mult.
    repeat rewrite bminus_mult.
    rewrite bunion_mult.
    generalize (mult s a).
    generalize (mult t a).
    generalize (mult ds a).
    intros.
    omega.
  Qed.

  (* P10. S-(T+dT) =b (S-T)-dT *)

  Lemma maint_minus_plus_r (s t:list data) (dt:list data):
    (s ⊖ (t ⊎ dt)) ≅ ((s ⊖ t) ⊖ dt).
  Proof.
    intros.
    rewrite bunion_comm.
    unfold bunion.
    rewrite bminus_over_app_delta.
    reflexivity.
  Qed.
    
  (* P11. (S-dS) min T =b (S min T)-(dS-(S-T)) *)

  Lemma maint_min_minus_l (ds s t:list data):
    ((s ⊖ ds) min-b t) ≅ ((s min-b t) ⊖ (ds ⊖ (s ⊖ t))).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bmin_mult.
    repeat rewrite bminus_mult.
    rewrite bmin_mult.
    generalize (mult s a).
    generalize (mult t a).
    generalize (mult ds a).
    intros.
    assert ((n1 <= n0) \/ (n0 <= n1)).
    omega.
    elim H; intro; clear H.
    rewrite min_l;[rewrite min_l;[omega|assumption]|omega].
    generalize (compare_either (n1 - n) n0); intro.
    elim H; intro; clear H.
    rewrite min_l.
    rewrite min_r;[omega|assumption].
    assumption.
    rewrite min_r;[rewrite min_r;[omega|assumption]|assumption].
  Qed.

  (* P11'. S min (T-dT) =b (S min T)-(dT-(T-S)) *)

  Lemma maint_min_minus_r (dt s t:list data):
      (s min-b (t ⊖ dt)) ≅ ((s min-b t) ⊖ (dt ⊖ (t ⊖ s))).
  Proof.
    intros.
    rewrite bmin_comm.
    rewrite maint_min_minus_l.
    rewrite bmin_comm; reflexivity.
  Qed.

  (* P12. (S+dS) min T =b (S min T)+(dS min (T-S)) *)

  Lemma maint_min_plus_l (ds s t:list data):
      ((s ⊎ ds) min-b t) ≅ ((s min-b t) ⊎ (ds min-b (t ⊖ s))).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bmin_mult.
    repeat rewrite bunion_mult.
    repeat rewrite bmin_mult.
    rewrite bminus_mult.
    generalize (mult s a) as nS.
    generalize (mult t a) as nT.
    generalize (mult ds a) as ndS.
    intros.
    generalize (compare_either nT nS); intro; elim H; intro; clear H.
    rewrite min_r; try omega.
    rewrite min_r; try omega.
    rewrite min_r; omega.
    generalize (compare_either (ndS+nS) nT); intro; elim H; intro; clear H.
    - rewrite min_l; try assumption.
      rewrite min_l; try omega.
      rewrite min_l; omega.
    - rewrite min_r; try assumption.
      rewrite min_r; try omega.
      rewrite min_l; omega.
  Qed.

  (* P12'. S min (T+dT) =b (S min T)+(dT min (S-T)) *)

  Lemma maint_min_plus_r (dt s t:list data):
      (s min-b (t ⊎ dt)) ≅ ((s min-b t) ⊎ (dt min-b (s ⊖ t))).
  Proof.
    intros.
    rewrite bmin_comm.
    rewrite maint_min_plus_l.
    assert ((t min-b s) ≅ (s min-b t)).
    rewrite bmin_comm; reflexivity.
    rewrite H; reflexivity.
  Qed.

  (* P13. (S-dS) max T =b (S max T)-(dS min (S-T)) *)

  Lemma maint_max_minus_l (ds s t:list data):
      ((s ⊖ ds) max-b t) ≅ ((s max-b t) ⊖ (ds min-b (s ⊖ t))).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bmax_mult.
    repeat rewrite bminus_mult.
    repeat rewrite bmin_mult.
    rewrite bmax_mult.
    rewrite bminus_mult.
    generalize (mult s a) as nS.
    generalize (mult t a) as nT.
    generalize (mult ds a) as ndS.
    intros.
    generalize (compare_either nS nT); intro; elim H; intro; clear H.
    rewrite max_r; try omega.
    rewrite max_r; try assumption.
    rewrite min_r; omega.
    generalize (compare_either nS (nT+ndS)); intro; elim H; intro; clear H.
    - rewrite max_r; try omega.
      rewrite max_l; try assumption.
      rewrite min_r; try omega.
    - rewrite max_l; try omega.
      rewrite max_l; try assumption.
      rewrite min_l; omega.
  Qed.

  (* P13'. S max (T-dT) =b (S max T)-(dT min (T-S)) *)

  Lemma maint_max_minus_r (dt s t:list data):
      (s max-b (t ⊖ dt)) ≅ ((s max-b t) ⊖ (dt min-b (t ⊖ s))).
  Proof.
    intros.
    rewrite bmax_comm.
    rewrite maint_max_minus_l.
    rewrite bmax_comm; reflexivity.
  Qed.

  (* P14. (S+dS) max T =b (S max T)+(dS-(T-S)) *)

  Lemma maint_max_plus_l (ds s t:list data):
      ((s ⊎ ds) max-b t) ≅ ((s max-b t) ⊎ (ds ⊖ (t ⊖ s))).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bmax_mult.
    repeat rewrite bunion_mult.
    repeat rewrite bminus_mult.
    rewrite bmax_mult.
    generalize (mult s a) as nS.
    generalize (mult t a) as nT.
    generalize (mult ds a) as ndS.
    intros.
    generalize (compare_either nT nS); intro; elim H; intro; clear H.
    rewrite max_l; try omega.
    rewrite max_l; omega.
    generalize (compare_either (ndS+nS) nT); intro; elim H; intro; clear H.
    - rewrite max_r; try assumption.
      rewrite max_r; omega.
    - rewrite max_l; try assumption.
      rewrite max_r; omega.
  Qed.

  (* P14. (S+dS) max T =b (S max T)+(dS-(T-S)) *)

  Lemma maint_max_plus_r (dt s t:list data):
      (s max-b (t ⊎ dt)) ≅ ((s max-b t) ⊎ (dt ⊖ (s ⊖ t))).
  Proof.
    intros.
    rewrite bmax_comm.
    rewrite maint_max_plus_l.
    rewrite bmax_comm; reflexivity.
  Qed.

  (* P15. epsilon(S-dS) =b epsilon(S)-(epsilon(dS min S)-(S-dS)) *)

  Lemma maint_distinct_minus (ds:list data) (s:list data):
      (distinct-b (s ⊖ ds)) ≅ ((distinct-b s) ⊖ ((distinct-b (ds min-b s)) ⊖ (s ⊖ ds))).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    repeat rewrite bminus_mult.
    repeat rewrite bdistinct_mult.
    rewrite bmin_mult.
    rewrite bminus_mult.
    generalize (mult s a) as nS; intro.
    generalize (mult ds a) as ndS; intro.
    generalize (compare_either nS ndS); intro; elim H; intro; clear H.
    - assert (nS - ndS = 0); try omega.
      assert (min ndS nS = nS); try (apply min_r;assumption).
      rewrite H; rewrite H1; simpl.
      assert ((nS <= 1) \/ (1 <= nS)); try omega.
    - assert (min ndS nS = ndS); try (apply min_l;assumption); rewrite H.
      assert (((nS - ndS) <= 1) \/ (1 <= (nS - ndS))); try omega.
      assert ((nS <= 1) \/ (1 <= nS)); try omega.
      assert ((ndS <= 1) \/ (1 <= ndS)); try omega.

      Ltac tme := 
        (rewrite min_l by assumption; tme) ||
        (rewrite min_r by assumption; tme) ||
        omega.

      elim H1; elim H2; elim H3; intros; clear H1 H2 H3; tme.
      
  Qed.

  (* P16. epsilon(S+dS) =b epsilon(S)+(epsilon(dS)-S) *)

  Lemma maint_distinct_plus (ds:list data) (s:list data):
      (distinct-b (s ⊎ ds)) ≅ ((distinct-b s) ⊎ ((distinct-b ds) ⊖ s)).
  Proof.
    intros.
    apply bags_same_mult_has_equal; intros.
    rewrite bunion_mult.
    rewrite bdistinct_over_bunion.
    rewrite bminus_mult.
    rewrite bmax_mult.
    assert (((mult (bdistinct s) a) = 0) \/ ((mult (bdistinct s) a) = 1)).
    apply bdistinct_at_most_one.
    assert (((mult (bdistinct ds) a) = 0) \/ ((mult (bdistinct ds) a) = 1)).
    apply bdistinct_at_most_one.
    elim H; elim H0; intros; clear H H0; rewrite H1; rewrite H2.
    - auto.
    - assert (mult s a = 0).
      apply bdistinct_exactly_zero_back; assumption.
      rewrite H; auto.
    - auto.
    - assert (mult s a >= 1).
      apply bdistinct_exactly_one_back_diff.
      omega.
      revert H.
      generalize (mult s a) as ns.
      intros.
      rewrite Max.max_idempotent.
      omega.
  Qed.

  (* P18. (S - dS) x T =b (S x T) - (ds x T)*)

  Lemma product_nil_r t:
    product t nil = nil.
    induction t.
    reflexivity.
    simpl; assumption.
  Qed.

  Lemma product_nil_l t:
    product nil t = nil.
    reflexivity.
  Qed.

  Lemma product_cons_l s t a:
    product (a::s) t = map_concat a t ++ (product s t).
  Proof.
    reflexivity.
  Qed.

  Lemma app_app {A} (x y z:list A) :
    z ++ x = z ++ y -> x = y.
  Proof.
    intros; induction z.
    simpl; assumption.
    simpl in H.
    inversion H.
    apply IHz; assumption.
  Qed.

  Lemma cons_rem {A} (x y:list A) (a:A) :
    a::x = a::y -> x = y.
  Proof.
    intros.
    inversion H; reflexivity.
  Qed.

  Lemma cons_add {A} (x y:list A) (a:A) :
    x = y -> a::x = a::y.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

(*
  not sure yet how...
  Lemma ttt
        (a a0: list (string * data))
        (t t1 t2 : list (list (string * data))):
    complement equiv a a0 ->
    (map_concat a0 t ++ t1 ⊖ map_concat a t ++ t2) =
    ((map_concat a0 t ++ (t1 ⊖ (map_concat a t))) ⊖ t2).
  Proof.
    intros.
    revert t t1 t2.
    induction t; intros.
    reflexivity.
    simpl.
    elim (EquivDec.equiv_dec (recconcat a a1) (recconcat a0 a1)); intros.
    assert (a = a0).
    unfold recconcat in a2.
    unfold equiv.
    apply app_app with (z := a1).
    assumption.
    assert (equiv a a0).
    rewrite H0; reflexivity.
    congruence.
    specialize (IHt (remove_one (recconcat a a1) t1)). rewrite IHt.
    apply cons_add.

  Lemma maint_product_minus
        (s ds:list (list (string*data))) (t:list (list (string*data))):
    (product (s ⊖ ds) t) = ((product s t) ⊖ (product ds t)).
  Proof.
    revert ds s t.
    induction ds; intros.
    - reflexivity.
    - simpl.
      induction s.
      + simpl; repeat rewrite bminus_to_nil; reflexivity.
      + simpl.
        elim (EquivDec.equiv_dec a a0); intros.
        unfold equiv in a1.
        rewrite a1 in *.
        rewrite <- bminus_over_app_delta.
        rewrite bunion_bminus.
        rewrite IHds; reflexivity.
        rewrite IHds.
        simpl.


        induction t.
        simpl.
        repeat rewrite product_nil_r; reflexivity.
        simpl.
        

    ((map_concat a0 t ++ product (remove_one a s) t) ⊖ product ds t) =
    (map_concat a0 t ++ product (remove_one a s) t ⊖ product ds t).

    (map_concat a0 t ++ product s t ⊖ map_concat a t ++ product ds t) =
    ((map_concat a0 t ++ product s t) ⊖ (map_concat a t ++ product ds t)).
    
*)    

  (* P19. (S + dS) x T =b (S x T) + (ds x T) *)

  Lemma maint_product_plus
        (s ds:list (list (string*data))) (t:list (list (string*data))):
    (product (s ⊎ ds) t) = ((product s t) ⊎ (product ds t)).
  Proof.
    revert s ds t; induction ds; intros.
    - reflexivity.
    - simpl; rewrite IHds.
      unfold bunion; rewrite app_assoc; reflexivity.
  Qed.

End UPropag.

