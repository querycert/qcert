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

Require Import List.
Require Import Sumbool.

Require Import Permutation.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Peano_dec.


Ltac dest_eqdec :=
  match goal with 
  | [|- context [eq_nat_dec ?x ?y]] => destruct (eq_nat_dec x y)
  | [H: context [eq_nat_dec ?x ?y] |- _] => destruct (eq_nat_dec x y)
                                                     
  | [|- context [@equiv_dec ?a ?b ?c ?d ?x ?y]] => destruct (@equiv_dec a b c d x y)
  | [H: context [@equiv_dec ?a ?b ?c ?d ?x ?y] |- _] => destruct (@equiv_dec a b c d x y)
  end; unfold Equivalence.equiv, RelationClasses.complement in *; try subst.

Section RUtil.

  Section bools.
  
    Require Import Bool.
    Lemma andb_true_inversion:
      forall b1 b2 : bool,
        andb b1 b2 = true <-> b1 = true /\ b2 = true.
    Proof.
      split.
      - case_eq b1; case_eq b2; auto.
      - apply andb_true_intro.
    Qed.

    Lemma four_cases {A:Type} :
      forall (p1 p2: A -> bool) (a:A),
        ((((p1 a) = true) /\ ((p2 a) = true)) \/
         (((p1 a) = true) /\ ((p2 a) = false))) \/
        ((((p1 a) = false) /\ ((p2 a) = true)) \/
         (((p1 a) = false) /\ ((p2 a) = false))).
    Proof.
      intros.
      case (p1 a); case (p2 a); auto.
    Qed.

    Lemma two_cases {A:Type} :
      forall (p: A -> bool) (a:A),
        ((p a) = true) \/ ((p a) = false).
    Proof.
      intros.
      case (p a); auto.
    Qed.

    Lemma notand p q:
      ~(p \/ q) -> ~p /\ ~q.
    Proof.
      intros.
      unfold not in *.
      split; intro. elim H. left. assumption. elim H. right. assumption.
    Qed.

    Lemma eq_implies_pred {A:Type} :
      forall (p:A -> bool), forall (x1 x2:A),
          x1 = x2 -> (p x1) = (p x2).
    Proof.
      intros.
      rewrite H; reflexivity.
    Qed.
  
    Lemma not_pred_implies_neq {A:Type}:
      forall (p:A -> bool), forall (x1 x2:A),
          (p x1) <> (p x2) -> x1 <> x2.
    Proof.
      intros.
      unfold not in *; intro.
      apply H; apply eq_implies_pred; assumption.
    Qed.

  End bools.

  Section In.
    Context {A:Type}.

    Lemma In_app (x:A) (l1 l2:list A):
      In x (l1 ++ l2) -> In x l1 \/ In x l2.
    Proof.
      intros. induction l1; simpl in *.
      right; assumption.
      elim H; intros; clear H.
      left; left; assumption.
      elim (IHl1 H0); intros; clear IHl1 H0.
      left; right; assumption.
      right; assumption.
    Qed.

    Lemma In_app_comm (v:A) (l1 l2:list A) :
      In v (l1++l2) -> In v (l2++l1).
    Proof.
      apply Permutation_in.
      apply Permutation_app_comm.
    Qed.
    
    Lemma In_app_iff (v:A) (l1 l2:list A) :
      In v (l1++l2) <-> In v (l2++l1).
    Proof.
      split; apply In_app_comm.
    Qed.
    
    Lemma find_In {f l} {b:A} : find f l = Some b -> In b l.
    Proof.
      revert b; induction l; simpl; try discriminate.
      destruct (f a); auto.
      inversion 1; auto.
    Qed.

    Lemma find_correct {f l} {b:A} : find f l = Some b -> f b = true.
    Proof.
      revert b; induction l; simpl; try discriminate.
      case_eq (f a); auto.
      inversion 2; subst; auto.
    Qed.
    
    Lemma app_or_in (x:A) (l1 l2: list A) :
      In x (l1 ++ l2) -> In x l1 \/ In x l2.
    Proof.
      intros.
      induction l1.
      simpl in *; right; assumption.
      simpl in *.
      elim H; clear H; intros.
      left; left; assumption.
      elim (IHl1 H); intros.
      left; right; assumption.
      right; assumption.
    Qed.
    
    Lemma app_or_in_iff (x:A) (l1 l2: list A) :
      In x (l1 ++ l2) <-> In x l1 \/ In x l2.
    Proof.
      split.
      apply app_or_in.
      apply in_or_app.
    Qed.

    Lemma in_or_not (eqd:forall a a':A, {a=a'} + {a<>a'}) (l:list A) a:
      (In a l) \/ ~(In a l).
    Proof.
      induction l; simpl.
      right; intro; assumption.
      elim (eqd a0 a); intros.
      rewrite a1 in *; left; left; reflexivity.
      elim IHl; intros.
      - left; right; assumption.
      - right; unfold not in *; intros.
        elim H0; intro.
        elim b; assumption.
        elim H; assumption.
    Qed.

    Lemma nin_app_or (x:A) a b :
      (~ In x (a ++ b)) <-> (~ In x a /\ ~ In x b).
    Proof.
      intuition. apply in_app_or in H0; intuition.
    Qed.

    Lemma in_in_app_false {l l1 l2} :
      (forall x:A,
          In x l ->
          In x (l1 ++ l2) -> False) ->
      ((forall x,
           In x l ->
           In x l1 -> False) /\
       (forall x,
           In x l ->
           In x l2 -> False)).
    Proof.
      intros.
      split; intuition; eapply H; eauto; apply in_app_iff; auto.
    Qed.

    Lemma in_in_cons_app_false {v l l1 l2} :
      (forall x:A,
          In x l ->
          v = x \/ In x (l1 ++ l2) -> False) ->
      ((forall x,
           In x l ->
           In x (l1) -> False) /\
       (forall x,
           In x l ->
           In x (l2) -> False) /\
       ~ (In v l)).
    Proof.
      intros.
      split; intuition; try solve[eapply H; eauto; repeat rewrite in_app_iff; auto].
    Qed.

    Lemma in_in_cons_cons_app_app_false {v v0 l l1 l2 l3} :
      (forall x:A,
          In x l ->
          v = x \/ v0 = x \/ In x (l1 ++ l2 ++ l3) -> False) ->
      ((forall x,
           In x l ->
           In x l1 -> False) /\
       (forall x,
           In x l ->
           In x l2 -> False) /\
       (forall x,
           In x l ->
           In x l3 -> False) /\
       ~ (In v l) /\
       ~ (In v0 l)).
    Proof.
      intros.
      split; intuition; try solve[eapply H; eauto; repeat rewrite in_app_iff; auto].
    Qed.

  End In.
  
  Section forallt.
    Inductive Forallt {A : Type} (P : A -> Type) : list A -> Type :=
      Forallt_nil : Forallt P nil
    | Forallt_cons : forall (x : A) (l : list A),
        P x -> Forallt P l -> Forallt P (x :: l).
  
    Lemma list_Forallt_eq_dec {A:Type}:
      forall (c l: list A),
        Forallt (fun x : A => forall y : A, {x = y} + {x <> y}) c -> {c = l} + {c <> l}.
    Proof.
      intros; revert l; induction c; intros l.
      destruct l.
      - left; trivial.
      - right; inversion 1.
      - destruct l.
        + right;inversion 1.
        + inversion X; subst.
          destruct (X0 a0).
          * destruct (IHc X1 l);subst; intuition.
            right; inversion 1; auto. 
          * right; inversion 1; auto. 
    Defined.

    Lemma forallt_impl {A} {P1 P2:A->Type} {l:list A} :
      Forallt P1 l -> Forallt (fun x => P1 x -> P2 x) l -> Forallt P2 l.
    Proof.
      Hint Constructors Forallt.
      induction l; trivial.
      inversion 1; inversion 1; subst.
      auto.
    Defined.

    Lemma forallt_weaken {A} P : (forall x:A, P x) -> forall l, Forallt P l.
    Proof.
      Hint Constructors Forallt.
      intros.
      induction l. apply Forallt_nil.
      apply Forallt_cons. apply (X a).
      trivial.
    Defined.

    Lemma Forallt_inv: forall A P (a:A) l, Forallt P (a :: l) -> P a.
    Proof.
      intros; inversion X; assumption.
    Qed.
    
    Lemma Forallt_inv2: forall A P (a:A) l, Forallt P (a :: l) -> Forallt P l.
    Proof.
      intros; inversion X; assumption.
    Qed.

    Require Import RelationClasses.
    Require Import EquivDec.
    Require Import Equivalence.

    Lemma Forallt_In {A:Type} {P:A->Type} {r} {eq:EqDec A eq}: 
      Forallt P r -> forall a, In a r -> P a.
    Proof.
      induction 1; simpl; intuition.
      (* Since equality is decidable, we can "rediscover" the components of the 
      In relation (the ‌\/ lives in Prop) *)
      destruct (x==a); unfold equiv, complement in *; subst; auto.
      destruct (In_dec eq a l); unfold equiv, complement in *; subst; auto.
      assert False; intuition.
    Defined.
  
    Lemma Forall_app {A} (P:A->Prop) (l1 l2:list A):
      Forall P l1 -> Forall P l2 ->
      Forall P (l1 ++ l2).
    Proof.
      intros.
      rewrite Forall_forall in *; intros.
      assert (In x l1 \/ In x l2)
        by (apply In_app; assumption).
      elim H2; intros; clear H2.
      - apply H; assumption.
      - apply H0; assumption.
    Qed.

    Lemma Forall_map {A B} P (f:A->B) l:
      Forall P (map f l) <->
      Forall (fun x => P (f x)) l.
    Proof.
      repeat rewrite Forall_forall.
      intuition.
      - apply H.
        rewrite in_map_iff.
        eauto.
      - rewrite in_map_iff in H0.
        destruct H0 as [? [??]].
        subst.
        eauto.
    Qed.
    

    Lemma Forall_impl_in {A} {P Q : A -> Prop} {l} :
      (forall a, In a l -> P a -> Q a) ->
      Forall P l -> Forall Q l.
    Proof.
      induction l; trivial; simpl; inversion 2; subst; auto.
    Qed.
    
    (* If P is a Prop, Forallt can be expressed more simply as Forall *)
    Lemma Forallt_Forall {A:Prop} (P:A->Prop) (l:list A) :
      Forallt P l -> Forall P l.
    Proof.
      induction l; eauto.
      induction 1; eauto.
    Qed.

  End forallt.

  Section forallb.

    Lemma forallb_ext {A} f1 f2 (l:list A) :
      (forall x, In x l -> f1 x = f2 x) ->
      forallb f1 l = forallb f2 l.
    Proof.
      induction l; simpl; trivial; intros.
      rewrite IHl.
      - f_equal.
        intuition.
      - intuition.
    Qed.

    Lemma forallb_incl {A} f (l1 l2 : list A) :
      incl l1 l2 ->
      forallb f l2 = true ->
      forallb f l1 = true.
    Proof.
      unfold incl.
      repeat rewrite forallb_forall.
      intuition.
    Qed.

    Lemma forallb_app {A} (f:A->bool) l1 l2 :
      forallb f (l1 ++ l2) = true <->
      (forallb f l1 = true /\ forallb f l2 = true).
    Proof.
      repeat rewrite forallb_forall.
      intuition; rewrite in_app_iff in *; intuition.
    Qed.
    
    Lemma forallb_map {A B} f (mf:A->B) m : forallb f (map mf m) = forallb ((fun x => f (mf x))) m.
    Proof.
      induction m; simpl; auto.
      f_equal; auto.
    Qed.

    Lemma existsb_not_forallb {A} f (l:list A)
      : existsb f l = negb (forallb (fun x => negb (f x)) l).
    Proof.
      induction l; simpl; trivial.
      destruct (f a); simpl in *; intuition.
    Qed.

    Lemma forallb_not_existb {A} f (l:list A)
      : forallb f l = negb (existsb (fun x => negb (f x)) l).
    Proof.
      induction l; simpl; trivial.
      destruct (f a); simpl in *; intuition.
    Defined.

    Lemma map_eq {A B} {f g:A->B} {l} :
      Forall (fun x => f x = g x) l ->
      map f l = map g l.
    Proof.
      induction l; trivial.
      inversion 1; simpl; subst.
      f_equal; auto.
    Qed.

    Lemma map_cons {A B:Type} (f:A->B) (l:list A) (a:A) : 
      map f (a::l) = (f a)::map f l.
    Proof.
      reflexivity.
    Qed.

    Lemma map_eq_cons {A B} (f : A -> B) (l:list A) b l' :
      map f l = b::l' ->
      {a : A & {ls:list A | l = a::ls /\f a = b /\ map f ls = l'}}.
    Proof.
      destruct l; simpl; intros; try discriminate.
      inversion H; subst.
      eauto.
    Qed.

  End forallb.

  Section pairs.

    Lemma pair_eq_dec {A B:Type} (a1:A) (b1:B) (a2:A) (b2:B) :
      {a1 = a2} + {a1 <> a2} ->
      {b1 = b2} + {b1 <> b2} ->
      {(a1, b1) = (a2, b2)} + {(a1, b1) <> (a2, b2)}.
    Proof.
      destruct 1; subst.
      - destruct 1; subst; auto.
        right; inversion 1; auto.
      - right; inversion 1; auto.
    Defined.

    Require String.

    Global Instance string_eqdec : EqDec String.string eq := String.string_dec.
    Global Instance pair_eqdec {A B} `{EqDec A eq} `{EqDec B eq} : EqDec (prod A B) eq.
    Proof.
      red; intros. unfold complement, equiv. 
      destruct x; destruct y; simpl.
      apply pair_eq_dec; eauto.
    Defined.

    Global Instance option_eqdec {A:Type} `{EqDec A eq}: EqDec (option A) eq.
    Proof.
      red; unfold equiv, complement; intros x y.
      destruct x; destruct y; try intuition congruence.
      destruct (a == a0); intuition congruence.
    Defined.

  End pairs.

  Require Import Omega.
  
  Section arith.

    Lemma min_zero:
      forall (n1 n2:nat), min n1 (S n2) = 0 -> n1 = 0.
    Proof.
      intros.
      induction n1.
      reflexivity.
      assert (exists (n3:nat), min (S n1) (S n2) = (S n3)).
      exists (min n1 n2).
      rewrite Min.succ_min_distr; reflexivity.
      elim H0; intros.
      congruence.
    Qed.

    Lemma min_against_one:
      forall (n:nat), min n 1 = 0 \/ min n 1 = 1.
    Proof.
      intros.
      induction n; simpl.
      left; reflexivity.
      elim IHn; intro; clear IHn; auto with arith.
    Qed.

    Lemma compare_either (n1 n2:nat):
      (n1 <= n2) \/ (n2 <= n1).
    Proof.
      omega.
    Qed.
    
    Lemma min_one_yields_one:
      forall n:nat, min n 1 = 1 -> 1 <= n.
    Proof.
      intros.
      induction n; simpl in *.
      congruence.
      auto with arith.
    Qed.

    Lemma fold_left_arith_dist1 {A} (x0:nat) (l:list A) (f:A -> nat):
      fold_left (fun (x:nat) (y:A) => (f y) + x) l x0 =
      (fold_left (fun (x:nat) (y:A) => (f y) + x) l 0) + x0.
    Proof.
      revert x0; simpl; induction l; [reflexivity|idtac]; intros.
      simpl in *.
      rewrite (IHl (f a + 0)); simpl.
      rewrite (IHl (f a + x0)); simpl.
      omega.
    Qed.
      
    Lemma fold_left_arith_dist2 {A} (x0 n0:nat) (l:list A) (f:A -> nat):
      fold_left (fun (x:nat) (y:A) => n0 * (f y) + x) l x0 =
      n0 * (fold_left (fun (x:nat) (y:A) => (f y) + x) l 0) + x0.
    Proof.
      revert x0; induction l; simpl; intros; try omega.
      rewrite (IHl (n0 * f a + x0)); simpl.
      rewrite (fold_left_arith_dist1 (f a + 0)).
      rewrite mult_plus_distr_l.
      rewrite mult_plus_distr_l.
      omega.
    Qed.

    Lemma fold_left_arith_dist3 {A} (x0 n0:nat) (l:list A) (f:A -> nat):
      n0 * (fold_left (fun (x:nat) (y:A) => (f y) + x) l 0) + x0 =
      n0 * (fold_left (fun (x:nat) (y:A) => x + (f y)) l 0) + x0.
    Proof.
      generalize 0.
      revert x0; induction l; simpl; intros; try omega.
      assert (f a + n = n + f a) by apply plus_comm.
      rewrite H; clear H.
      rewrite (IHl x0 (n + f a)); reflexivity.
    Qed.

    Lemma fold_left_arith_dist4 {A} (x0 n0:nat) (l:list A) (f:A -> nat):
      fold_left (fun (x:nat) (y:A) => n0 * (f y) + x) l x0 =
      n0 * (fold_left (fun (x:nat) (y:A) => x + (f y)) l 0) + x0.
    Proof.
      rewrite <- fold_left_arith_dist3.
      apply fold_left_arith_dist2.
    Qed.

  End arith.

  Section Zutil.
    Require Import ZArith Zdigits Znat.
    Open Scope Z_scope.
  
    Definition ZToSignedNat (z:Z) : (bool*nat) :=
      match (Z.sgn z) with
      | -1 => (false,(Z.to_nat z))
      | _ => (true, (Z.to_nat z))
      end.
  
    Lemma pos_succ_inv (n1 n2:positive):
      (Pos.succ n1 = Pos.succ n2 -> n1 = n2).
    Proof.
      intros.
      apply Pos.succ_inj.
      assumption.
    Qed.
  
    Lemma Pos_of_nat_inv (n1 n2:nat) :
      Pos.of_nat (S n1) = Pos.of_nat (S n2) -> n1 = n2.
    Proof.
      intros.
      simpl in H; repeat rewrite of_nat_succ in H.
      revert n2 H; induction n1; intros.
      destruct n2; try congruence.
      simpl in H.
      induction n2.
      simpl in H; congruence.
      simpl in *.
      assert False.
      generalize Pos.succ_not_1; intros.
      unfold not in H0.
      apply (H0 (Pos.succ
                   match n2 with
                   | 0%nat => 1
                   | S _ => Pos.succ (Pos.of_nat n2)
                   end)). rewrite <- H; reflexivity.
      contradiction.
      simpl in H.
      specialize (IHn1 (pred n2)).
      destruct n2; simpl in *.
      destruct n1; try congruence.
      simpl in H. congruence.
      simpl in H.
      assert False.
      generalize Pos.succ_not_1; intros.
      unfold not in H0.
      apply (H0 (Pos.succ
                   match n1 with
                   | 0%nat => 1
                   | S _ => Pos.succ (Pos.of_nat n1)
                   end)). rewrite H; reflexivity.
      contradiction.
      apply f_equal.
      apply IHn1.
      apply pos_succ_inv; assumption.
    Qed.
  
    Lemma of_nat_inv (n1 n2:nat) :
      Z.of_nat n1 = Z.of_nat n2 -> n1 = n2.
    Proof.
      intros.
      unfold Z.of_nat in H.
      destruct n1; destruct n2; try congruence.
      inversion H.
      rewrite Pos.of_nat_succ in H1.
      rewrite Pos.of_nat_succ in H1.
      inversion H1.
      rewrite (Pos_of_nat_inv n1 n2 H1); reflexivity.
    Qed.
  
    Lemma pos_succ_nat_inv (n1 n2:nat) :
      Pos.of_succ_nat n1 = Pos.of_succ_nat n2 -> n1 = n2.
    Proof.
      intros.
      repeat rewrite Pos.of_nat_succ in H.
      apply Pos_of_nat_inv; assumption.
    Qed.

  End Zutil.

  Section vm.
    Definition is_true {A B} (x:{A}+{B}) : bool :=
      Eval vm_compute in (if x then true else false).

    Definition holds {A B} (x:{A}+{B}) : Prop :=
      is_true x = true.
  End vm.

End RUtil.

Require String.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* Some generic tactics from Avi *)

(* Fails when a specific hypothesis is present *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.

Ltac extend P :=
  let t := type of P in
  notHyp t; generalize P; intro.

Ltac match_destr
  := match goal with [|- context [match ?x with _ => _ end]] => destruct x end; trivial; try discriminate.

Ltac match_destr_in H
  := match type of H with context [match ?x with _ => _ end] => destruct x end; trivial; try discriminate.

Ltac match_case
  := match goal with [|- context [match ?x with _ => _ end]] => case_eq x end; trivial; try discriminate.

Ltac match_case_in H
  := match type of H with context [match ?x with _ => _ end] => case_eq x end; trivial; try discriminate.


Ltac cut_to H :=
  match type of H with
    | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
    | _ -> ?b => cut (b); [clear H; intros H|apply H]
  end.

Ltac invcs H := inversion H; clear H; try subst.

Require Import String.
Definition brand := string.

(* If there is a default way to convert a type to a string.
    This is particularly useful for debugging *)
Class ToString (A:Type)
  := {
      toString (a:A) : string
      }.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
