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
Require Import Bool.
Require Import List.
Require Import Permutation.
Require Import Morphisms.
Require Import RelationClasses.
Require Import EquivDec.
Require Import Utils.
Require Import ForeignType.
Require Import RType.
Require Import BrandRelation.

Section RTypeMeetJoin.

(* the rtype_join of two records is Closed iff the records are both closed 
   and have the same domain *)
Definition record_kind_rtype_join {B} (k₁ k₂:record_kind) (l₁ l₂:list (string * B))
  := match k₁, k₂ with
       | Closed, Closed =>
         if (domain l₁) == (domain l₂) then Closed else Open
       | _, _ => Open
     end.

Lemma record_kind_rtype_join_open_l {B} k l₁ l₂:
  @record_kind_rtype_join B Open k l₁ l₂ = Open.
Proof.
  destruct k; simpl; trivial.
Qed.

Lemma record_kind_rtype_join_open_r {B} k l₁ l₂:
  @record_kind_rtype_join B k Open l₁ l₂ = Open.
Proof.
  destruct k; simpl; trivial.
Qed.

Lemma record_kind_rtype_join_closed_inv {B} k₁ k₂ l₁ l₂:
  @record_kind_rtype_join B k₁ k₂ l₁ l₂ = Closed ->
  k₁ = Closed /\ k₂ = Closed /\ domain l₁ = domain l₂.
Proof.
  destruct k₁; destruct k₂; simpl; intros; try discriminate.
  destruct (equiv_dec (domain l₁) (domain l₂)); intuition congruence.
Qed.

Lemma record_kind_rtype_join_idempotent {B} k l :
  @record_kind_rtype_join B k k l l = k.
Proof.
  destruct k; simpl; trivial.
  destruct ((domain l) == (domain l));
    congruence.
Qed.

Lemma record_kind_rtype_join_comm_kind {B} k₁ k₂ l₁ l₂ :
  @record_kind_rtype_join B k₁ k₂ l₁ l₂ =
  record_kind_rtype_join k₂ k₁ l₁ l₂.
Proof.
  destruct k₁; destruct k₂; simpl; trivial.
Qed.

Lemma record_kind_rtype_join_comm_list {B} k₁ k₂ l₁ l₂ :
  @record_kind_rtype_join B k₁ k₂ l₁ l₂ =
  record_kind_rtype_join k₁ k₂ l₂ l₁.
Proof.
  destruct k₁; destruct k₂; simpl; trivial.
  destruct ((domain l₁) == (domain l₂));
    destruct ((domain l₂) == (domain l₁));
      trivial; congruence.
Qed.

Lemma record_kind_rtype_join_comm {B} k₁ k₂ l₁ l₂ :
  @record_kind_rtype_join B k₁ k₂ l₁ l₂ =
  record_kind_rtype_join k₂ k₁ l₂ l₁.
Proof.
  rewrite record_kind_rtype_join_comm_kind;
  rewrite record_kind_rtype_join_comm_list;
  trivial.  
Qed.


Definition rtype_meet_compatible_records {A B} (k₁ k₂:record_kind)
             (l₁:list (string*A)) (l₂:list (string * B)) : Prop
    := match k₁, k₂ with
       | Open, Open => True
       | Open, Closed => sublist (domain l₁) (domain l₂)
       | Closed, Open => sublist (domain l₂) (domain l₁)
       | Closed, Closed => (domain l₂) = (domain l₁) 
     end.

Lemma rtype_meet_compatible_records_dec {A B} (k₁ k₂:record_kind)
        (l₁:list (string*A)) (l₂:list (string * B)) :
    {rtype_meet_compatible_records k₁ k₂ l₁ l₂}  + {~ rtype_meet_compatible_records k₁ k₂ l₁ l₂}.
Proof.
  destruct k₁; destruct k₂.
  - left; simpl; trivial.
  - destruct (sublist_dec (domain l₁) (domain l₂)).
    + left; simpl; trivial.
    + right; simpl; trivial.
  - destruct (sublist_dec (domain l₂) (domain l₁)).
    + left; simpl; trivial.
    + right; simpl; trivial.
  - destruct (sublist_dec (domain l₁) (domain l₂)).
    + destruct (sublist_dec (domain l₂) (domain l₁)).
       * left; simpl; trivial. apply sublist_antisymm; trivial.
       * right; simpl. congruence.
    + right; simpl. intro eqq; apply n; rewrite eqq. reflexivity.
Defined.
    
  (* the join of two records is Closed iff the records are both closed 
   and have the same domain *)
Definition record_kind_rtype_meet (k₁ k₂:record_kind) 
  := match k₁, k₂ with
       | Open, Open => Open
       | _, _ => Closed
     end.

Lemma rtype_meet_compatible_records_idempotent {B} k₁ k₂ r :
  @rtype_meet_compatible_records B B k₁ k₂ r r.
Proof.
  destruct k₁; destruct k₂; simpl; trivial; reflexivity.
Qed.

Lemma record_kind_rtype_meet_idempotent k : record_kind_rtype_meet k k = k.
Proof.
  destruct k; reflexivity.
Qed.

Lemma rtype_meet_compatible_records_commutative {A B} k₁ k₂ r₁ r₂:
  @rtype_meet_compatible_records A B k₁ k₂ r₁ r₂ ->
  @rtype_meet_compatible_records B A k₂ k₁ r₂ r₁.
Proof.
  destruct k₁; destruct k₂; simpl; intuition.
Qed.

Lemma record_kind_rtype_meet_commutative k₁ k₂ : record_kind_rtype_meet k₁ k₂ = record_kind_rtype_meet k₂ k₁.
Proof.
  destruct k₁; destruct k₂; simpl; trivial.
Qed.

Lemma rtype_meet_compatible_records_domain_eq_l {A B C}
      (k₁ k₂:record_kind) (l₁:list (string*A)) (l₁':list (string*B)) (l₂:list (string * C))  :
  domain l₁ = domain l₁' ->
  rtype_meet_compatible_records k₁ k₂ l₁ l₂
  =  rtype_meet_compatible_records k₁ k₂ l₁' l₂.
Proof.
  destruct k₁; destruct k₂; simpl; intros; congruence.
Qed.

Lemma rtype_meet_compatible_records_domain_eq_r {A B C}
      (k₁ k₂:record_kind) (l₁:list (string*A)) (l₂:list (string*B)) (l₂':list (string * C))  :
  domain l₂ = domain l₂' ->
  rtype_meet_compatible_records k₁ k₂ l₁ l₂
  =  rtype_meet_compatible_records k₁ k₂ l₁ l₂'.
Proof.
  destruct k₁; destruct k₂; simpl; intros; congruence.
Qed.


Lemma record_kind_rtype_meet_associative k k0 k1 :
  record_kind_rtype_meet (record_kind_rtype_meet k k0) k1
  = record_kind_rtype_meet k (record_kind_rtype_meet k0 k1).
Proof.
  destruct k; destruct k0; destruct k1; simpl; trivial.
Qed.

Section mj.
  Context {ftype:foreign_type}.
  Context {br:brand_relation}.

  Fixpoint rtype_join₀  (τ₁ τ₂:rtype₀) : rtype₀ 
  := match τ₁, τ₂ with
       | ⊥₀, τ => τ
       | τ, ⊥₀ => τ
       | Unit₀, Unit₀ => Unit₀
       | Nat₀, Nat₀ => Nat₀
       | Float₀, Float₀ => Float₀
       | Bool₀, Bool₀ => Bool₀
       | String₀, String₀ => String₀
       | Coll₀ τ₁', Coll₀ τ₂' => Coll₀ (rtype_join₀ τ₁' τ₂')
       | Rec₀ k₁ srl, Rec₀ k₂ srl' => Rec₀ (record_kind_rtype_join k₁ k₂ srl srl')
                                ((fix map_rtype_join₀ l1 l2 :=
                                match l1 with
                                  | nil => nil
                                  | (s,r)::srs => match lookup string_dec l2 s with
                                                      | None => map_rtype_join₀ srs l2
                                                      | Some r' => (s,rtype_join₀ r r')::(map_rtype_join₀ srs l2)
                                                  end
                                end) srl srl')
       | Either₀ τl₁ τr₁, Either₀ τl₂ τr₂ => Either₀ (rtype_join₀ τl₁ τl₂) (rtype_join₀ τr₁ τr₂)
       | Arrow₀ τl₁ τr₁, Arrow₀ τl₂ τr₂ => Arrow₀ (rtype_meet₀ τl₁ τl₂) (rtype_join₀ τr₁ τr₂)
       | Brand₀ b₁, Brand₀ b₂ => Brand₀ (brand_join brand_relation_brands b₁ b₂)
       | Foreign₀ ft₁, Foreign₀ ft₂ => Foreign₀ (join ft₁ ft₂)
       | _, _ => ⊤₀
     end
  with rtype_meet₀ (τ₁ τ₂:rtype₀) : rtype₀ 
  := match τ₁, τ₂ with
       | ⊤₀, τ => τ
       | τ, ⊤₀ => τ
       | Unit₀, Unit₀ => Unit₀
       | Nat₀, Nat₀ => Nat₀
       | Float₀, Float₀ => Float₀
       | Bool₀, Bool₀ => Bool₀
       | String₀, String₀ => String₀
       | Coll₀ τ₁', Coll₀ τ₂' => Coll₀ (rtype_meet₀ τ₁' τ₂')
       | Rec₀ k₁ srl, Rec₀ k₂ srl' =>
         if rtype_meet_compatible_records_dec k₁ k₂ srl srl'
         then Rec₀ (record_kind_rtype_meet k₁ k₂)
                  (rec_concat_sort ((fix map_rtype_meet₀ l1 l2 :=
                     match l1 with
                       | nil => nil
                       | (s,r)::srs => match lookup string_dec l2 s with
                                         | None => (s,r)::map_rtype_meet₀ srs l2
                                         | Some r' => (s,rtype_meet₀ r r')::(map_rtype_meet₀ srs l2)
                                       end
                     end) srl srl')
                                   (lookup_diff string_dec srl' srl))
         else ⊥₀
       | Either₀ τl₁ τr₁, Either₀ τl₂ τr₂ =>
         Either₀ (rtype_meet₀ τl₁ τl₂) (rtype_meet₀ τr₁ τr₂)
       | Arrow₀ τl₁ τr₁, Arrow₀ τl₂ τr₂ => Arrow₀ (rtype_join₀ τl₁ τl₂) (rtype_meet₀ τr₁ τr₂)
       | Brand₀ τ₁, Brand₀ τ₂ => Brand₀ (brand_meet brand_relation_brands τ₁ τ₂)
       | Foreign₀ ft₁, Foreign₀ ft₂ => Foreign₀ (meet ft₁ ft₂)
       | _, _ => ⊥₀
     end.

Lemma map_rtype_join₀_domain_subset r srl x:
  In x (domain (((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s0, r1) :: srs =>
               match lookup string_dec l2 s0 with
               | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) r srl))) -> In x (domain r) /\ In x (domain srl).
Proof.
  induction r; simpl; [intuition|].
  destruct a; simpl.
  case_eq (lookup string_dec srl s); [intros t teq|intuition].
  simpl. intuition; subst.
  eapply in_dom. apply (lookup_in string_dec); eauto.
Qed.

Lemma map_rtype_join₀_domain_subset_inv r srl x:
 In x (domain r) /\ In x (domain srl) ->
  In x (domain (((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s0, r1) :: srs =>
               match lookup string_dec l2 s0 with
               | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) r srl))).
Proof.
  revert srl.
  induction r; simpl; [intuition|].
  destruct a; simpl; intros.
  case_eq (lookup string_dec srl s); [intros t teq|intros neq].
  - intuition; subst; simpl; intuition.
  - intuition; subst. apply lookup_none_nin in neq. intuition.
Qed.

Lemma map_rtype_join₀_rtype_joins {r₁ r₂ s τ₁ τ₂} :
  lookup string_dec r₁ s = Some τ₁ ->
    lookup string_dec r₂ s = Some τ₂ ->
    lookup string_dec (((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
                | None => map_rtype_join₀ srs l2
                end
            end) r₁ r₂)) s = Some (rtype_join₀ τ₁ τ₂).
Proof.
  induction r₁; simpl; auto; inversion 1; subst.
  destruct a; simpl.
  destruct (string_dec s s0); intros lr2.
  - subst. inversion H; subst.
    rewrite lr2. simpl.
    destruct (string_dec s0 s0); congruence.
  - specialize (IHr₁ H lr2).
    destruct (lookup string_dec r₂ s0); simpl; auto.
    destruct (string_dec s s0); congruence.
Qed.

Lemma NoDup_map_rtype_join₀ {r₁ r₂} :
      NoDup (domain r₁) -> NoDup (domain
      ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
          list (string * rtype₀) :=
          match l1 with
          | nil => nil
          | (s0, r1) :: srs =>
              match lookup string_dec l2 s0 with
              | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
              | None => map_rtype_join₀ srs l2
              end
          end) r₁ r₂)).
Proof.
  induction r₁; simpl; auto.
  inversion 1; subst.
  destruct a; simpl.
  case_eq (lookup string_dec r₂ s); [intros t teq|intuition].
  simpl in *. intuition; subst.
  constructor; intuition.
  apply map_rtype_join₀_domain_subset in H1.
  intuition.
Qed.

Lemma map_rtype_meet₀_domain r srl:
  (domain (((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s,r)::srs => match lookup string_dec l2 s with
                             | None => (s,r)::map_rtype_meet₀ srs l2
                             | Some r' => (s,rtype_meet₀ r r')::(map_rtype_meet₀ srs l2)
                           end
           end)
             r srl))) = domain r.
Proof.
  induction r; simpl; [intuition|].
  destruct a; simpl.
  case_eq (lookup string_dec srl s); [intros t teq|intuition]; simpl;
  rewrite IHr; trivial.
Qed.

Lemma map_rtype_meet₀_rtype_meets {r₁ r₂ s τ₁ τ₂} :
  lookup string_dec r₁ s = Some τ₁ ->
    lookup string_dec r₂ s = Some τ₂ ->
    lookup string_dec (((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_meet₀ r r') :: map_rtype_meet₀ srs l2
                | None => (s, r)::map_rtype_meet₀ srs l2
                end
            end) r₁ r₂)) s = Some (rtype_meet₀ τ₁ τ₂).
Proof.
  induction r₁; simpl; auto; inversion 1; subst.
  destruct a; simpl.
  destruct (string_dec s s0); intros lr2.
  - subst. inversion H; subst.
    rewrite lr2. simpl.
    destruct (string_dec s0 s0); congruence.
  - specialize (IHr₁ H lr2).
    destruct (lookup string_dec r₂ s0); simpl; auto.
    destruct (string_dec s s0); congruence.
    match_destr; congruence.
Qed.

Lemma map_rtype_meet₀_some_none {r₁ r₂ s τ₁} :
  lookup string_dec r₁ s = Some τ₁ ->
    lookup string_dec r₂ s = None ->
    lookup string_dec (((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_meet₀ r r') :: map_rtype_meet₀ srs l2
                | None => (s, r)::map_rtype_meet₀ srs l2
                end
            end) r₁ r₂)) s = Some τ₁.
Proof.
  induction r₁; simpl; auto; inversion 1; subst.
  destruct a; simpl.
  destruct (string_dec s s0); intros lr2.
  - subst. inversion H; subst.
    rewrite lr2. simpl.
    destruct (string_dec s0 s0); congruence.
  - specialize (IHr₁ H lr2).
    destruct (lookup string_dec r₂ s0); simpl; auto.
    destruct (string_dec s s0); congruence.
    match_destr; congruence.
Qed.

Lemma map_rtype_meet₀_none {r₁ r₂ s} :
  lookup string_dec r₁ s = None ->
    lookup string_dec (((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_meet₀ r r') :: map_rtype_meet₀ srs l2
                | None => (s, r)::map_rtype_meet₀ srs l2
                end
            end) r₁ r₂)) s = None.
Proof.
  intros.
  apply lookup_nin_none.
  rewrite map_rtype_meet₀_domain.
  apply lookup_none_nin in H.
  trivial.
Qed.
  
Ltac perm_tac := 
        try match goal with
          | [H1:In ?x ?l, H3:Permutation ?l2 ?l |- _ ] =>
            extend (Permutation_in _ (symmetry H3) H1)
          | [H1:In ?x ?l, H3:Permutation ?l ?l2 |- _ ] =>
            extend (Permutation_in _ H3 H1)
            end.

Lemma map_rtype_meet₀_disjoint r₁ r₂ :
  disjoint (domain ((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
          list (string * rtype₀) :=
          match l1 with
          | nil => nil
          | (s,r)::srs => match lookup string_dec l2 s with
                            | None => (s,r)::map_rtype_meet₀ srs l2
                            | Some r' => (s,rtype_meet₀ r r')::(map_rtype_meet₀ srs l2)
                          end
          end) r₁ r₂)) (domain (lookup_diff string_dec r₂ r₁)).
Proof.
  rewrite map_rtype_meet₀_domain.
  symmetry.
  apply lookup_diff_disjoint.
Qed.  

Lemma NoDup_map_rtype_meet₀_lookup_diff {r₁ r₂} :
      NoDup (domain r₁) ->  
      NoDup (domain r₂) ->
      NoDup (domain
               (((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
          list (string * rtype₀) :=
          match l1 with
          | nil => nil
          | (s,r)::srs => match lookup string_dec l2 s with
                             | None => (s,r)::map_rtype_meet₀ srs l2
                             | Some r' => (s,rtype_meet₀ r r')::(map_rtype_meet₀ srs l2)
                           end
          end) r₁ r₂) ++ (lookup_diff string_dec r₂ r₁))).
Proof.
  intros.
  rewrite domain_app, map_rtype_meet₀_domain.
  apply NoDup_app; auto.
  - symmetry; apply lookup_diff_disjoint.
  - apply NoDup_lookup_diff; auto.
Qed.

Lemma map_rtype_meet₀_cons2_nin a b l1 l2 :
                  ~ In a (domain l1) ->
                  ((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
         list (string * rtype₀) :=
         match l1 with
         | nil => nil
         | (s, r2) :: srs =>
             match lookup string_dec l2 s with
             | Some r' => (s, rtype_meet₀ r2 r') :: map_rtype_meet₀ srs l2
             | None => (s, r2) :: map_rtype_meet₀ srs l2
             end
         end) l1 ((a,b) :: l2))
                     =
                  ((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
             list (string * rtype₀) :=
             match l1 with
             | nil => nil
             | (s, r) :: srs =>
                 match lookup string_dec l2 s with
                 | Some r' => (s, rtype_meet₀ r r') :: map_rtype_meet₀ srs l2
                 | None => (s, r) :: map_rtype_meet₀ srs l2
                 end
             end) l1 l2).
Proof.
  revert l2.
  induction l1; simpl; trivial; intuition; simpl in *.
  destruct (string_dec a1 a); try congruence.
  rewrite IHl1; trivial.
Qed.  

Lemma rtype_join₀_meet₀_wf {τ₁ τ₂} :
  wf_rtype₀ τ₁ = true ->
  wf_rtype₀ τ₂ = true ->
  wf_rtype₀ (rtype_join₀ τ₁ τ₂) = true
/\ wf_rtype₀ (rtype_meet₀ τ₁ τ₂) = true.
Proof.
  revert τ₂.
  induction τ₁; destruct τ₂; simpl; try tauto.
  - eauto.
  - repeat rewrite andb_true_iff in *. intuition.
    + clear H H3 H4.
    induction r; simpl; trivial.
    destruct a; simpl.
    rewrite domain_cons, is_list_sorted_cons in H2. 
    intuition; simpl in *.
    case_eq (lookup string_dec srl s); [intros t teq|intros neq]; auto.
    rewrite domain_cons, is_list_sorted_cons; intuition.
    simpl.
    generalize (map_rtype_join₀_domain_subset r srl).
    destruct (domain
       ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s0, r1) :: srs =>
               match lookup string_dec l2 s0 with
               | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) r srl)); simpl; trivial.
    intros iin.
    specialize (iin s0); intuition.
    destruct (domain r); intuition.
    rewrite is_list_sorted_Sorted_iff in H.
    apply (Sorted_cons (a:=s)) in H; eauto.
    apply Sorted_StronglySorted in H; [|red;intros;etransitivity;eauto].
    eapply StronglySorted_cons_in; eauto.
  + rewrite forallb_forall.
    intros.
    destruct x; simpl in *.
    assert (indprem:In s (domain
             ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
                 list (string * rtype₀) :=
                 match l1 with
                 | nil => nil
                 | (s0, r1) :: srs =>
                     match lookup string_dec l2 s0 with
                     | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
                     | None => map_rtype_join₀ srs l2
                     end
                 end) r srl))) by (eapply in_dom; eauto).
    generalize (map_rtype_join₀_domain_subset r srl s indprem).
    destruct 1 as [indr indsrl].
    rewrite forallb_forall in H3,H4.
    apply (in_dom_lookup string_dec) in indr; destruct indr as [rx indr].
    apply (in_dom_lookup string_dec) in indsrl; destruct indsrl as [srlx indsrl].
      apply (in_lookup_nodup string_dec) in H1.
    * rewrite (map_rtype_join₀_rtype_joins indr indsrl) in H1.
      inversion H1; clear H1; subst.
      specialize (H3 _ (lookup_in string_dec _ indr)).
      specialize (H4 _ (lookup_in string_dec _ indsrl)).
      simpl in *.
      revert indr H3 H4 H; clear.
      induction r; simpl; intuition; try discriminate.
      destruct a; inversion H; subst.
      destruct (string_dec s s0); subst; simpl in *; auto.
      inversion indr; subst.
      apply H2; trivial.
    * apply NoDup_map_rtype_join₀. 
      apply (is_list_sorted_NoDup ODT_lt_dec); trivial.
  + match_destr. simpl; rewrite andb_true_iff.
    * revert k0 srl H0 H2 H3 H4 r0.
      { induction r.
        - intros; simpl.
          rewrite (@drec_concat_sort_sorted _ ODT_string).
          unfold rec_concat_sort.
          repeat rewrite lookup_diff_nilr.
          split; trivial.
          apply forallb_rec_sort; trivial.
        - destruct a.
          intros k0 srl srl_sort sr_sort fasr fasrl compat.
          simpl.
          rewrite (@drec_concat_sort_sorted _ ODT_string); simpl.
          simpl in fasr.
          rewrite andb_true_iff in fasr.
          destruct fasr as [wfr0 far].
          inversion H; clear H; subst.
          specialize (IHr H3).
          clear H3.
          split; trivial.
          apply forallb_rec_sort.
          rewrite forallb_app. split.
          + { match_case; intros.

              + simpl. rewrite andb_true_iff; trivial. split.
                { apply H2; simpl; trivial.
                  rewrite forallb_forall in fasrl.
                  apply (fasrl (s,r1)).
                  eapply lookup_in; eauto.
                }

      assert(sortr:is_list_sorted ODT_lt_dec (domain r) = true)
            by (eapply is_list_sorted_cons_inv; eauto).
      { destruct k; simpl in IHr, compat.
        - specialize (IHr Open srl); simpl in IHr.
          destruct IHr as [rs rwf]; trivial.
          unfold rec_concat_sort in rwf.
          apply forallb_rec_sort_inv in rwf.
          + rewrite forallb_app in rwf; intuition.
          + apply NoDup_map_rtype_meet₀_lookup_diff; eauto.
        - destruct k0; simpl in IHr, compat. 
          + inversion compat; subst.
            * destruct srl; simpl in H0; inversion H0.
              destruct p; subst. simpl in H.
              match_destr_in H; try congruence.
              inversion H; clear e H H0; subst.
              assert(srlsort:is_list_sorted ODT_lt_dec (domain srl) = true)
                by (eapply is_list_sorted_cons_inv; eauto).
              simpl in fasrl. rewrite andb_true_iff in fasrl.
              destruct fasrl.
              destruct (IHr Open srl); trivial.
              { unfold rec_concat_sort in H4.
                apply forallb_rec_sort_inv in H4.
                - rewrite forallb_app in H4; intuition.
                  rewrite map_rtype_meet₀_cons2_nin; trivial.
                  apply is_list_sorted_NoDup in sr_sort;
                    [ | eapply StringOrder.lt_strorder ].
                  simpl in sr_sort. inversion sr_sort; subst.
                  trivial.
                - apply NoDup_map_rtype_meet₀_lookup_diff; eauto.
              }
            * destruct (IHr Open srl); trivial.
              { unfold rec_concat_sort in H1.
                apply forallb_rec_sort_inv in H1.
                - rewrite forallb_app in H1; intuition.
                - apply NoDup_map_rtype_meet₀_lookup_diff; eauto.
              }
          + destruct srl; simpl in compat; inversion compat.
            destruct p; subst. simpl in H.
            match_destr_in H; try congruence.
            inversion H; subst. clear H e.
                          assert(srlsort:is_list_sorted ODT_lt_dec (domain srl) = true)
                by (eapply is_list_sorted_cons_inv; eauto).
              simpl in fasrl. rewrite andb_true_iff in fasrl.
              destruct fasrl.
            destruct (IHr Closed srl); simpl in IHr; trivial.
             { unfold rec_concat_sort in H4.
                apply forallb_rec_sort_inv in H4.
                - rewrite forallb_app in H4; intuition.
                  rewrite map_rtype_meet₀_cons2_nin; trivial.
                  apply is_list_sorted_NoDup in sr_sort;
                    [ | eapply StringOrder.lt_strorder ].
                  simpl in sr_sort. inversion sr_sort; subst.
                  trivial.
                - apply NoDup_map_rtype_meet₀_lookup_diff; eauto.
              }
      }
    + simpl; rewrite wfr0; simpl.
      assert(sortr:is_list_sorted ODT_lt_dec (domain r) = true)
        by (eapply is_list_sorted_cons_inv; eauto).
      { destruct k; simpl in IHr, compat.
        - specialize (IHr Open srl); simpl in IHr.
          destruct IHr as [rs rwf]; trivial.
          unfold rec_concat_sort in rwf.
          apply forallb_rec_sort_inv in rwf.
          + rewrite forallb_app in rwf; intuition.
          + apply NoDup_map_rtype_meet₀_lookup_diff; eauto.
        - destruct k0; simpl in IHr, compat. 
          + inversion compat; subst.
            * destruct srl; simpl in H0; inversion H0.
              destruct p; subst. simpl in H.
              match_destr_in H; try congruence.
            * destruct (IHr Open srl); trivial.
              { unfold rec_concat_sort in H1.
                apply forallb_rec_sort_inv in H1.
                - rewrite forallb_app in H1; intuition.
                - apply NoDup_map_rtype_meet₀_lookup_diff; eauto.
              }
          + assert (ins:In s (s::domain r)) by (simpl; intuition).
             rewrite <- compat in ins.
             apply lookup_none_nin in H.
             intuition.
      }
     }
   + rewrite forallb_forall in *.
     intros ? inn.
     apply lookup_diff_inv in inn.
     destruct inn as [inn _ ].
     eauto.
      }
  - repeat rewrite andb_true_iff in *; intuition;
    solve [apply IHτ₁1; trivial] || solve[apply IHτ₁2; trivial].
  - repeat rewrite andb_true_iff in *; intuition;
    solve [apply IHτ₁1; trivial] || solve[apply IHτ₁2; trivial].
  - repeat match_destr.
    + tauto.
    + elim n. apply brand_meet_is_canon.
    + elim n. apply brand_join_is_canon.
    + elim n. apply brand_join_is_canon.
Qed.

Corollary rtype_join₀_wf {τ₁ τ₂} :
  wf_rtype₀ τ₁ = true ->
  wf_rtype₀ τ₂ = true ->
  wf_rtype₀ (rtype_join₀ τ₁ τ₂) = true.
Proof.
  intros.
  apply rtype_join₀_meet₀_wf; trivial.
Qed.

Corollary rtype_meet₀_wf {τ₁ τ₂} :
  wf_rtype₀ τ₁ = true ->
  wf_rtype₀ τ₂ = true ->
  wf_rtype₀ (rtype_meet₀ τ₁ τ₂) = true.
Proof.
  intros.
  apply rtype_join₀_meet₀_wf; trivial.
Qed.

(** This definition does not reduce well.  To reduce with it,
    use autorewrite using rtype_join. *)
Program Definition rtype_join (τ₁ τ₂:rtype) : rtype 
  := exist _ (rtype_join₀ τ₁ τ₂) (rtype_join₀_wf (proj2_sig τ₁) (proj2_sig τ₂)).

Program Definition rtype_meet (τ₁ τ₂:rtype) : rtype 
  := exist _ (rtype_meet₀ τ₁ τ₂) (rtype_meet₀_wf (proj2_sig τ₁) (proj2_sig τ₂)).

Lemma map_rtype_join₀_lookup_none1 {l₁ l₂ s r} :
lookup string_dec l₂ s = None ->
(fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
          | None => map_rtype_join₀ srs l2
          end
      end) ((s, r)::l₁) l₂ =
(fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
          | None => map_rtype_join₀ srs l2
          end
      end) l₁ l₂.
Proof.
  simpl; intros nin.
  rewrite nin; trivial.
Qed.

Lemma map_rtype_join₀_lookup_none2 {l₁ l₂ s r} :
lookup string_dec l₁ s = None ->
(fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
          | None => map_rtype_join₀ srs l2
          end
      end) l₁ ((s, r) :: l₂) =
(fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
          | None => map_rtype_join₀ srs l2
          end
      end) l₁ l₂.
Proof.
  induction l₁; trivial; intros nin.
  destruct a; simpl in *.
    case_eq (string_dec s s0);
      [intros t teq; rewrite teq in nin; discriminate
       |intros neq neqpf].
    rewrite neqpf in nin.
    case_eq (string_dec s0 s); [intros; subst; intuition|intros neq2 ?].
    repeat rewrite (IHl₁ nin); trivial.
Qed.

Lemma map_rtype_join₀_lookup_some2 {l₁ l₂ s τ₁ τ₂} :
  lookup string_dec l₁ s = Some τ₁ ->
  is_list_sorted ODT_lt_dec (domain l₁) = true ->
  is_list_sorted ODT_lt_dec (domain ((s,τ₂)::l₂)) = true ->
   (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
          | None => map_rtype_join₀ srs l2
          end
      end) l₁ ((s, τ₂) :: l₂) =
 (s, rtype_join₀ τ₁ τ₂)
   :: (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
         list (string * rtype₀) :=
         match l1 with
         | nil => nil
         | (s0, r1) :: srs =>
             match lookup string_dec l2 s0 with
             | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
             | None => map_rtype_join₀ srs l2
             end
         end) l₁ l₂.
Proof.
  revert l₂. induction l₁; intros; try discriminate.
  destruct a.
  case_eq (string_dec s s0); [intros eq eqpf; subst|intros neq eqpf];
  try rewrite eqpf in *.
  - simpl in H; rewrite eqpf in H; inversion H; subst.
    rewrite domain_cons in H1.
    apply is_list_sorted_NoDup in H1; simpl in H1; inversion H1; subst.
    simpl; rewrite eqpf.
    f_equal.
    case_eq (lookup string_dec l₂ s0); [intros t teq|intros neq2]; auto.
    + elim H4. eapply in_dom; eapply lookup_in; eauto.
    + apply map_rtype_join₀_lookup_none2.
      apply is_list_sorted_NoDup in H0; simpl in H0; inversion H0; subst.
      apply lookup_nin_none; trivial.
      apply StringOrder.lt_strorder.
    + apply StringOrder.lt_strorder.
  - simpl in H |- *. rewrite eqpf in H.
    case_eq (string_dec s0 s); [intros; subst; intuition|intros neq2 ?].
    case_eq (lookup string_dec l₂ s0); [intros t teq|intros neq3]; auto.
    + rewrite domain_cons in H0,H1.
      apply is_list_sorted_Sorted_iff in H0.
      apply is_list_sorted_Sorted_iff in H1.
      apply Sorted_StronglySorted in H0; [|red;intros;etransitivity;eauto].
      apply Sorted_StronglySorted in H1; [|red;intros;etransitivity;eauto].
      simpl in H0, H1.
      generalize (StronglySorted_cons_in H0 (in_dom (lookup_in string_dec _ H))); intros ltt.
      generalize (StronglySorted_cons_in H1 (in_dom (lookup_in string_dec _ teq))); intros ltt2.
      rewrite ltt in ltt2.
      eelim ODT_lt_irr; eauto.
    + apply IHl₁; eauto.
       * rewrite domain_cons in H0. rewrite is_list_sorted_cons in H0.
         intuition.
Qed.

Lemma map_rtype_join₀_idempotent' k {rl1} :
  forall (wf1 : wf_rtype₀ (Rec₀ k rl1) = true)
         (subH : Forall
                   (fun ab : string * rtype₀ =>
                      wf_rtype₀ (snd ab) = true ->
                      rtype_join₀ (snd ab) (snd ab) = (snd ab)) rl1),
       (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s, r) :: srs =>
               match lookup string_dec l2 s with
               | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) rl1 rl1
       = rl1.
Proof.
    induction rl1; trivial.
    intros wf1 subH. generalize wf1; intros wf1'; unfold wf_rtype₀ in wf1. 
    rewrite andb_true_iff in wf1.
    destruct wf1 as [iss fb].
    rewrite domain_cons in iss.
    destruct a; simpl.
    destruct (string_dec s s); [|intuition].
    inversion subH; subst.
    simpl in fb; rewrite andb_true_iff in fb.
    destruct fb as [wff fb]. simpl in H1; rewrite H1 by intuition.
    f_equal.
    rewrite map_rtype_join₀_lookup_none2.
    + rewrite is_list_sorted_cons in iss.
      apply IHrl1; intuition. 
      apply wf_rtype₀_cons_tail in wf1'. auto.
    + apply is_list_sorted_NoDup in iss; simpl in iss; inversion iss; subst.
      apply lookup_nin_none; trivial.
      apply StringOrder.lt_strorder.
Qed.

Lemma rtype_join₀_meet₀_idempotent a :
  wf_rtype₀ a = true ->
  rtype_join₀ a a = a
  /\ rtype_meet₀ a a = a.
Proof.
  induction a; simpl; intros awf; intuition.
  - congruence.
  - congruence.
  - f_equal.
    + apply record_kind_rtype_join_idempotent.
    +  apply (map_rtype_join₀_idempotent' Closed); auto.
       rewrite Forall_forall in *; intros.
       apply H; trivial.
  - match_destr
    ; [ | generalize (rtype_meet_compatible_records_idempotent k k r);
          intuition].
    rewrite record_kind_rtype_meet_idempotent.
    f_equal.
    rewrite lookup_diff_bounded by reflexivity.
    rewrite rec_concat_sort_nil_r.
    clear r0.
    rewrite rec_sorted_id
      by (rewrite andb_true_iff in *;
           rewrite map_rtype_meet₀_domain; intuition).
    induction r; trivial.
    destruct a.
    inversion H; clear H; subst.
    simpl.
    destruct (string_dec s s); try congruence.
    rewrite andb_true_iff in *.
    destruct awf as [isl fasrr].
    simpl in fasrr.
    rewrite andb_true_iff in fasrr.
    destruct fasrr as [wfr0 fasr].
    simpl in H2.
    rewrite map_rtype_meet₀_cons2_nin.
    + rewrite IHr; trivial.
      * f_equal. f_equal. apply H2; trivial.
      * rewrite fasr.
        rewrite domain_cons in isl.
        rewrite (is_list_sorted_cons_inv _ isl).
        split; trivial.
    + apply is_list_sorted_NoDup in isl
      ; [ | apply StringOrder.lt_strorder].
      inversion isl; subst; trivial.
  - rewrite andb_true_iff in *.
    f_equal; intuition.
  - rewrite andb_true_iff in *.
    f_equal; intuition.
  - rewrite andb_true_iff in *.
    f_equal; intuition.
  - rewrite andb_true_iff in *.
    f_equal; intuition.
  - match_destr_in awf.
    rewrite brand_join_idempotent_can; trivial.
  - match_destr_in awf.
    rewrite brand_meet_idempotent_can; trivial.
  - rewrite join_idempotent; trivial.
  - rewrite meet_idempotent; trivial.
Qed.

Corollary rtype_join₀_idempotent a:
  forall (awf:wf_rtype₀ a = true),
    rtype_join₀ a a = a.
Proof.
  intros.
  apply rtype_join₀_meet₀_idempotent; trivial.
Qed.

Corollary rtype_meet₀_idempotent a:
  forall (awf:wf_rtype₀ a = true),
    rtype_meet₀ a a = a.
Proof.
  intros.
  apply rtype_join₀_meet₀_idempotent; trivial.
Qed.

Theorem rtype_join_idempotent: forall a, rtype_join a a = a.
Proof.
  intros. apply rtype_fequal; 
          destruct a as [a awf]; simpl.
  apply rtype_join₀_idempotent; auto.
Qed.

Theorem rtype_meet_idempotent a : rtype_meet a a = a.
Proof.
  intros. apply rtype_fequal; 
          destruct a as [a awf]; simpl.
  apply rtype_meet₀_idempotent; trivial.
Qed.

Lemma map_rtype_join₀_idempotent k {rl1} :
  forall (wf1 : wf_rtype₀ (Rec₀ k rl1) = true),
       (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s, r) :: srs =>
               match lookup string_dec l2 s with
               | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) rl1 rl1
       = rl1.
Proof.
  Hint Resolve rtype_join₀_idempotent.
  Hint Constructors Forallt.
  intros; apply (map_rtype_join₀_idempotent' k); auto.
  clear wf1.
  induction rl1; simpl; auto.
Qed.
  
 Lemma map_rtype_join₀_commutative' k₁ k₂ {rl1 rl2} :
  forall (wf1 : wf_rtype₀ (Rec₀ k₁ rl1) = true)
           (wf2 : wf_rtype₀ (Rec₀ k₂ rl2) = true)
           (subH : Forall
                  (fun ab : string * rtype₀ =>
                     forall b : rtype₀,
                     wf_rtype₀ (snd ab) = true ->
                       wf_rtype₀ b = true -> rtype_join₀ (snd ab) b = rtype_join₀ b (snd ab)) rl1),
       (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s, r) :: srs =>
               match lookup string_dec l2 s with
               | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) rl1 rl2
       = (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s, r) :: srs =>
               match lookup string_dec l2 s with
               | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) rl2 rl1.
Proof.
  intros wf1 wf2 subH.
  revert wf1 subH rl2 wf2.
  induction rl1; intros.
  - generalize (map_rtype_join₀_domain_subset rl2 nil).
      destruct ( (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s, r) :: srs =>
          match lookup string_dec l2 s with
          | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
          | None => map_rtype_join₀ srs l2
          end
      end) rl2 nil); trivial; simpl.
      intros iin.
      specialize (iin (fst p)); intuition.
    - inversion subH; subst.
       specialize (IHrl1 (wf_rtype₀_cons_tail wf1) H2).
       destruct a.
       repeat rewrite (IHr _ bwf).
       case_eq (lookup string_dec rl2 s); [intros t teq|intros neq]; auto.
       + specialize (IHrl1 _ wf2); simpl in wf2; rewrite andb_true_iff in wf2. 
         rewrite (map_rtype_join₀_lookup_some2 teq) 
           by (simpl in wf1; repeat rewrite andb_true_iff in wf1; intuition).
         f_equal. f_equal.
         apply H1; simpl.
         simpl in wf1; repeat rewrite andb_true_iff in wf1; intuition.
         rewrite forallb_forall in wf2.
         apply lookup_in in teq; intuition.
         specialize (H0 _ teq). simpl in *; trivial. 
         auto.
       + rewrite map_rtype_join₀_lookup_none2; auto.
Qed.

Lemma map_rtype_meet₀_lookup_none1 {l₁ l₂ s r} :
lookup string_dec l₂ s = None ->
(fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_meet₀ r1 r') :: map_rtype_meet₀ srs l2
          | None => map_rtype_meet₀ srs l2
          end
      end) ((s, r)::l₁) l₂ =
(fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_meet₀ r1 r') :: map_rtype_meet₀ srs l2
          | None => map_rtype_meet₀ srs l2
          end
      end) l₁ l₂.
Proof.
  simpl; intros nin.
  rewrite nin; trivial.
Qed.

Lemma map_rtype_meet₀_lookup_none2 {l₁ l₂ s r} :
lookup string_dec l₁ s = None ->
(fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_meet₀ r1 r') :: map_rtype_meet₀ srs l2
          | None => map_rtype_meet₀ srs l2
          end
      end) l₁ ((s, r) :: l₂) =
(fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_meet₀ r1 r') :: map_rtype_meet₀ srs l2
          | None => map_rtype_meet₀ srs l2
          end
      end) l₁ l₂.
Proof.
  induction l₁; trivial; intros nin.
  destruct a; simpl in *.
    case_eq (string_dec s s0);
      [intros t teq; rewrite teq in nin; discriminate
       |intros neq neqpf].
    rewrite neqpf in nin.
    case_eq (string_dec s0 s); [intros; subst; intuition|intros neq2 ?].
    repeat rewrite (IHl₁ nin); trivial.
Qed.

Lemma map_rtype_meet₀_lookup_some2 {l₁ l₂ s τ₁ τ₂} :
  lookup string_dec l₁ s = Some τ₁ ->
  is_list_sorted ODT_lt_dec (domain l₁) = true ->
  is_list_sorted ODT_lt_dec (domain ((s,τ₂)::l₂)) = true ->
   (fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s0, r1) :: srs =>
          match lookup string_dec l2 s0 with
          | Some r' => (s0, rtype_meet₀ r1 r') :: map_rtype_meet₀ srs l2
          | None => map_rtype_meet₀ srs l2
          end
      end) l₁ ((s, τ₂) :: l₂) =
 (s, rtype_meet₀ τ₁ τ₂)
   :: (fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
         list (string * rtype₀) :=
         match l1 with
         | nil => nil
         | (s0, r1) :: srs =>
             match lookup string_dec l2 s0 with
             | Some r' => (s0, rtype_meet₀ r1 r') :: map_rtype_meet₀ srs l2
             | None => map_rtype_meet₀ srs l2
             end
         end) l₁ l₂.
Proof.
  revert l₂. induction l₁; intros; try discriminate.
  destruct a.
  case_eq (string_dec s s0); [intros eq eqpf; subst|intros neq eqpf];
  try rewrite eqpf in *.
  - simpl in H; rewrite eqpf in H; inversion H; subst.
    rewrite domain_cons in H1.
    apply is_list_sorted_NoDup in H1; simpl in H1; inversion H1; subst.
    simpl; rewrite eqpf.
    f_equal.
    case_eq (lookup string_dec l₂ s0); [intros t teq|intros neq2]; auto.
    + elim H4. eapply in_dom; eapply lookup_in; eauto.
    + apply map_rtype_meet₀_lookup_none2.
      apply is_list_sorted_NoDup in H0; simpl in H0; inversion H0; subst.
      apply lookup_nin_none; trivial.
      apply StringOrder.lt_strorder.
    + apply StringOrder.lt_strorder.
  - simpl in H |- *. rewrite eqpf in H.
    case_eq (string_dec s0 s); [intros; subst; intuition|intros neq2 ?].
    case_eq (lookup string_dec l₂ s0); [intros t teq|intros neq3]; auto.
    + rewrite domain_cons in H0,H1.
      apply is_list_sorted_Sorted_iff in H0.
      apply is_list_sorted_Sorted_iff in H1.
      apply Sorted_StronglySorted in H0; [|red;intros;etransitivity;eauto].
      apply Sorted_StronglySorted in H1; [|red;intros;etransitivity;eauto].
      simpl in H0, H1.
      inversion H0; subst. inversion H1; subst.
      rewrite Forall_forall in *.
      specialize (H6 _ (in_dom (lookup_in string_dec _ H))).
      specialize (H8 _ (in_dom (lookup_in string_dec _ teq))).
      rewrite H6 in H8.
      eelim ODT_lt_irr; eauto.
    + apply IHl₁; eauto.
       * rewrite domain_cons in H0. rewrite is_list_sorted_cons in H0.
         intuition.
Qed.

Lemma rtype_join₀_meet₀_commutative a b: 
  forall (awf : wf_rtype₀ a = true)
         (bwf : wf_rtype₀ b = true),
    rtype_join₀ a b = rtype_join₀ b a
    /\ rtype_meet₀ a b = rtype_meet₀ b a.
Proof.
  revert b.
  induction a; try solve[destruct b; simpl; tauto].
  - destruct b; simpl; try tauto; intros.
    split; f_equal; apply IHa; trivial.
  - split.
    + destruct b; simpl; intuition; f_equal; auto.
      * apply record_kind_rtype_join_comm.
      * (* Note the Closed is an arbitrary (concrete) choice here,
          since wf_rtype₀ doesn't actually care *)
        apply (@map_rtype_join₀_commutative' Closed Closed); trivial.
        rewrite Forall_forall in *; intros; apply H; trivial.
    + simpl. destruct b; simpl; try tauto.
      match_destr; match_destr; trivial;
      try solve [
            generalize (rtype_meet_compatible_records_commutative k k0 r srl );
            generalize (rtype_meet_compatible_records_commutative k0 k srl r );
      intuition].
      rewrite record_kind_rtype_meet_commutative.
      f_equal.
      unfold rec_concat_sort.
      simpl in *; rewrite andb_true_iff in *.
      apply drec_sort_perm_eq.
      { apply NoDup_map_rtype_meet₀_lookup_diff; intuition; eauto 2. }
      apply NoDup_Permutation.
      { apply NoDup_domain_NoDup; apply NoDup_map_rtype_meet₀_lookup_diff; intuition; eauto 2. }
      { apply NoDup_domain_NoDup; apply NoDup_map_rtype_meet₀_lookup_diff; intuition; eauto 2. }
      clear r0.
      destruct x.
      {
      split; (intros inn; apply (in_lookup_nodup string_dec) in inn;
       [ | apply NoDup_map_rtype_meet₀_lookup_diff; intuition; eauto 2]);
      rewrite lookup_app in inn;
      (match_case_in inn; [intros ? eqq | intros eqq]);
      rewrite eqq in inn.
      - inversion inn; clear inn; subst.
        assert (In s (domain r))
          by (apply lookup_in in eqq;
              apply in_dom in eqq;
              rewrite map_rtype_meet₀_domain in eqq;
              trivial).
        apply (in_dom_lookup string_dec) in H0.
        destruct H0 as [v rslo].
        case_eq (lookup string_dec srl s); intros.
        + rewrite in_app_iff. left.
          rewrite (map_rtype_meet₀_rtype_meets rslo H0) in eqq.
          apply (lookup_in string_dec).
          rewrite (map_rtype_meet₀_rtype_meets H0 rslo).
          rewrite <- eqq.
          f_equal.
          apply lookup_in in rslo.
          rewrite Forall_forall in H.
          destruct (H _ rslo r2) as [_ ree]; simpl; trivial.
          * rewrite forallb_forall in *; intuition.
             apply (H2 (s,v)); trivial.
          * rewrite forallb_forall in *; intuition.
             apply (H4 (s,r2)); trivial.
             eapply lookup_in; eauto.
          * simpl in ree; rewrite <- ree; trivial.
        + rewrite in_app_iff.
           right.
           apply (lookup_in string_dec).
           rewrite lookup_diff_none2; trivial.
           rewrite (map_rtype_meet₀_some_none rslo H0) in eqq.
           inversion eqq; subst; trivial.
      - apply lookup_in in inn.
        apply lookup_diff_inv in inn.
        destruct inn as [inn ninn].
        rewrite in_app_iff. left.
        apply (lookup_in string_dec).
        apply map_rtype_meet₀_some_none.
        + apply in_lookup_nodup; trivial.
          destruct bwf as [isl _].
          apply is_list_sorted_NoDup in isl
          ; [ | apply StringOrder.lt_strorder]; trivial.
        + apply lookup_nin_none.
          simpl in *; trivial.
- inversion inn; clear inn; subst.
        assert (In s (domain srl))
          by (apply lookup_in in eqq;
              apply in_dom in eqq;
              rewrite map_rtype_meet₀_domain in eqq;
              trivial).
        apply (in_dom_lookup string_dec) in H0.
        destruct H0 as [v rslo].
        case_eq (lookup string_dec r s); intros.
        + rewrite in_app_iff. left.
          rewrite (map_rtype_meet₀_rtype_meets rslo H0) in eqq.
          apply (lookup_in string_dec).
          rewrite (map_rtype_meet₀_rtype_meets H0 rslo).
          rewrite <- eqq.
          f_equal.
          apply lookup_in in H0.
          rewrite Forall_forall in H.
          destruct (H _ H0 v) as [_ ree]; simpl; trivial.
          * rewrite forallb_forall in *; intuition.
            apply (H2 (s,r2)); trivial.
          * rewrite forallb_forall in *; intuition.
             apply (H4 (s,v)); trivial.
             eapply lookup_in; eauto.
        + rewrite in_app_iff.
           right.
           apply (lookup_in string_dec).
           rewrite lookup_diff_none2; trivial.
           rewrite (map_rtype_meet₀_some_none rslo H0) in eqq.
           inversion eqq; subst; trivial.
      - apply lookup_in in inn.
        apply lookup_diff_inv in inn.
        destruct inn as [inn ninn].
        rewrite in_app_iff. left.
        apply (lookup_in string_dec).
        apply map_rtype_meet₀_some_none.
        + apply in_lookup_nodup; trivial.
          destruct awf as [isl _].
          apply is_list_sorted_NoDup in isl
          ; [ | apply StringOrder.lt_strorder]; trivial.
        + apply lookup_nin_none.
          simpl in *; trivial.
    }

  - intros.
    destruct b; simpl; intuition;
    destruct (Either₀_wf_inv awf) as [??];
    destruct (Either₀_wf_inv bwf) as [??];
    (f_equal; [apply IHa1 | apply IHa2]; trivial).
  - intros.
    destruct b; simpl; intuition;
    destruct (Either₀_wf_inv awf) as [??];
    destruct (Either₀_wf_inv bwf) as [??];
    (f_equal; [apply IHa1 | apply IHa2]; trivial).
  - intros.
    destruct b0; simpl; try tauto.
    rewrite brand_join_commutative.
    rewrite brand_meet_commutative.
    tauto.
  - intros.
    destruct b; simpl; intuition.
    + rewrite join_commutative; trivial.
    + rewrite meet_commutative; trivial.
Qed.

Corollary rtype_join₀_commutative a b: 
  forall (awf : wf_rtype₀ a = true)
         (bwf : wf_rtype₀ b = true),
         rtype_join₀ a b = rtype_join₀ b a.
Proof.
  intros; apply rtype_join₀_meet₀_commutative; trivial.
Qed.

Corollary rtype_meet₀_commutative a b: 
  forall (awf : wf_rtype₀ a = true)
         (bwf : wf_rtype₀ b = true),
         rtype_meet₀ a b = rtype_meet₀ b a.
Proof.
  intros; apply rtype_join₀_meet₀_commutative; trivial.
Qed.

Theorem rtype_join_commutative: forall a b, rtype_join a b = rtype_join b a.
Proof.
  intros. apply rtype_fequal; 
          destruct a as [a awf]; destruct b as [b bwf]; simpl.
  apply rtype_join₀_commutative; auto.
Qed.

Theorem rtype_meet_commutative: forall a b, rtype_meet a b = rtype_meet b a.
Proof.
  intros. apply rtype_fequal; 
          destruct a as [a awf]; destruct b as [b bwf]; simpl.
  apply rtype_meet₀_commutative; auto.
Qed.

 Lemma map_rtype_join₀_commutative k₁ k₂ {rl1 rl2} :
  forall (wf1 : wf_rtype₀ (Rec₀ k₁ rl1) = true)
           (wf2 : wf_rtype₀ (Rec₀ k₂ rl2) = true),
       (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s, r) :: srs =>
               match lookup string_dec l2 s with
               | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) rl1 rl2
       = (fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s, r) :: srs =>
               match lookup string_dec l2 s with
               | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) rl2 rl1.
Proof.
  Hint Resolve rtype_join₀_commutative.
  Hint Constructors Forallt.
  intros; apply (@map_rtype_join₀_commutative' Closed Closed); auto.
  clear wf1 wf2.
  induction rl1; simpl; auto.
Qed.


Lemma map_rtype_join₀_lookup_rtype_join {l₁ l₂ s τ₁ τ₂} :
   lookup string_dec l₁ s = Some τ₁ ->
   lookup string_dec l₂ s = Some τ₂ ->
   lookup string_dec (((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s0, r1) :: srs =>
               match lookup string_dec l2 s0 with
               | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) l₁ l₂)) s = Some (rtype_join₀ τ₁ τ₂).
Proof.
  revert l₂.
  induction l₁; simpl; [discriminate|].
  destruct a; simpl; intros.
  case_eq (string_dec s0 s); [intros; subst |intros neq ?].
  - rewrite H1 in H. inversion H; subst.
    rewrite H0. simpl. rewrite H1. trivial.
  - case_eq (string_dec s s0); [intros; subst; intuition |intros neq2 ?].
    rewrite H2 in H. specialize (IHl₁ _ H H0).
    case_eq (lookup string_dec l₂ s0); [intros t teq|intros neq3]; auto.
    simpl. rewrite H2. auto.
Qed.

Lemma map_rtype_join₀_lookup_none1_rtype_join {l₁ l₂ s} :
   lookup string_dec l₁ s = None ->
   lookup string_dec (((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s0, r1) :: srs =>
               match lookup string_dec l2 s0 with
               | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) l₁ l₂)) s = None.
Proof.
  intros.
  generalize (map_rtype_join₀_domain_subset l₁ l₂ s).
  case_eq (lookup string_dec
     ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
         list (string * rtype₀) :=
         match l1 with
         | nil => nil
         | (s0, r1) :: srs =>
             match lookup string_dec l2 s0 with
             | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
             | None => map_rtype_join₀ srs l2
             end
         end) l₁ l₂) s); trivial.
  intros.
  apply lookup_in,in_dom in H0.
  apply lookup_none_nin in H.
  intuition.
Qed.

Lemma map_rtype_join₀_lookup_none2_rtype_join {l₁ l₂ s} :
   lookup string_dec l₂ s = None ->
   lookup string_dec (((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
           list (string * rtype₀) :=
           match l1 with
           | nil => nil
           | (s0, r1) :: srs =>
               match lookup string_dec l2 s0 with
               | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
               | None => map_rtype_join₀ srs l2
               end
           end) l₁ l₂)) s = None.
Proof.
  intros.
  generalize (map_rtype_join₀_domain_subset l₁ l₂ s).
  case_eq (lookup string_dec
     ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
         list (string * rtype₀) :=
         match l1 with
         | nil => nil
         | (s0, r1) :: srs =>
             match lookup string_dec l2 s0 with
             | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
             | None => map_rtype_join₀ srs l2
             end
         end) l₁ l₂) s); trivial.
  intros.
  apply lookup_in,in_dom in H0.
  apply lookup_none_nin in H.
  intuition.
Qed.

Lemma map_rtype_join₀_domain_sublist a b :
  sublist (domain ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} : list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
                | None => map_rtype_join₀ srs l2
                end
            end) a b)) (domain a).
Proof.
  induction a; simpl; auto 1.
  destruct a. destruct (lookup string_dec b s); simpl.
  - apply sublist_cons; auto.
  - apply sublist_skip; auto.
Qed.

Lemma map_rtype_join₀_domain_is_list_sorted {a b} :
  is_list_sorted ODT_lt_dec (domain a) = true ->
  is_list_sorted ODT_lt_dec (domain ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
                | None => map_rtype_join₀ srs l2
                end
            end) a b)) = true.
Proof.
  intros s1.
  apply (is_list_sorted_sublist s1).
  apply map_rtype_join₀_domain_sublist.
Qed.

Lemma map_rtype_join₀_domain {a b}:
  is_list_sorted ODT_lt_dec (domain a) = true ->
  is_list_sorted ODT_lt_dec (domain b) = true ->
  domain a = domain b ->
  domain ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
                | None => map_rtype_join₀ srs l2
                end
            end) a b) = domain a.
Proof.
  intros.
  apply Sorted_incl_both_eq.
  - eapply is_list_sorted_Sorted_iff.
    apply map_rtype_join₀_domain_is_list_sorted.
    trivial.
  - eapply is_list_sorted_Sorted_iff. eassumption.
  - intros; apply map_rtype_join₀_domain_subset in H2; tauto.
  - intros. apply map_rtype_join₀_domain_subset_inv.
    intuition congruence.
Qed.

Lemma record_kind_rtype_join_associative {k k0 k1 a b c}:
    wf_rtype₀ (Rec₀ k a) = true ->
   wf_rtype₀ (Rec₀ k0 b) = true ->
   wf_rtype₀ (Rec₀ k1 c) = true ->
   (record_kind_rtype_join (record_kind_rtype_join k k0 a b) k1
        ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
                | None => map_rtype_join₀ srs l2
                end
            end) a b) c) =
 (record_kind_rtype_join k (record_kind_rtype_join k0 k1 b c) a
        ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s, r) :: srs =>
                match lookup string_dec l2 s with
                | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
                | None => map_rtype_join₀ srs l2
                end
            end) b c)).
Proof.
  intros.
  destruct k; simpl; trivial.
  destruct k0; simpl; trivial.
  destruct k1; simpl; trivial
  ; [rewrite record_kind_rtype_join_open_r; trivial | ].
  simpl in *; rewrite andb_true_iff in *; intuition.
  destruct (equiv_dec (domain a) (domain b))
  ; unfold equiv, complement in *; subst; simpl.
  - rewrite (@map_rtype_join₀_domain a b) by auto.
    rewrite e.
    destruct (equiv_dec (domain b) (domain c)); trivial.
    rewrite map_rtype_join₀_domain by auto.
    destruct (equiv_dec (domain b) (domain b)); congruence.
  - destruct (equiv_dec (domain b) (domain c)); trivial
    ; unfold equiv, complement in *; subst; simpl.
    rewrite map_rtype_join₀_domain by auto.
    destruct (equiv_dec (domain a) (domain b)); congruence.
Qed.


Lemma domain_map_rtype_meet₀_diff r srl :
      domain (rec_concat_sort
            ((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
                list (string * rtype₀) :=
                match l1 with
                | nil => nil
                | (s, r) :: srs =>
                    match lookup string_dec l2 s with
                    | Some r' => (s, rtype_meet₀ r r') :: map_rtype_meet₀ srs l2
                    | None => (s, r) :: map_rtype_meet₀ srs l2
                    end
                end) r srl) (lookup_diff string_dec srl r)) =
      domain (rec_concat_sort r srl).
Proof.
  unfold rec_concat_sort.
  repeat rewrite domain_rec_sort.
  apply insertion_sort_equivlist; [apply lt_contr1 | ].
  repeat rewrite domain_app.
  rewrite map_rtype_meet₀_domain.
  split; repeat rewrite in_app_iff; intuition.
  - apply in_domain_in in H0.
    destruct H0 as [? inn].
    apply lookup_diff_inv in inn.
    destruct inn as [inn _].
    apply in_dom in inn.
    intuition.
  - case_eq (lookup string_dec r x); intros.
    + apply lookup_in in H.
      apply in_dom in H.
      intuition.
    + right. generalize (lookup_diff_none2 string_dec srl H); intros.
      apply (in_dom_lookup string_dec) in H0.
      destruct H0 as [? inn].
      rewrite inn in H1.
      apply lookup_in in H1.
      apply in_dom in H1.
      trivial.
Qed.


Lemma NoDup_domain_lookups_Permutation {A B : Type} dec (l l' : list (A*B)) :
       NoDup (domain l) ->
       NoDup (domain l') ->
       (forall x : A, lookup dec l x = lookup dec l' x) ->
       Permutation l l'.
Proof.
  intros.
  apply NoDup_Permutation.
  - apply NoDup_domain_NoDup; trivial.
  - apply NoDup_domain_NoDup; trivial.
  - intros [a b]; split; intros inn;
    apply (in_lookup_nodup dec) in inn; trivial;
    apply (lookup_in dec); specialize (H1 a); congruence.
Qed.

Lemma lookup_nodup_perm {A B : Type}
      (dec : forall a a' : A, {a = a'} + {a <> a'})
         (l l' : list (A * B)) (a : A) :
       NoDup (domain l) ->
       Permutation l l' ->
       lookup dec l a = lookup dec l' a.
Proof.
  intros.
  case_eq (lookup dec l a); intros; symmetry.
  - eapply lookup_some_nodup_perm; eauto.
  - eapply lookup_none_perm; eauto.
Qed.

Lemma map_rtype_meet₀_domain_rec_concat_sort r srl s :
              NoDup (domain r) ->
              NoDup (domain srl) ->
        lookup string_dec (rec_concat_sort ((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s0, r0) :: srs =>
                match lookup string_dec l2 s0 with
                | Some r' => (s0, rtype_meet₀ r0 r') :: map_rtype_meet₀ srs l2
                | None => (s0, r0) :: map_rtype_meet₀ srs l2
                end
            end) r srl) (lookup_diff string_dec srl r)) s
              = lookup string_dec (((fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
            list (string * rtype₀) :=
            match l1 with
            | nil => nil
            | (s0, r0) :: srs =>
                match lookup string_dec l2 s0 with
                | Some r' => (s0, rtype_meet₀ r0 r') :: map_rtype_meet₀ srs l2
                | None => (s0, r0) :: map_rtype_meet₀ srs l2
                end
            end) r srl) ++ (lookup_diff string_dec srl r)) s.
Proof.
  unfold rec_concat_sort.
  intros.
  apply lookup_nodup_perm.
  - apply (is_list_sorted_NoDup ODT_lt_dec).
    eapply rec_sort_sorted; reflexivity.
  - symmetry. apply rec_sort_perm.
    apply NoDup_map_rtype_meet₀_lookup_diff; trivial.
Qed.

Lemma map_rtype_join₀_associative' {k k0 k1 a b c}:
     Forall
     (fun ab : string * rtype₀ =>
      forall b c : rtype₀,
      wf_rtype₀ (snd ab) = true ->
      wf_rtype₀ b = true ->
      wf_rtype₀ c = true ->
      rtype_join₀ (rtype_join₀ (snd ab) b) c = rtype_join₀ (snd ab) (rtype_join₀ b c)) a ->
    wf_rtype₀ (Rec₀ k a) = true ->
   wf_rtype₀ (Rec₀ k0 b) = true ->
   wf_rtype₀ (Rec₀ k1 c) = true ->
     rtype_join₀ (rtype_join₀ (Rec₀ k a) (Rec₀ k0 b)) (Rec₀ k1 c) =
     rtype_join₀ (Rec₀ k a) (rtype_join₀ (Rec₀ k0 b) (Rec₀ k1 c)).
Proof.
  intros X awf bwf cwf.
  induction a; trivial.
  - simpl. rewrite <- record_kind_rtype_join_associative; auto.
  - inversion X; clear X; subst.
    specialize (IHa H2 (wf_rtype₀_cons_tail awf)).
    destruct a.
    inversion IHa; clear IHa.
    simpl.
    rewrite <- record_kind_rtype_join_associative by (simpl in *; auto).
    f_equal. 
    case_eq (lookup string_dec b s); 
      [intros t teq|intros neq; 
         rewrite (map_rtype_join₀_lookup_none1_rtype_join neq); trivial].
    case_eq (lookup string_dec c s); 
      [intros t2 teq2|intros neq; 
         rewrite (map_rtype_join₀_lookup_none2_rtype_join neq); trivial].
    rewrite (map_rtype_join₀_lookup_rtype_join teq teq2).
    rewrite H3.
    f_equal.
    f_equal.
    apply H1; simpl; auto.
    + apply (wf_rtype₀_cons_wf awf).
    + apply lookup_in in teq.
      apply lookup_in in teq2.
      revert bwf cwf teq teq2.
      clear; simpl; repeat rewrite andb_true_iff, forallb_forall.
      intuition.
      apply (H2 _ teq).
    + apply lookup_in in teq.
      apply lookup_in in teq2.
      revert bwf cwf teq teq2.
      clear; simpl; repeat rewrite andb_true_iff, forallb_forall.
      intuition.
      apply (H3 _ teq2).
Qed.

Lemma rtype_join₀_meet₀_associative {a b c : rtype₀} :
   wf_rtype₀ a = true ->
   wf_rtype₀ b = true ->
   wf_rtype₀ c = true ->
   rtype_join₀ (rtype_join₀ a b) c = rtype_join₀ a (rtype_join₀ b c)
   /\ rtype_meet₀ (rtype_meet₀ a b) c = rtype_meet₀ a (rtype_meet₀ b c).
Proof.
  revert b c.
  induction a; simpl. 
  - destruct b; destruct c; simpl; try tauto. 
  - destruct b; destruct c; simpl; try tauto. 
    repeat rewrite andb_true_iff; intuition.
    match_destr.
  - destruct b; destruct c; simpl; try tauto. 
    repeat rewrite andb_true_iff; intuition.
    destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial.
  - destruct b; destruct c; simpl; try tauto. 
    repeat rewrite andb_true_iff; intuition.
    destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial.
  - destruct b; destruct c; simpl; try tauto. 
    repeat rewrite andb_true_iff; intuition.
    destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial.
  - destruct b; destruct c; simpl; try tauto. 
    repeat rewrite andb_true_iff; intuition.
    destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial.
  - destruct b; destruct c; simpl; try tauto. 
    repeat rewrite andb_true_iff; intuition.
    destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial.
  - destruct b; destruct c; simpl; try tauto. 
    repeat rewrite andb_true_iff; intuition.
    + f_equal; apply IHa; trivial.
    + f_equal; apply IHa; trivial.
    + destruct (rtype_meet_compatible_records_dec k k0 srl srl0); tauto.
  - destruct b; destruct c; simpl; try tauto;
             try solve[intros; destruct (rtype_meet_compatible_records_dec k k0 r srl); tauto].
    repeat rewrite andb_true_iff; intuition.
    + intros. apply map_rtype_join₀_associative'; simpl;
                try rewrite andb_true_iff; auto 3.
      rewrite Forall_forall in *; intros.
      apply H; trivial.
    + { destruct (rtype_meet_compatible_records_dec k k0 r srl); simpl; trivial;
        destruct (rtype_meet_compatible_records_dec k0 k1 srl srl0); trivial.
            + {
        match_destr; match_destr.
        - (* This is the only case where everything is compatible.
              The rest (of the Rec) part of the proofs show that 
              any incompatibility propogates and yields bottom both ways
         *)
          erewrite rtype_meet_compatible_records_domain_eq_l in r2;
          [ | eapply domain_map_rtype_meet₀_diff].
          erewrite rtype_meet_compatible_records_domain_eq_r in r3;
          [ | eapply domain_map_rtype_meet₀_diff].
          rewrite record_kind_rtype_meet_associative.
          f_equal.
          apply drec_sort_perm_eq.
          {
            apply NoDup_map_rtype_meet₀_lookup_diff.
            - rewrite domain_map_rtype_meet₀_diff.
              unfold rec_concat_sort; rewrite domain_rec_sort.
              apply (is_list_sorted_NoDup ODT_lt_dec).
              eapply is_list_sorted_Sorted_iff.
              eapply insertion_sort_Sorted.
            - eauto 2.
          }
          apply (NoDup_domain_lookups_Permutation string_dec).
          {
            apply NoDup_map_rtype_meet₀_lookup_diff.
            - rewrite domain_map_rtype_meet₀_diff.
              unfold rec_concat_sort; rewrite domain_rec_sort.
              apply (is_list_sorted_NoDup ODT_lt_dec).
              eapply is_list_sorted_Sorted_iff.
              eapply insertion_sort_Sorted.
            - eauto 2.
          }
          {
            apply NoDup_map_rtype_meet₀_lookup_diff.
            - eauto 2.
            - rewrite domain_map_rtype_meet₀_diff.
              unfold rec_concat_sort; rewrite domain_rec_sort.
              apply (is_list_sorted_NoDup ODT_lt_dec).
              eapply is_list_sorted_Sorted_iff.
              eapply insertion_sort_Sorted.
          }
        (* At this point, I need to show that lookups on both coincide *)
          intros s.
          {
            simpl in *. 
            repeat rewrite lookup_app.
            Ltac lsimp :=
              try (rewrite map_rtype_meet₀_domain_rec_concat_sort by eauto 2);
              try rewrite lookup_app.
            Ltac lsn t1
              := rewrite (map_rtype_meet₀_some_none (τ₁:=t1)); trivial;
                 lsimp.
            Ltac ln 
              := rewrite (map_rtype_meet₀_none); trivial;
                 lsimp.
            Ltac lmm t1 t2
              := rewrite (map_rtype_meet₀_rtype_meets (τ₁:=t1) (τ₂:=t2)); trivial;
                 lsimp.
            Ltac ldn1 := rewrite lookup_diff_none1; trivial; lsimp.
            Ltac ldn2 := rewrite lookup_diff_none2; trivial; lsimp.

            case_eq (lookup string_dec r s); [intros τr inr| intros ninr];
            (case_eq (lookup string_dec srl s); [intros τs ins| intros nins];
             (case_eq (lookup string_dec srl0 s); [intros τs0 ins0| intros nins0])).
            - lmm (rtype_meet₀ τr τs) (τs0).
              + lmm (τr) ((rtype_meet₀ τs τs0)).
                * rewrite Forall_forall in H.
                  generalize (H (s, τr)); intros mm.
                  {  rewrite forallb_forall in *.
                     f_equal.
                     apply mm; trivial.
                    - apply (lookup_in string_dec); trivial.
                    - apply lookup_in in inr. 
                      apply (H4 _ inr).
                    - apply lookup_in in ins.
                      apply (H5 _ ins).
                    - apply lookup_in in ins0.
                      apply (H6 _ ins0).
                  }
                * lmm τs τs0.
              + lmm τr τs.
            - lsn (rtype_meet₀ τr τs).
              + lmm τr τs.
                lsn τs.
              + lmm τr τs.
            - lmm τr τs0.
              + lmm τr τs0.
                ln.
                ldn2.
              + lsn τr.
            - lsn τr.
              + lsn τr.
                ln.
                ldn1.
              + lsn τr.
            - lmm τs τs0.
              + ln.
                ldn2.
                lmm τs τs0.
              + ln.
                ldn2.
            - lsn τs.
              + ln.
                ldn2.
                lsn τs.
              + ln.
                ldn2.
            - ln.
              + ldn2.
                * ln.
                  ldn2.
                  ln.
                  ldn2.
                * ln.
                  ldn1.
              + ln.
                ldn1.
            - ln.
              + ldn1.
                ln.
                ldn1.
                ln.
                ldn1.
              + ln.
                ldn1.
          }
        - erewrite rtype_meet_compatible_records_domain_eq_l in r2;
          [ | eapply domain_map_rtype_meet₀_diff].
          elim n; clear n.
          erewrite rtype_meet_compatible_records_domain_eq_r;
            [ | eapply domain_map_rtype_meet₀_diff].
          destruct k; destruct k0; destruct k1; simpl in *; trivial.
          + rewrite sublist_rec_concat_sort_bounded
              by (rewrite r1; reflexivity).
            rewrite sort_sorted_is_id
              by intuition.
            rewrite <- r2.
            apply rec_concat_sort_sublist_sorted.
            intuition.
          + rewrite r0.
            apply rec_concat_sort_sublist_sorted; intuition.
          + rewrite r0.
            apply rec_concat_sort_sublist_sorted; intuition.
          + assert (subl:sublist (domain srl0) (domain r)).
            * rewrite domain_rec_concat_sort_app_comm in r2.
               rewrite sublist_rec_concat_sort_bounded in r2.
               { rewrite sort_sorted_is_id in r2; intuition. }
               rewrite r0; reflexivity.
            * rewrite <- (sort_sorted_is_id r) by intuition.
              apply incl_sort_sublist.
              rewrite domain_app.
              apply incl_app; apply sublist_incl_sub; trivial.
          + rewrite domain_rec_concat_sort_app_comm in r2.
            rewrite sublist_rec_concat_sort_bounded in r2
              by (apply sublist_incl_sub; eauto).
            rewrite sort_sorted_is_id in r2
              by intuition.
            rewrite sublist_rec_concat_sort_bounded
              by (apply sublist_incl_sub; eauto).
            rewrite sort_sorted_is_id
              by intuition.
            trivial.
          + rewrite domain_rec_concat_sort_app_comm.
            rewrite sublist_rec_concat_sort_bounded
              by (apply sublist_incl_sub; intuition).
            rewrite sort_sorted_is_id
              by intuition.
            trivial.
          +  rewrite sublist_rec_concat_sort_bounded
              by (rewrite r1; intuition).
            rewrite sort_sorted_is_id
               by intuition.
            congruence.
        - erewrite rtype_meet_compatible_records_domain_eq_r in r2;
            [ | eapply domain_map_rtype_meet₀_diff].
          elim n; clear n.
          erewrite rtype_meet_compatible_records_domain_eq_l;
            [ | eapply domain_map_rtype_meet₀_diff].
          destruct k; destruct k0; destruct k1; simpl in *; trivial.
          + rewrite sublist_rec_concat_sort_bounded in r2
              by (rewrite r1; reflexivity).
            rewrite sort_sorted_is_id in r2
              by intuition.
            rewrite <- (sort_sorted_is_id srl0) by intuition.
            apply incl_sort_sublist.
            rewrite domain_app.
            apply incl_app; apply sublist_incl_sub; trivial.
          + rewrite domain_rec_concat_sort_app_comm in r2.
            rewrite sublist_rec_concat_sort_bounded in r2
              by (apply sublist_incl_sub; eauto).
            rewrite sort_sorted_is_id in r2
              by intuition.
            rewrite sublist_rec_concat_sort_bounded
              by (apply sublist_incl_sub; eauto).
            rewrite sort_sorted_is_id
              by intuition.
            trivial.
          + rewrite sublist_rec_concat_sort_bounded
              by (apply sublist_incl_sub; intuition).
            rewrite sort_sorted_is_id
              by intuition.
            trivial.
          +  rewrite domain_rec_concat_sort_app_comm.
             rewrite sublist_rec_concat_sort_bounded
              by (rewrite r0; intuition).
            rewrite sort_sorted_is_id
               by intuition.
            rewrite <- r2.
            rewrite domain_rec_concat_sort_app_comm.
            apply rec_concat_sort_sublist_sorted.
            intuition.
          + rewrite sublist_rec_concat_sort_bounded in r2
              by (rewrite r1; intuition).
            rewrite sort_sorted_is_id in r2
              by intuition.
            rewrite domain_rec_concat_sort_app_comm.
            rewrite sublist_rec_concat_sort_bounded
              by (rewrite r0; intuition).
            rewrite sort_sorted_is_id 
               by intuition.
            trivial.
          + rewrite domain_rec_concat_sort_app_comm in r2.
            rewrite sublist_rec_concat_sort_bounded in r2
              by (rewrite r1; intuition).
            rewrite sort_sorted_is_id in r2
              by intuition.
            rewrite sublist_rec_concat_sort_bounded
              by (rewrite r2; intuition).
            rewrite sort_sorted_is_id
              by intuition.
            trivial.
          +  rewrite sublist_rec_concat_sort_bounded
              by (rewrite r0; intuition).
             rewrite sort_sorted_is_id
               by intuition.
             trivial.
      }
    + match_destr.
      erewrite rtype_meet_compatible_records_domain_eq_l in r1;
        [ | eapply domain_map_rtype_meet₀_diff].
      destruct k; destruct k0; destruct k1; simpl in *;
      intuition.
      * unfold rec_concat_sort in r1.
        rewrite domain_rec_sort in r1.
        rewrite domain_app in r1.
        elim n.
        generalize (sublist_of_sorted_sublist StringOrder.trichotemy StringOrder.lt_dec r1 (domain srl)); intros subl.
        rewrite insertion_sort_sorted_is_id in subl.
        { apply subl. apply sublist_app_r. }
        intuition.
      * rewrite sublist_rec_concat_sort_bounded in r1.
        { rewrite sort_sorted_is_id in r1;
          intuition.
        }
        rewrite r0; reflexivity.
      * rewrite sublist_rec_concat_sort_bounded in r1.
        { rewrite sort_sorted_is_id in r1;
          intuition.
        }
        rewrite r0; reflexivity.
      * rewrite domain_rec_concat_sort_app_comm in r1.
        rewrite sublist_rec_concat_sort_bounded in r1.
        { rewrite sort_sorted_is_id in r1;
          intuition.
          rewrite r1 in n.
          intuition.
        }
        rewrite r0; reflexivity.
      * rewrite sublist_rec_concat_sort_bounded in r1.
        { rewrite sort_sorted_is_id in r1;
          intuition.
        }
        rewrite r0; reflexivity.
      * rewrite sublist_rec_concat_sort_bounded in r1.
        { rewrite sort_sorted_is_id in r1;
          intuition.
        }
        rewrite r0; reflexivity.
    + match_destr.
      erewrite rtype_meet_compatible_records_domain_eq_r in r1;
        [ | eapply domain_map_rtype_meet₀_diff].
      destruct k; destruct k0; destruct k1; simpl in *;
      intuition.
      * rewrite domain_rec_concat_sort_app_comm in r1.
        rewrite sublist_rec_concat_sort_bounded in r1.
        { rewrite sort_sorted_is_id in r1;
          intuition.
        }
        rewrite r0; reflexivity.
      * rewrite sublist_rec_concat_sort_bounded in r1.
        { rewrite sort_sorted_is_id in r1;
          intuition.
          rewrite r0 in r1; intuition.
        }
        rewrite r0; reflexivity.
      * elim n.
        rewrite <- r1.
        apply rec_concat_sort_sublist_sorted.
        intuition.
      * elim n.
        rewrite <- r1.
        apply rec_concat_sort_sublist_sorted.
        intuition.
      * rewrite <- r1 in n.
        rewrite domain_rec_concat_sort_app_comm in n.
        rewrite sublist_rec_concat_sort_bounded in n.
         { rewrite sort_sorted_is_id in n;
          intuition.
        }
        rewrite r0; reflexivity.
      *  rewrite <- r1 in n.
        rewrite domain_rec_concat_sort_app_comm in n.
        rewrite sublist_rec_concat_sort_bounded in n.
         { rewrite sort_sorted_is_id in n;
          intuition.
        }
         rewrite r0; reflexivity.
      }
  - destruct b; destruct c; simpl; intuition; try first [f_equal; auto || destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial];
      simpl in *; rewrite andb_true_iff in *;
        f_equal;
        solve[apply IHa1; intuition] || solve[apply IHa2; intuition].
  - destruct b; destruct c; simpl; intuition; try first [f_equal; auto || destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial];
      simpl in *; rewrite andb_true_iff in *;
        f_equal;
        solve[apply IHa1; intuition] || solve[apply IHa2; intuition].
  - destruct b0; destruct c; simpl; trivial; try tauto.
    + repeat rewrite andb_true_iff; intuition.
      destruct (rtype_meet_compatible_records_dec k k0 srl srl0); trivial.
    + repeat match_destr; intros.
      split; f_equal.
      * apply brand_join_associative; trivial.
      * apply brand_meet_associative; trivial.
  - destruct b; destruct c; simpl; trivial; intuition.
    + destruct ( rtype_meet_compatible_records_dec k k0 srl srl0); trivial.
    + rewrite join_associative; trivial.
    + rewrite meet_associative; trivial.
Qed.

Corollary rtype_join₀_associative {a b c : rtype₀} :
   wf_rtype₀ a = true ->
   wf_rtype₀ b = true ->
   wf_rtype₀ c = true ->
   rtype_join₀ (rtype_join₀ a b) c = rtype_join₀ a (rtype_join₀ b c).
Proof.
  intros; apply rtype_join₀_meet₀_associative; trivial.
Qed.

Corollary rtype_meet₀_associative {a b c : rtype₀} :
   wf_rtype₀ a = true ->
   wf_rtype₀ b = true ->
   wf_rtype₀ c = true ->
   rtype_meet₀ (rtype_meet₀ a b) c = rtype_meet₀ a (rtype_meet₀ b c).
Proof.
  intros; apply rtype_join₀_meet₀_associative; trivial.
Qed.

Theorem rtype_join_associative : forall a b c,
    rtype_join (rtype_join a b) c = rtype_join a (rtype_join b c).
Proof.
  intros; apply rtype_fequal; 
    destruct a as [a awf];
    destruct b as [b bwf];
    destruct c as [c cwf]; simpl.
  apply rtype_join₀_associative; trivial.
Qed.

Theorem rtype_meet_associative : forall a b c,
    rtype_meet (rtype_meet a b) c = rtype_meet a (rtype_meet b c).
Proof.
  intros; apply rtype_fequal; 
    destruct a as [a awf];
    destruct b as [b bwf];
    destruct c as [c cwf]; simpl.
  apply rtype_meet₀_associative; trivial.
Qed.

Lemma map_rtype_join₀_nil_r l₁ :
      ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
         list (string * rtype₀) :=
         match l1 with
         | nil => nil
         | (s, r) :: srs =>
             match lookup string_dec l2 s with
             | Some r' => (s, rtype_join₀ r r') :: map_rtype_join₀ srs l2
             | None => map_rtype_join₀ srs l2
             end
         end) l₁ nil) = nil.
Proof.
generalize (map_rtype_join₀_domain_subset l₁ nil).
case_eq ( ((fix map_rtype_join₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
             list (string * rtype₀) :=
             match l1 with
             | nil => nil
             | (s0, r1) :: srs =>
                 match lookup string_dec l2 s0 with
                 | Some r' => (s0, rtype_join₀ r1 r') :: map_rtype_join₀ srs l2
                 | None => map_rtype_join₀ srs l2
                 end
             end) l₁ nil)); simpl; trivial.
intros.
destruct (H0 (fst p)); intuition.
Qed.

End mj.
End RTypeMeetJoin.

Section rtype_join_re.

(** since rtype_join does not reduce nicely, we define a bunch of reduction equations
     these will then be added in to the rtype_join autorewrite database
*)

Lemma rtype_nequal {ftype:foreign_type} {br:brand_relation} {τ₁ τ₂:rtype} : τ₁ <> τ₂ -> proj1_sig τ₁ <> proj1_sig τ₂.
Proof.
  intros a b.
  apply a. apply rtype_fequal; trivial.
Qed.

Ltac prover_simpler
  := repeat
       match goal with
         | [H: not (@eq rtype ?A ?B) |- _ ] => apply rtype_nequal in H; simpl in H
         | [H: (@eq rtype ?A ?B) -> False |- _ ] => apply rtype_nequal in H; simpl in H
         | [H: not (eq ?x ?x) |- _ ] => elim H; trivial
         | [H: (eq ?x ?x) -> False |- _ ] => elim H; trivial
       end.

Ltac prover0 := apply rtype_fequal; unfold rtype_join; simpl; trivial.
Ltac prover1 τ := intros; apply rtype_fequal; unfold rtype_join; simpl;
                  let tt := fresh "τ'" in
                  let tpf := fresh "pf'" in 
                  destruct τ as [tt tpf]; destruct tt; simpl;
                  prover_simpler; trivial.

Context {ftype:foreign_type}.
Context {m:brand_relation}.
Lemma rtype_join_Top_l τ :
  rtype_join ⊤ τ = ⊤.
Proof.
  prover1 τ.
Qed.

Lemma rtype_join_Top_r τ : rtype_join τ ⊤ = ⊤.
Proof.
  prover1 τ.
Qed.

Lemma rtype_join_Bottom_r τ : rtype_join τ ⊥ = τ.
Proof.
  prover1 τ.
Qed.

Lemma rtype_join_Bottom_l τ : rtype_join ⊥ τ = τ.
Proof.
  prover1 τ.
Qed.

Lemma rtype_join_Unit_eq : rtype_join Unit Unit = Unit.
Proof.
  prover0.
Qed.

Lemma rtype_join_Unit_neq_l τ: τ <> ⊥ -> τ <> Unit -> rtype_join Unit τ = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Unit_neq_r τ: τ <> ⊥ -> τ <> Unit -> rtype_join τ Unit = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Nat_eq : rtype_join Nat Nat = Nat.
Proof.
  prover0.
Qed.

Lemma rtype_join_Nat_neq_l τ: τ <> ⊥ -> τ <> Nat -> rtype_join Nat τ = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Nat_neq_r τ: τ <> ⊥ -> τ <> Nat -> rtype_join τ Nat = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Float_eq : rtype_join Float Float = Float.
Proof.
  prover0.
Qed.

Lemma rtype_join_Float_neq_l τ: τ <> ⊥ -> τ <> Float -> rtype_join Float τ = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Float_neq_r τ: τ <> ⊥ -> τ <> Float -> rtype_join τ Float = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Bool_eq : rtype_join Bool Bool = Bool.
Proof.
  prover0.
Qed.

Lemma rtype_join_Bool_neq_l τ: τ <> ⊥ -> τ <> Bool -> rtype_join Bool τ = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Bool_neq_r τ: τ <> ⊥ -> τ <> Bool -> rtype_join τ Bool = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_String_eq : rtype_join String String = String.
Proof.
  prover0.
Qed.

Lemma rtype_join_String_neq_l τ: τ <> ⊥ -> τ <> String -> rtype_join String τ = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_String_neq_r τ: τ <> ⊥ -> τ <> String -> rtype_join τ String = ⊤.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_join_Coll_eq τ₁ τ₂ : rtype_join (Coll τ₁) (Coll τ₂) = Coll (rtype_join τ₁ τ₂).
Proof.
  prover0.
Qed.

Lemma rtype_join_Coll_neq_l τ τ₃: τ <> ⊥ -> (forall τ₂, τ <> Coll τ₂) -> rtype_join (Coll τ₃) τ = ⊤.
 Proof.                                                              
   prover1 τ.
   elim (H0 (exist _ τ' pf')); simpl.
   reflexivity.
 Qed.

Lemma rtype_join_Coll_neq_r τ τ₃: τ <> ⊥ -> (forall τ₂, τ <> Coll τ₂) -> rtype_join τ (Coll τ₃) = ⊤.
 Proof.                                                              
   prover1 τ.
   elim (H0 (exist _ τ' pf')); simpl.
   reflexivity.
 Qed.

Fixpoint map_rtype_join l1 l2 :=
  match l1 with
    | nil => nil
    | (s,r)::srs => match lookup string_dec l2 s with
                      | None => map_rtype_join srs l2
                      | Some r' => (s,rtype_join r r')::(map_rtype_join srs l2)
                    end
  end.


Lemma map_rtype_join_sublist_l l₁ l₂ : sublist (domain (map_rtype_join l₁ l₂)) (domain l₁).
Proof.
  Hint Constructors sublist.
  induction l₁; simpl; auto 1.
  destruct a.
  destruct (lookup string_dec l₂ s); simpl; auto.
Qed.

Lemma map_rtype_join_is_sorted l₁ l₂ :
  is_list_sorted ODT_lt_dec (domain l₁) = true
  -> is_list_sorted ODT_lt_dec (domain (map_rtype_join l₁ l₂)) = true.
Proof.
  Hint Constructors StronglySorted.
  repeat rewrite sorted_StronglySorted by apply StringOrder.lt_strorder.
  induction l₁; simpl; trivial.
  destruct a; simpl.
  case_eq l₁; intros; subst. 
  -  simpl in *; destruct (lookup string_dec l₂ s); simpl; auto 1.
  - inversion H0; subst.
    specialize (IHl₁ H2).
    destruct p. unfold fst in *.
    case_eq (lookup string_dec l₂ s); trivial; intros.
    rewrite domain_cons.
    constructor; auto 1.
    unfold fst.
    rewrite map_rtype_join_sublist_l; simpl; trivial.
Qed.
                              
Lemma rtype_join_Rec_eq k₁ rl₁ pf₁ k₂ rl₂ pf₂ :
  rtype_join (Rec k₁ rl₁ pf₁) (Rec k₂ rl₂ pf₂) =
  Rec (record_kind_rtype_join k₁ k₂ rl₁ rl₂)
        (map_rtype_join rl₁ rl₂) (map_rtype_join_is_sorted rl₁ rl₂ pf₁).
Proof.
  prover0.
  unfold rtype_join₀. simpl.
  fold rtype_join₀.
  f_equal.
  - destruct k₁; trivial; destruct k₂; trivial; simpl.
    unfold domain; repeat rewrite map_map; simpl.
    repeat rewrite map_eta_fst_domain.
    trivial.
  - clear k₁ k₂. clear pf₁ pf₂.
    induction rl₁; simpl; trivial.
    rewrite IHrl₁. clear IHrl₁.
    destruct a; simpl.
    case_eq (lookup string_dec rl₂ s); [intros r2 seq | intro sneq].
    + apply lookup_map_some in seq.
      rewrite seq; trivial.
    + apply lookup_map_none in sneq.
      rewrite sneq; trivial.
Qed.

Lemma rtype_join_Rec_neq_l τ k rl pf :
  τ <> ⊥ -> (forall k₂ rl₂ pf₂, τ <> Rec k₂ rl₂ pf₂) -> rtype_join (Rec k rl pf) τ = ⊤.
Proof.
  prover1 τ.
  destruct (from_Rec₀ srl pf') as [srl' [srl'pf [srl'eq srl'receq]]].
  symmetry in srl'receq.
  elim (H0 _ _ _ srl'receq).
Qed.

Lemma rtype_join_Rec_neq_r τ k rl pf :
  τ <> ⊥ -> (forall k₂ rl₂ pf₂, τ <> Rec k₂ rl₂ pf₂) -> rtype_join τ (Rec k rl pf) = ⊤.
Proof.
  prover1 τ.
  destruct (from_Rec₀ srl pf') as [srl' [srl'pf [srl'eq srl'receq]]].
  symmetry in srl'receq.
  elim (H0 _ _ _ srl'receq).
Qed.

Lemma rtype_join_Either_eq τl₁ τr₁ τl₂ τr₂ : rtype_join (Either τl₁ τr₁) (Either τl₂ τr₂) = Either (rtype_join τl₁ τl₂) (rtype_join τr₁ τr₂).
Proof.
  prover0.
Qed.

Lemma rtype_join_Either_neq_l τ τl τr: τ <> ⊥ -> (forall τl₂ τr₂, τ <> Either τl₂ τr₂) -> rtype_join (Either τl τr) τ = ⊤.
 Proof.                                                              
   prover1 τ.
   destruct (Either₀_wf_inv pf') as [pfl pfr].
   elim (H0 (exist _ _ pfl) (exist _ _ pfr)).
   apply rtype_fequal; simpl; trivial.
 Qed.

Lemma rtype_join_Either_neq_r τ τl τr: τ <> ⊥ -> (forall τl₂ τr₂, τ <> Either τl₂ τr₂) -> rtype_join τ (Either τl τr) = ⊤.
 Proof.                                                              
   prover1 τ.
   destruct (Either₀_wf_inv pf') as [pfl pfr].
   elim (H0 (exist _ _ pfl) (exist _ _ pfr)).
   apply rtype_fequal; simpl; trivial.
 Qed.

Lemma rtype_join_Brand_eq x y : rtype_join (Brand x) (Brand y) = Brand (brand_join brand_relation_brands x y).
Proof.
  prover0.
  unfold rtype_join₀.
  simpl.
  fold rtype_join₀.
  rewrite
    brand_join_canon_l,
    brand_join_canon_r,
    is_canon_brands_canon_brands; trivial.
  apply brand_join_is_canon.
Qed.

Lemma rtype_join_Brand_neq_l τ y: τ <> ⊥ -> (forall x, τ <> Brand x) -> rtype_join (Brand y) τ = ⊤.
 Proof.                                                              
   prover1 τ.
   elim (H0 b).
   prover0.
   rewrite is_canon_brands_canon_brands; trivial.
   apply wf_rtype₀_Brand₀; trivial.
 Qed.

Lemma rtype_join_Brand_neq_r τ y: τ <> ⊥ -> (forall x, τ <> Brand x) -> rtype_join τ (Brand y) = ⊤.
 Proof.                                                              
   prover1 τ.
   elim (H0 b).
   prover0.
   rewrite is_canon_brands_canon_brands; trivial.
   apply wf_rtype₀_Brand₀; trivial.
 Qed.

 Lemma rtype_join_Foreign_eq x y : rtype_join (Foreign x) (Foreign y) = Foreign (join x y).
Proof.
  prover0.
Qed.

Lemma rtype_join_Foreign_neq_l τ y: τ <> ⊥ -> (forall x, τ <> Foreign x) -> rtype_join (Foreign y) τ = ⊤.
 Proof.                                                              
   prover1 τ.
   elim (H0 ft).
   prover0.
 Qed.

Lemma rtype_join_Foreign_neq_r τ y: τ <> ⊥ -> (forall x, τ <> Foreign x) -> rtype_join τ (Foreign y) = ⊤.
 Proof.                                                              
   prover1 τ.
   elim (H0 ft).
   prover0.
 Qed.
End rtype_join_re.

Section rtype_meet_re.

(** since rtype_meet does not reduce nicely, we define a bunch of reduction equations
     these will then be added in to the rtype_meet autorewrite database
*)

Ltac prover_simpler
  := repeat
       match goal with
         | [H: not (@eq rtype ?A ?B) |- _ ] => apply rtype_nequal in H; simpl in H
         | [H: (@eq rtype ?A ?B) -> False |- _ ] => apply rtype_nequal in H; simpl in H
         | [H: not (eq ?x ?x) |- _ ] => elim H; trivial
         | [H: (eq ?x ?x) -> False |- _ ] => elim H; trivial
       end.

Ltac prover0 := apply rtype_fequal; unfold rtype_meet; simpl; trivial.
Ltac prover1 τ := intros; apply rtype_fequal; unfold rtype_meet; simpl;
                  let tt := fresh "τ'" in
                  let tpf := fresh "pf'" in 
                  destruct τ as [tt tpf]; destruct tt; simpl;
                  prover_simpler; trivial.

Context {ftype:foreign_type}.
Context {m:brand_relation}.

Lemma rtype_meet_Top_l τ :
  rtype_meet ⊤ τ = τ.
Proof.
  prover1 τ.
Qed.

Lemma rtype_meet_Top_r τ : rtype_meet τ ⊤ = τ.
Proof.
  prover1 τ.
Qed.

Lemma rtype_meet_Bottom_r τ : rtype_meet τ ⊥ = ⊥.
Proof.
  prover1 τ.
Qed.

Lemma rtype_meet_Bottom_l τ : rtype_meet ⊥ τ = ⊥.
Proof.
  prover1 τ.
Qed.

Lemma rtype_meet_Unit_eq : rtype_meet Unit Unit = Unit.
Proof.
  prover0.
Qed.

Lemma rtype_meet_Unit_neq_l τ: τ <> ⊤ -> τ <> Unit -> rtype_meet Unit τ = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Unit_neq_r τ: τ <> ⊤ -> τ <> Unit -> rtype_meet τ Unit = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Nat_eq : rtype_meet Nat Nat = Nat.
Proof.
  prover0.
Qed.

Lemma rtype_meet_Nat_neq_l τ: τ <> ⊤ -> τ <> Nat -> rtype_meet Nat τ = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Nat_neq_r τ: τ <> ⊤ -> τ <> Nat -> rtype_meet τ Nat = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Float_eq : rtype_meet Float Float = Float.
Proof.
  prover0.
Qed.

Lemma rtype_meet_Float_neq_l τ: τ <> ⊤ -> τ <> Float -> rtype_meet Float τ = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Float_neq_r τ: τ <> ⊤ -> τ <> Float -> rtype_meet τ Float = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Bool_eq : rtype_meet Bool Bool = Bool.
Proof.
  prover0.
Qed.

Lemma rtype_meet_Bool_neq_l τ: τ <> ⊤ -> τ <> Bool -> rtype_meet Bool τ = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Bool_neq_r τ: τ <> ⊤ -> τ <> Bool -> rtype_meet τ Bool = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_String_eq : rtype_meet String String = String.
Proof.
  prover0.
Qed.

Lemma rtype_meet_String_neq_l τ: τ <> ⊤ -> τ <> String -> rtype_meet String τ = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_String_neq_r τ: τ <> ⊤ -> τ <> String -> rtype_meet τ String = ⊥.
 Proof.                                                              
   prover1 τ.
 Qed.

Lemma rtype_meet_Coll_eq τ₁ τ₂ : rtype_meet (Coll τ₁) (Coll τ₂) = Coll (rtype_meet τ₁ τ₂).
Proof.
  prover0.
Qed.

Lemma rtype_meet_Coll_neq_l τ τ₃: τ <> ⊤ -> (forall τ₂, τ <> Coll τ₂) -> rtype_meet (Coll τ₃) τ = ⊥.
 Proof.                                                              
   prover1 τ.
   elim (H0 (exist _ τ' pf')); simpl.
   reflexivity.
 Qed.

Lemma rtype_meet_Coll_neq_r τ τ₃: τ <> ⊤ -> (forall τ₂, τ <> Coll τ₂) -> rtype_meet τ (Coll τ₃) = ⊥.
 Proof.                                                              
   prover1 τ.
   elim (H0 (exist _ τ' pf')); simpl.
   reflexivity.
 Qed.

Fixpoint map_rtype_meet l1 l2 :=
  match l1 with
    | nil => nil
    | (s,r)::srs => match lookup string_dec l2 s with
                      | None => (s,r)::map_rtype_meet srs l2
                      | Some r' => (s,rtype_meet r r')::(map_rtype_meet srs l2)
                    end
  end.

Lemma map_rtype_meet_domain r srl:
  domain (map_rtype_meet r srl) = domain r.
Proof.
  induction r; simpl; [intuition|].
  destruct a; simpl.
  case_eq (lookup string_dec srl s); [intros t teq|intuition]; simpl;
  rewrite IHr; trivial.
Qed.

  Lemma NoDup_map_rtype_meet_lookup_diff {r₁ r₂} :
      NoDup (domain r₁) ->  
      NoDup (domain r₂) ->
      NoDup (domain
               ((map_rtype_meet r₁ r₂) ++ (lookup_diff string_dec r₂ r₁))).
  Proof.
      intros.
      rewrite domain_app, map_rtype_meet_domain.
      apply NoDup_app; auto.
      - symmetry; apply lookup_diff_disjoint.
      - apply NoDup_lookup_diff; auto.
  Qed.

  Lemma map_rtype_meet_sublist_l l₁ l₂ : sublist (domain (map_rtype_meet l₁ l₂)) (domain l₁).
Proof.
  Hint Constructors sublist.
  induction l₁; simpl; auto 1.
  destruct a.
  destruct (lookup string_dec l₂ s); simpl; auto.
Qed.

Lemma map_rtype_meet_eq
      (rl₁ rl₂ : list (string * rtype)) :
   (fix map_rtype_meet₀ (l1 l2 : list (string * rtype₀)) {struct l1} :
      list (string * rtype₀) :=
      match l1 with
      | nil => nil
      | (s, r) :: srs =>
          match lookup string_dec l2 s with
          | Some r' => (s, rtype_meet₀ r r') :: map_rtype_meet₀ srs l2
          | None => (s, r) :: map_rtype_meet₀ srs l2
          end
      end)
     (map
        (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
         (fst x, proj1_sig (snd x))) rl₁)
     (map
        (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
         (fst x, proj1_sig (snd x))) rl₂) =
   map
     (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
        (fst x, proj1_sig (snd x))) (map_rtype_meet rl₁ rl₂).
Proof.
  induction rl₁; simpl; trivial.
  rewrite IHrl₁.
  destruct a; simpl in *.
  case_eq (lookup string_dec rl₂ s ); [intros ? eqq | intros eqq].
  - apply lookup_map_some in eqq. rewrite eqq.
    reflexivity.
  - apply lookup_map_none in eqq. rewrite eqq.
    reflexivity.
Qed.

  
Lemma rtype_meet_Rec_eq k₁ rl₁ pf₁ k₂ rl₂ pf₂ :
  rtype_meet (Rec k₁ rl₁ pf₁) (Rec k₂ rl₂ pf₂) =
  if rtype_meet_compatible_records_dec k₁ k₂ rl₁ rl₂
    then
      Rec (record_kind_rtype_meet k₁ k₂)
          (rec_concat_sort (map_rtype_meet rl₁ rl₂) (lookup_diff string_dec rl₂ rl₁)) (drec_concat_sort_sorted _ _)
   else ⊥.
Proof.
  prover0.
  unfold rtype_meet₀; simpl; fold rtype_meet₀.
destruct (rtype_meet_compatible_records_dec k₁ k₂
         (map
            (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
             (fst x, proj1_sig (snd x))) rl₁)
         (map
            (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
               (fst x, proj1_sig (snd x))) rl₂));
    destruct (rtype_meet_compatible_records_dec k₁ k₂ rl₁ rl₂).
  - simpl.
    f_equal.
    clear k₁ k₂ r r0. clear pf₁ pf₂.
    unfold rec_concat_sort.
    rewrite map_rec_sort by reflexivity.
    f_equal.
    rewrite map_app.
    f_equal.
    + apply map_rtype_meet_eq.
    + rewrite <- map_lookup_diff by reflexivity.
      f_equal.
      apply lookup_diff_same_domain2.
      unfold domain.
      rewrite map_map; simpl.
      reflexivity.
  - elim n.
    erewrite rtype_meet_compatible_records_domain_eq_l,
    rtype_meet_compatible_records_domain_eq_r in r; eauto;
    unfold domain; try rewrite map_map; try reflexivity.
  - elim n.
    erewrite rtype_meet_compatible_records_domain_eq_l,
    rtype_meet_compatible_records_domain_eq_r; eauto;
    unfold domain; try rewrite map_map; try reflexivity.
  - reflexivity.
Qed.

Lemma rtype_meet_Rec_neq_l τ k rl pf :
  τ <> ⊤ -> (forall k₂ rl₂ pf₂, τ <> Rec k₂ rl₂ pf₂) -> rtype_meet (Rec k rl pf) τ = ⊥.
Proof.
  prover1 τ.
  destruct (from_Rec₀ srl pf') as [srl' [srl'pf [srl'eq srl'receq]]].
  symmetry in srl'receq.
  elim (H0 _ _ _ srl'receq).
Qed.

Lemma rtype_meet_Rec_neq_r τ k rl pf :
  τ <> ⊤ -> (forall k₂ rl₂ pf₂, τ <> Rec k₂ rl₂ pf₂) -> rtype_meet τ (Rec k rl pf) = ⊥.
Proof.
  prover1 τ.
  destruct (from_Rec₀ srl pf') as [srl' [srl'pf [srl'eq srl'receq]]].
  symmetry in srl'receq.
  elim (H0 _ _ _ srl'receq).
Qed.

Lemma rtype_meet_Either_eq τl₁ τr₁ τl₂ τr₂ : rtype_meet (Either τl₁ τr₁) (Either τl₂ τr₂) = Either (rtype_meet τl₁ τl₂) (rtype_meet τr₁ τr₂).
Proof.
  prover0.
Qed.

Lemma rtype_meet_Either_neq_l τ τl τr: τ <> ⊤ -> (forall τl₂ τr₂, τ <> Either τl₂ τr₂) -> rtype_meet (Either τl τr) τ = ⊥.
 Proof.                                                              
   prover1 τ.
   destruct (Either₀_wf_inv pf') as [pfl pfr].
   elim (H0 (exist _ _ pfl) (exist _ _ pfr)).
   apply rtype_fequal; simpl; trivial.
 Qed.

Lemma rtype_meet_Either_neq_r τ τl τr: τ <> ⊤ -> (forall τl₂ τr₂, τ <> Either τl₂ τr₂) -> rtype_meet τ (Either τl τr) = ⊥.
 Proof.                                                              
   prover1 τ.
   destruct (Either₀_wf_inv pf') as [pfl pfr].
   elim (H0 (exist _ _ pfl) (exist _ _ pfr)).
   apply rtype_fequal; simpl; trivial.
 Qed.

Lemma rtype_meet_Brand_eq x y : rtype_meet (Brand x) (Brand y) = Brand (brand_meet brand_relation_brands x y).
Proof.
  prover0.
  unfold rtype_meet₀; simpl; fold rtype_meet₀.
  rewrite
    brand_meet_canon_l,
    brand_meet_canon_r,
    is_canon_brands_canon_brands; trivial.
  apply brand_meet_is_canon.
Qed.

Lemma rtype_meet_Brand_neq_l τ y: τ <> ⊤ -> (forall x, τ <> Brand x) -> rtype_meet (Brand y) τ = ⊥.
 Proof.                                                              
   prover1 τ.
   elim (H0 b).
   prover0.
   rewrite is_canon_brands_canon_brands; trivial.
   apply wf_rtype₀_Brand₀; trivial.
 Qed.

Lemma rtype_meet_Brand_neq_r τ y: τ <> ⊤ -> (forall x, τ <> Brand x) -> rtype_meet τ (Brand y) = ⊥.
 Proof.                                                              
   prover1 τ.
   elim (H0 b).
   prover0.
   rewrite is_canon_brands_canon_brands; trivial.
   apply wf_rtype₀_Brand₀; trivial.
 Qed.

 Lemma rtype_meet_Foreign_eq x y : rtype_meet (Foreign x) (Foreign y) = Foreign (meet x y).
 Proof.
   prover0.
 Qed.

Lemma rtype_meet_Foreign_neq_l τ y: τ <> ⊤ -> (forall x, τ <> Foreign x) -> rtype_meet (Foreign y) τ = ⊥.
 Proof.                                                              
   prover1 τ.
   elim (H0 ft).
   prover0.
 Qed.

Lemma rtype_meet_Foreign_neq_r τ y: τ <> ⊤ -> (forall x, τ <> Foreign x) -> rtype_meet τ (Foreign y) = ⊥.
 Proof.                                                              
   prover1 τ.
   elim (H0 ft).
   prover0.
 Qed.

End rtype_meet_re.

Hint Rewrite @rtype_join_Top_l @rtype_join_Top_r: rtype_join.
Hint Rewrite @rtype_join_Bottom_l @rtype_join_Bottom_r: rtype_join.
Hint Rewrite @rtype_join_Unit_eq : rtype_join.
Hint Rewrite @rtype_join_Unit_neq_l @rtype_join_Unit_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Nat_eq : rtype_join.
Hint Rewrite @rtype_join_Nat_neq_l @rtype_join_Nat_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Float_eq : rtype_join.
Hint Rewrite @rtype_join_Float_neq_l @rtype_join_Float_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Bool_eq : rtype_join.
Hint Rewrite @rtype_join_Bool_neq_l @rtype_join_Bool_neq_r using discriminate: rattype_join.
Hint Rewrite @rtype_join_String_eq : rtype_join.
Hint Rewrite @rtype_join_String_neq_l @rtype_join_String_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Coll_eq : rtype_join.
Hint Rewrite @rtype_join_Coll_neq_l @rtype_join_Coll_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Rec_eq : rtype_join.
Hint Rewrite @rtype_join_Rec_neq_l @rtype_join_Rec_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Either_eq : rtype_join.
Hint Rewrite @rtype_join_Either_neq_l @rtype_join_Either_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Brand_eq : rtype_join.
Hint Rewrite @rtype_join_Brand_neq_l @rtype_join_Brand_neq_r using discriminate: rtype_join.
Hint Rewrite @rtype_join_Foreign_eq : rtype_join.
Hint Rewrite @rtype_join_Foreign_neq_l @rtype_join_Foreign_neq_r using discriminate: rtype_join.


Hint Rewrite @rtype_meet_Top_l @rtype_meet_Top_r: rtype_meet.
Hint Rewrite @rtype_meet_Bottom_l @rtype_meet_Bottom_r: rtype_meet.
Hint Rewrite @rtype_meet_Unit_eq : rtype_meet.
Hint Rewrite @rtype_meet_Unit_neq_l @rtype_meet_Unit_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Nat_eq : rtype_meet.
Hint Rewrite @rtype_meet_Nat_neq_l @rtype_meet_Nat_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Float_eq : rtype_meet.
Hint Rewrite @rtype_meet_Float_neq_l @rtype_meet_Float_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Bool_eq : rtype_meet.
Hint Rewrite @rtype_meet_Bool_neq_l @rtype_meet_Bool_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_String_eq : rtype_meet.
Hint Rewrite @rtype_meet_String_neq_l @rtype_meet_String_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Coll_eq : rtype_meet.
Hint Rewrite @rtype_meet_Coll_neq_l @rtype_meet_Coll_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Rec_eq : rtype_meet.
Hint Rewrite @rtype_meet_Rec_neq_l @rtype_meet_Rec_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Either_eq : rtype_meet.
Hint Rewrite @rtype_meet_Either_neq_l @rtype_meet_Either_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Brand_eq : rtype_meet.
Hint Rewrite @rtype_meet_Brand_neq_l @rtype_meet_Brand_neq_r using discriminate: rtype_meet.
Hint Rewrite @rtype_meet_Foreign_eq : rtype_meet.
Hint Rewrite @rtype_meet_Foreign_neq_l @rtype_meet_Foreign_neq_r using discriminate: rtype_meet.

