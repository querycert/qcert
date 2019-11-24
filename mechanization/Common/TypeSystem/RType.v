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
Require Import Sorting.
Require Import Eqdep_dec.
Require Import Bool.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignType.

Section RType.
  (* Possibly non-canonical relational types *)

  Inductive record_kind : Set
    :=
    (** open records allow width subtyping: they can have additional fields not in the type description *)
    | Open
    (** closed records do not allow width subtyping.  They must have exactly the specified fields. *)
    | Closed.

  Global Instance record_kind_eqdec : EqDec record_kind eq.
  intros x y.
  change ({x=y} + {x<>y}).
  decide equality.
  Defined.

  Section rtypes₀.

    (** Syntax of types. Note that there is no guarantee yet that records are well formed. i.e., having distinct fields. *)

    Context {ftype:foreign_type}.
    Unset Elimination Schemes.

    Inductive rtype₀ : Set :=
    | Bottom₀ : rtype₀
    | Top₀ : rtype₀
    | Unit₀ : rtype₀
    | Nat₀ : rtype₀
    | Float₀ : rtype₀
    | Bool₀ : rtype₀
    | String₀ : rtype₀
    | Coll₀ (r:rtype₀) : rtype₀
    | Rec₀ (k:record_kind) (srl:list (string* rtype₀)) : rtype₀
    | Either₀ (tl tr:rtype₀) : rtype₀
    | Arrow₀ (tin tout : rtype₀) : rtype₀
    | Brand₀ : brands -> rtype₀
    | Foreign₀ (ft:foreign_type_type) : rtype₀.

    Set Elimination Schemes.

    Notation "⊥₀" := Bottom₀.
    Notation "⊤₀" := Top₀.

    Definition rtype₀_rect (P : rtype₀ -> Type)
               (ftop : P ⊤₀)
               (fbottom : P ⊥₀)
               (funit : P Unit₀)
               (fnat : P Nat₀)
               (ffloat : P Float₀)
               (fbool : P Bool₀)
               (fstring : P String₀)
               (fcol : forall t : rtype₀, P t -> P (Coll₀ t))
               (frec : forall (k:record_kind) (r : list (string * rtype₀)), Forallt (fun ab => P (snd ab)) r -> P (Rec₀ k r))
               (feither : forall l r, P l -> P r -> P (Either₀ l r))
               (farrow : forall tin tout, P tin -> P tout -> P (Arrow₀ tin tout))
               (fbrand : forall b, P (Brand₀ b))
               (fforeign : forall ft, P (Foreign₀ ft))
      :=
        fix F (t : rtype₀) : P t :=
      match t as t0 return (P t0) with
        | ⊤₀ => ftop
        | ⊥₀ => fbottom
        | Unit₀ => funit
        | Nat₀ => fnat
        | Float₀ => ffloat
        | Bool₀ => fbool
        | String₀ => fstring
        | Coll₀ x => fcol x (F x)
        | Rec₀ k x => frec k x ((fix Frec (r : list (string * rtype₀)) : Forallt (fun ab => P (snd ab)) r :=
                               match r as c0 with
                                 | nil => Forallt_nil _
                                 | cons sd c0 => @Forallt_cons _ (fun ab => P (snd ab)) sd c0 (F (snd sd)) (Frec c0)
                               end) x)
        | Either₀ l r => feither l r (F l) (F r)
        | Arrow₀ tin tout => farrow tin tout (F tin) (F tout)
        | Brand₀ b => fbrand b
        | Foreign₀ ft => fforeign ft
      end.

    Definition rtype₀_ind (P : rtype₀ -> Prop)
               (ftop : P ⊤₀)
               (fbottom : P ⊥₀)
               (funit : P Unit₀)
               (fnat : P Nat₀)
               (ffloat : P Float₀)
               (fbool : P Bool₀)
               (fstring : P String₀)
               (fcol : forall t : rtype₀, P t -> P (Coll₀ t))
               (frec : forall (k:record_kind) (r : list (string * rtype₀)), Forall (fun ab => P (snd ab)) r -> P (Rec₀ k r))
               (feither : forall l r, P l -> P r -> P (Either₀ l r))
               (farrow : forall tin tout, P tin -> P tout -> P (Arrow₀ tin tout))
               (fbrand : forall b, P (Brand₀ b))
               (fforeign : forall ft, P (Foreign₀ ft))
      :=
        fix F (t : rtype₀) : P t :=
      match t as t0 return (P t0) with
        | ⊤₀ => ftop
        | ⊥₀ => fbottom
        | Unit₀ => funit
        | Nat₀ => fnat
        | Float₀ => ffloat
        | Bool₀ => fbool
        | String₀ => fstring
        | Coll₀ x => fcol x (F x)
        | Rec₀ k x => frec k x ((fix Frec (r : list (string * rtype₀)) : Forall (fun ab => P (snd ab)) r :=
                               match r as c0 with
                                 | nil => Forall_nil _
                                 | cons sd c0 => @Forall_cons _ (fun ab => P (snd ab)) sd c0 (F (snd sd)) (Frec c0)
                               end) x)
        | Either₀ l r => feither l r (F l) (F r)
        | Arrow₀ tin tout => farrow tin tout (F tin) (F tout)
        | Brand₀ b => fbrand b
        | Foreign₀ ft => fforeign ft
      end.

    Definition rtype₀_rec (P:rtype₀->Set) := rtype₀_rect P.

    (* Equality is decidable for rtype₀ *)
    Global Instance rtype₀_eqdec : EqDec rtype₀ eq.
    Proof.
      red; unfold equiv, complement.
      induction x; destruct y;
      try solve[right; inversion 1]; try solve[left; trivial].
      - (* Col *)
        destruct (IHx y) as [e|e].
        + left; f_equal; trivial.
        + right; intro n. apply e;inversion n; trivial.
      - (* Rec *)
        destruct (k == k0); unfold equiv, complement in *.
        + destruct (list_Forallt_eq_dec r srl); subst; auto.
          * apply (forallt_impl H).
            apply forallt_weaken; clear; intros.
            destruct x; destruct y; simpl in *.
            apply pair_eq_dec; eauto.
            apply string_dec.
          * right; inversion 1; auto.
        + right; inversion 1; auto.
      - destruct (IHx1 y1); unfold equiv, complement in *.
        + destruct (IHx2 y2); unfold equiv, complement in *.
          * left; subst; trivial.
          * right; inversion 1; eauto.
        +  right; inversion 1; eauto.
      - destruct (IHx1 y1); unfold equiv, complement in *.
        + destruct (IHx2 y2); unfold equiv, complement in *.
          * left; subst; trivial.
          * right; inversion 1; eauto.
        +  right; inversion 1; eauto.
      - destruct (b == b0); unfold equiv, complement in *;
          [left | right]; congruence.
      - destruct (foreign_type_dec ft ft0).
        + left; f_equal; apply e.
        + right; inversion 1; congruence.
    Defined.

  End rtypes₀.
  Notation "⊥₀" := Bottom₀.
  Notation "⊤₀" := Top₀.
  
  Section well_formed_rtypes.
    Context {ftype:foreign_type}.
    Context {br:brand_relation}.
    
    Fixpoint wf_rtype₀ (τ:rtype₀): bool
      := match τ with
           | Coll₀ τ' => wf_rtype₀ τ'
           | Rec₀ oc srl => is_list_sorted ODT_lt_dec (domain srl)
                                           && forallb (fun ab => wf_rtype₀ (snd ab)) srl
           | Either₀ τl τr => wf_rtype₀ τl && wf_rtype₀ τr
           | Arrow₀ τin τout => wf_rtype₀ τin && wf_rtype₀ τout
           | Brand₀ b => if is_canon_brands_dec brand_relation_brands b then true else false
           | _ => true
         end.

    Definition rtype : Set := {τ₀:rtype₀ | wf_rtype₀ τ₀ = true}.

    Lemma wf_rtype₀_ext {τ₀:rtype₀} (pf1 pf2:wf_rtype₀ τ₀ = true) : pf1 = pf2.
    Proof.
      apply UIP_dec; apply bool_dec.
    Defined.
    
    Lemma rtype_ext {τ₀} (wfτ1 wfτ2:wf_rtype₀ τ₀ = true) :
      (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ₀ wfτ1) =
      (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ₀ wfτ2).
    Proof.
      f_equal. apply wf_rtype₀_ext.
    Defined.

    Lemma rtype_fequal {τ₁ τ₂:rtype} : proj1_sig τ₁ = proj1_sig τ₂ -> τ₁ = τ₂.
    Proof.
      destruct τ₁; destruct τ₂; simpl; intros; subst.
      apply rtype_ext.
    Qed.

    Lemma rtype_nequal {τ₁ τ₂:rtype} : τ₁ <> τ₂ -> proj1_sig τ₁ <> proj1_sig τ₂.
    Proof.
      intros a b.
      apply a. apply rtype_fequal; trivial.
    Qed.

    Lemma map_rtype_fequal r1 r2 :
      map
        (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x, proj1_sig (snd x))) r1 =
      map
        (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x, proj1_sig (snd x))) r2 ->
      r1 = r2.
    Proof.
      revert r2.
      induction r1; destruct r2; simpl; trivial; try discriminate.
      inversion 1.
      f_equal; auto.
      destruct a; destruct p; simpl in *; subst. f_equal.
      apply rtype_fequal; auto.
    Qed.

    Lemma map_rtype_single_rec_fequal a τ r :
      (a, proj1_sig τ)::nil =
      map
        (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x, proj1_sig (snd x))) r ->
      ((a, τ)::nil) = r.
    Proof.
      assert ((a, proj1_sig τ)::nil =
              map (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                     (fst x, proj1_sig (snd x))) ((a, τ)::nil)) by reflexivity.
      rewrite H.
      apply map_rtype_fequal.
    Qed.

    Global Instance rtype_eq_dec : EqDec rtype eq.
    Proof.
      red; unfold equiv, complement.
      intros [x₀ xwf] [y₀ ywf].
      destruct (x₀ == y₀); unfold equiv, complement in *.
      - left. apply rtype_fequal; simpl; trivial.
      - right; congruence.
    Defined.

    (** Lifted versions of the type constructors *)
    (** This is the main type system, and always carries a proofs that the records are well formed *)
    Program Definition Bottom : rtype := Bottom₀.
    Program Definition Top : rtype := Top₀.
    Program Definition Unit : rtype := Unit₀.
    Program Definition Nat : rtype := Nat₀.
    Program Definition Float : rtype := Float₀.
    Program Definition Bool : rtype := Bool₀.
    Program Definition String : rtype := String₀.
    Definition Coll (τ:rtype): rtype := 
      exist _ (Coll₀ (proj1_sig τ)) (proj2_sig τ).

    Program Definition Either (τl τr:rtype) : rtype :=
      exist _ (Either₀ (proj1_sig τl) (proj1_sig τr)) _.
    Next Obligation.
      rewrite (proj2_sig τl), (proj2_sig τr).
      reflexivity.
    Defined.

    Program Definition Arrow (τl τr:rtype) : rtype :=
      exist _ (Arrow₀ (proj1_sig τl) (proj1_sig τr)) _.
    Next Obligation.
      rewrite (proj2_sig τl), (proj2_sig τr).
      reflexivity.
    Defined.

    Program Definition Foreign (ft:foreign_type_type) : rtype
      := Foreign₀ ft.

    Program Definition Rec
            (k:record_kind)
            (srl:list (string* rtype))
            (pf_sorted:is_list_sorted ODT_lt_dec (domain srl) = true) : rtype
      := Rec₀ k (map (fun x => (fst x, proj1_sig (snd x))) srl).
    Next Obligation.
      unfold domain in *.
      rewrite map_map; simpl.
      rewrite (map_eq (g:=fst)) by (rewrite Forall_forall; trivial).
      rewrite andb_true_iff; split.
      - apply pf_sorted.
      - rewrite forallb_map; simpl.
        rewrite forallb_forall.
        intros [? [??]] ?; simpl; trivial.
    Defined.

    Program Definition Brand b : rtype := Brand₀ (canon_brands brand_relation_brands b).
    Next Obligation.
      match_destr.
      elim n.
      apply canon_brands_is_canon_brands.
    Defined.

    Global Instance Brand_equiv_proper :
      Proper (equiv_brands brand_relation_brands ==> eq) (Brand).
    Proof.
      unfold Proper, respectful; intros.
      apply rtype_fequal; simpl.
      rewrite H; trivial.
    Qed.

    Notation "⊥" := Bottom.
    Notation "⊤" := Top.

    Definition Option τ := Either τ Unit.

    (* (derived) induction principle for rtype.  Between the "smart"
       constructors, and this eliminator, there should be no need to
       operate on the underlying rtype₀.  Unfortunately, we do lose
       explicit pattern matching (it can still be written as a call to
       this induction principle) *)

    Theorem rtype_rect (P : rtype -> Type)
            (ftop : P ⊤)
            (fbottom : P ⊥)
            (funit : P Unit)
            (fnat : P Nat)
            (ffloat : P Float)
            (fbool : P Bool)
            (fstring : P String)
            (fcol : forall t : rtype, P t -> P (Coll t))
            (frec : forall (k:record_kind) (srl : list (string * rtype))
                           (pf:is_list_sorted ODT_lt_dec (domain srl) = true),
                      Forallt (fun ab => P (snd ab)) srl -> P (Rec k srl pf))
            (feither : forall (τl τr:rtype), P τl -> P τr -> P (Either τl τr))
            (farrow : forall (τin τout:rtype), P τin -> P τout -> P (Arrow τin τout))
            (fbrand : forall b, P (Brand b))
            (fforeign : forall ft, P (Foreign ft))
      :
      forall (τ:rtype), P τ.
    Proof.
      Hint Constructors Forallt.
      destruct τ as [τ₀ wfτ].
      revert wfτ. (* ftop fbottom funit fnat fbool fstring fcol frec. *)
      unfold Top, Bottom, Unit, Nat, Float, Bool, String, Coll, Rec, Either, Arrow in *.
      (* Ltac r_ext := solve [erewrite (rtype_ext); eauto]. *)
      induction τ₀; simpl; intros.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - specialize (fcol _ (IHτ₀ wfτ)).
        erewrite rtype_ext; eauto.
      - revert frec wfτ X; clear. intros frec.
        intros.
        assert (srlpf:{srl: list (string * rtype) | (map
                                                       (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                          (fst x, proj1_sig (snd x))) srl) = r}).
        + clear P X frec. rewrite andb_true_iff, forallb_forall in wfτ.
          destruct wfτ as [iss fb].
          revert iss fb.
          induction r; intros.
          * exists nil; simpl; trivial.
                   * rewrite domain_cons, is_list_sorted_cons in iss.
                     destruct iss as [iss isa].
                     destruct IHr as [srl srlpf]; intuition.
                     specialize (fb a).
                     simpl in fb; intuition.
                     exists ((fst a ,(exist _ (snd a) H1))::srl).
                     destruct a; simpl. congruence. 
                   + destruct srlpf as [srl srleq].
                     assert (dreq:domain srl = domain r).
                     rewrite <- srleq; simpl; unfold domain.
                     rewrite map_map. simpl. apply map_eq; apply Forall_forall; auto.     
                     assert (pfs:is_list_sorted ODT_lt_dec (domain srl) = true).
                     rewrite dreq; rewrite andb_true_iff in wfτ; intuition.
                     assert (pff:Forallt (fun ab : string * rtype => P (snd ab)) srl).
                     revert X. rewrite <- srleq. clear.
                     induction srl; simpl; eauto.
                     destruct a; destruct r; simpl.
                     inversion 1; subst; eauto.
                     specialize (frec k srl pfs pff).
                     destruct srleq.
                     erewrite (rtype_ext); eapply frec.
    - generalize wfτ; intros.
      rewrite andb_true_iff in wfτ. destruct wfτ as [wfτ1 wfτ2].
      specialize (feither _ _ (IHτ₀1 wfτ1) (IHτ₀2 wfτ2)).
      erewrite rtype_ext; eauto. 
    - generalize wfτ; intros.
      rewrite andb_true_iff in wfτ. destruct wfτ as [wfτ1 wfτ2].
      specialize (farrow _ _ (IHτ₀1 wfτ1) (IHτ₀2 wfτ2)).
      erewrite rtype_ext; eauto. 
    - revert fbrand b wfτ. clear; intros.
      assert (isc:is_canon_brands brand_relation_brands b)
             by match_destr_in wfτ.
      replace (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Brand₀ b) wfτ) with (Brand b); trivial.
      apply rtype_fequal; simpl.
      rewrite is_canon_brands_canon_brands; trivial.
    - specialize (fforeign ft).
      erewrite rtype_ext.
      eauto.
    Defined.
    
    Theorem rtype_ind (P : rtype -> Prop)
            (ftop : P ⊤)
            (fbottom : P ⊥)
            (funit : P Unit)
            (fnat : P Nat)
            (ffloat : P Float)
            (fbool : P Bool)
            (fstring : P String)
            (fcol : forall t : rtype, P t -> P (Coll t))
            (frec : forall (k:record_kind) (srl : list (string * rtype))
                           (pf:is_list_sorted ODT_lt_dec (domain srl) = true),
                      Forall (fun ab => P (snd ab)) srl -> P (Rec k srl pf))
            (feither : forall (τl τr:rtype), P τl -> P τr -> P (Either τl τr))
            (farrow : forall (τin τout:rtype), P τin -> P τout -> P (Arrow τin τout))
            (fbrand : forall b, P (Brand b))
            (fforeign : forall ft, P (Foreign ft)) :
      forall (τ:rtype), P τ.
    Proof.
      Hint Constructors Forallt.
      destruct τ as [τ₀ wfτ].
      revert wfτ. (* ftop fbottom funit fnat fbool fstring fcol frec. *)
      unfold Top, Bottom, Unit, Nat, Float, Bool, String, Coll, Rec in *.
      (* Ltac r_ext := solve [erewrite (rtype_ext); eauto]. *)
      induction τ₀; simpl; intros.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - erewrite rtype_ext; eauto.
      - specialize (fcol _ (IHτ₀ wfτ)).
        erewrite rtype_ext; eauto.
      - revert frec wfτ H; clear. intros frec.
        intros.
        assert (srlpf:{srl: list (string * rtype) | (map
                                                       (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                          (fst x, proj1_sig (snd x))) srl) = r}).
        + clear P H frec. rewrite andb_true_iff, forallb_forall in wfτ.
          destruct wfτ as [iss fb].
          revert iss fb.
          induction r; intros.
          * exists nil; simpl; trivial.
                   * rewrite domain_cons, is_list_sorted_cons in iss.
                     destruct iss as [iss isa].
                     destruct IHr as [srl srlpf]; intuition.
                     specialize (fb a).
                     simpl in fb; intuition.
                     exists ((fst a ,(exist _ (snd a) H1))::srl).
                     destruct a; simpl. congruence. 
                   + destruct srlpf as [srl srleq].
                     assert (dreq:domain srl = domain r).
                     rewrite <- srleq; simpl; unfold domain.
                     rewrite map_map. simpl. apply map_eq; apply Forall_forall; auto.     
                     assert (pfs:is_list_sorted ODT_lt_dec (domain srl) = true).
                     rewrite dreq; rewrite andb_true_iff in wfτ; intuition.
                     assert (pff:Forall (fun ab : string * rtype => P (snd ab)) srl).
                     revert H. rewrite <- srleq. clear.
                     induction srl; simpl; eauto.
                     destruct a; destruct r; simpl.
                     inversion 1; subst; eauto.
                     specialize (frec k srl pfs pff).
                     destruct srleq.
                     erewrite (rtype_ext); eapply frec.
    - generalize wfτ; intros.
      rewrite andb_true_iff in wfτ. destruct wfτ as [wfτ1 wfτ2].
      specialize (feither _ _ (IHτ₀1 wfτ1) (IHτ₀2 wfτ2)).
      erewrite rtype_ext; eauto.
    - generalize wfτ; intros.
      rewrite andb_true_iff in wfτ. destruct wfτ as [wfτ1 wfτ2].
      specialize (farrow _ _ (IHτ₀1 wfτ1) (IHτ₀2 wfτ2)).
      erewrite rtype_ext; eauto.
    - revert fbrand b wfτ. clear; intros.
      assert (isc:is_canon_brands brand_relation_brands b)
             by match_destr_in wfτ.
      replace (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Brand₀ b) wfτ) with (Brand b); trivial.
      apply rtype_fequal; simpl.
      rewrite is_canon_brands_canon_brands; trivial.
    - specialize (fforeign ft).
      erewrite rtype_ext.
      eauto.
    Defined.

    Definition rtype_rec (P:rtype->Set) := rtype_rect P.

    Lemma wf_rtype₀_kind_irrel k₁ k₂ l :
      wf_rtype₀ (Rec₀ k₁ l) = wf_rtype₀ (Rec₀ k₂ l).
    Proof.
      reflexivity.
    Qed.

    Lemma wf_rtype₀_Brand₀ b :
      wf_rtype₀ (Brand₀ b) = true ->
      is_canon_brands brand_relation_brands b.
    Proof.
      simpl.
      match_destr.
    Qed.

    Lemma brand_ext b pf : exist _ (Brand₀ b) pf = Brand b.
    Proof.
      apply rtype_fequal; simpl in *.
      match_destr_in pf.
      rewrite is_canon_brands_canon_brands; trivial.
    Qed.
                             
    Lemma wf_rtype₀_cons_tail {k} {a r} : 
      wf_rtype₀ (Rec₀ k (a::r)) = true ->
      wf_rtype₀ (Rec₀ k r) = true.
    Proof.
      simpl.
      repeat rewrite andb_true_iff.
      intuition.
      destruct (domain r); intuition.
      destruct (StringOrder.lt_dec (fst a) s); intuition.
    Defined.

    Lemma wf_rtype₀_cons_lt {k s r srl s' r'} : 
      wf_rtype₀ (Rec₀ k ((s, r) :: srl)) = true ->
      lookup string_dec srl s' = Some r' ->
      ODT_lt s s'.
    Proof.
      unfold wf_rtype₀. rewrite andb_true_iff.
      intros [isl _].
      apply is_list_sorted_Sorted_iff in isl.
      apply Sorted_StronglySorted in isl; [|eapply StringOrder.lt_strorder].
      simpl in isl. inversion isl. subst.
      rewrite Forall_forall in H2.
      specialize (H2 s').
      intros los.
      apply lookup_in in los. apply in_dom in los.
      simpl.
      auto.
    Qed.

    Lemma wf_rtype₀_cons_nin {k s r srl} : 
      wf_rtype₀ (Rec₀ k ((s, r) :: srl)) = true -> lookup string_dec srl s = None.
    Proof.
      unfold wf_rtype₀. rewrite andb_true_iff.
      intros [isl _].
      apply is_list_sorted_NoDup in isl; [|eapply StringOrder.lt_strorder].
      inversion isl; subst.
      eapply lookup_nin_none; auto.
    Defined.

    Lemma wf_rtype₀_cons_wf {k s r srl} : 
      wf_rtype₀ (Rec₀ k ((s, r) :: srl)) = true -> 
      wf_rtype₀ r = true.
    Proof.
      simpl; repeat rewrite andb_true_iff; intuition.
    Qed.

  End well_formed_rtypes.
  Notation "⊥" := Bottom.
  Notation "⊤" := Top.

  Ltac equalizer := 
    repeat match goal with 
             | [H:(@eq rtype₀ (proj1_sig _) (proj1_sig _)) |- _] => apply rtype_fequal in H
             | [H: map
                     (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                        (fst x, proj1_sig (snd x))) _ =
                   map
                     (fun x' : string * {τ₀' : rtype₀ | wf_rtype₀ τ₀' = true} =>
                        (fst x', proj1_sig (snd x'))) _ |- _] => apply map_rtype_fequal in H
           end.

  Lemma to_Rec {ftype:foreign_type} {br:brand_relation} k l pf :
    exists pf2, 
      exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true)
            (Rec₀
               k (map
                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                     (fst x, proj1_sig (snd x))) l)) pf 
      = Rec k l pf2.
  Proof.
    unfold Rec.
    generalize pf. intros pf'.
    simpl in pf. rewrite andb_true_iff in pf.
    unfold domain in pf; rewrite map_map in pf; simpl in pf.
    destruct pf as [isl ?].
    exists isl. 
    apply rtype_ext.
  Qed.

  Lemma from_Rec₀ {ftype:foreign_type} {br:brand_relation} {k} (l:list (string * rtype₀)) (pf : wf_rtype₀ (Rec₀ k l) = true) :
    {l' | exists pf',
          l = 
          (map
             (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                (fst x, proj1_sig (snd x))) l') 
          /\ Rec k l' pf' = exist  (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Rec₀ k l) pf}.
  Proof.
    revert pf. induction l; unfold Rec; intros pf.
    - exists nil; simpl. exists eq_refl; intuition. apply rtype_ext.
             - generalize (wf_rtype₀_cons_tail pf); intros pf'.
               destruct (IHl pf') as [l' l'H].
               destruct a. 
               exists ((s, (exist _ r (wf_rtype₀_cons_wf pf)))::l').
               destruct l'H as [pf'' [eq1 eq2]].
               generalize pf; intros pf_. 
               simpl in pf. repeat rewrite andb_true_iff in pf.
               destruct pf as [isl [wfr wfb]]. 
               assert (pf'0 : is_list_sorted ODT_lt_dec
                                             (domain
                                                ((s, exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) r wfr)
                                                   :: l')) = true).
               rewrite domain_cons, is_list_sorted_cons. simpl; intuition.
               subst. unfold domain in isl; rewrite map_map in isl.
               simpl in isl.
               rewrite (map_eq (g:=fst)) in isl by (rewrite Forall_forall; trivial).
               unfold domain. destruct (map fst l'); intuition.
               destruct (StringOrder.lt_dec s s0); intuition.
               
               exists pf'0. subst; simpl. intuition.
               apply rtype_ext.
  Defined.

  Lemma lookup_map_some {ftype:foreign_type} {br:brand_relation} rl2 s x :
    lookup string_dec rl2 s = Some x <->
    lookup string_dec
           (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2) s = Some (proj1_sig x).
  Proof.
    induction rl2; simpl; [split; discriminate|].
    destruct a; simpl.
    destruct (string_dec s s0); auto.
    subst.
    split; inversion 1; subst; auto.
    equalizer. subst; auto.
  Qed.

  Lemma lookup_map_some' {ftype:foreign_type} {br:brand_relation} rl2 s x pf :
    lookup string_dec rl2 s = Some (exist _ x pf) <->
    lookup string_dec
           (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2) s = Some x.
  Proof.
    rewrite lookup_map_some; simpl; reflexivity.
  Qed.

    Lemma  lookup_map_some_ex {ftype:foreign_type} {br:brand_relation}
    (rl2 : list (string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true})) 
    (s : string) (x : rtype₀) :
  (exists pf, lookup string_dec rl2 s =
  Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x pf)) <->
  lookup string_dec
    (map
       (fun x0 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
        (fst x0, proj1_sig (snd x0))) rl2) s = Some x.
Proof.
  induction rl2; simpl; split.
  - intros [??]; discriminate.
  - discriminate.
  - intros [??].
    destruct a; simpl.
    destruct (string_dec s s0); auto.
    + inversion H.
      subst. simpl; trivial.
    + apply IHrl2. eauto.
  - destruct a; simpl.
    destruct (string_dec s s0); auto.
    + inversion 1.
      subst. destruct s1. eauto.
    + apply IHrl2. 
Qed.

  Lemma lookup_map_none {ftype:foreign_type} {br:brand_relation} rl2 s :
    lookup string_dec rl2 s = None <->
    lookup string_dec
           (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2) s = None.
  Proof.
    induction rl2; simpl; [intuition|].
    destruct a; simpl.
    destruct (string_dec s s0); subst; intuition discriminate.
  Qed.

End RType.

Section recmaybe.
  Context {ftype:foreign_type}.
  Context {br:brand_relation}.
  Definition RecMaybe (k:record_kind) (lsr:list (string*rtype)) : option rtype.
    case_eq (is_list_sorted ODT_lt_dec (domain lsr)); intros pf.
    - exact (Some (Rec k lsr pf)).
    - exact None.
  Defined.

  Lemma RecMaybe_some_pf_helper (z:bool) τ f :
    (if z as b
        return
        (z = b -> option rtype)
     then
       fun pf : z = true =>
         Some (f pf)
     else
       fun _ : z = false => None)
      eq_refl = Some τ ->
    {pf : z = true |
     τ = f pf}.
  Proof.
    destruct z; inversion 1; eauto.
  Qed.

  Lemma RecMaybe_some_pf {k τ₀ τ} :
    RecMaybe k τ₀ = Some τ ->
    {pf | τ = Rec k τ₀ pf}.
  Proof.
    unfold RecMaybe. intros eqs.
    apply RecMaybe_some_pf_helper in eqs.
    auto.
  Qed.

  Lemma RecMaybe_pf_some_helper (z:bool) f pf :
    z = true ->
    (if z as b
        return
        (z = b -> option rtype)
     then
       fun pf : z = true =>
         f pf
     else
       fun _ : z = false => None)
      eq_refl = f pf.
  Proof.
    destruct z; inversion 1; eauto.
    f_equal. apply UIP_dec. apply bool_dec.
  Qed.

  Lemma RecMaybe_pf_some k l pf : 
    RecMaybe k l = Some (Rec k l pf).
  Proof.
    unfold RecMaybe.
    rewrite (@RecMaybe_pf_some_helper _ _ pf); trivial.
  Qed.

  Lemma RecMaybe_nil k : RecMaybe k nil = Some (Rec k nil eq_refl).
  Proof.
    apply RecMaybe_pf_some.
  Qed.

End recmaybe.

Section other.
  
  Context {ftype:foreign_type}.
  Context {br:brand_relation}.
  Lemma Rec_inv {k k' x pf1 y pf2} : Rec k x pf1 = Rec k' y pf2 -> x = y.
  Proof.
    intros.
    unfold Rec in H.
    inversion H.
    apply map_rtype_fequal; trivial.
  Qed.

  Lemma Rec_kind_inv {k k' x pf1 y pf2} : Rec k x pf1 = Rec k' y pf2 -> k = k'.
  Proof.
    intros.
    inversion H.
    trivial.
  Qed.

  Lemma Rec_pr_irrel k l1 pf1 pf2 :
    Rec k l1 pf1 = Rec k l1 pf2.
  Proof.
    f_equal. apply UIP_dec; apply bool_dec. 
  Qed.

  Lemma Rec_rewrite {l1 l2} k pf1 pf2 :
    l1 = l2 ->
    Rec k l1 pf1 = Rec k l2 pf2.
  Proof.
    intros eqs.
    destruct eqs.
    apply Rec_pr_irrel.
  Qed.

  Lemma Rec_kind_rewrite k1 k2 l pf :
    k1 = k2 ->
    Rec k1 l pf = Rec k2 l pf.
  Proof.
    congruence.
  Qed.
  
  Lemma Coll_right_inv (τ₁ τ₂:rtype) :
    (proj1_sig τ₁) = Coll₀ (proj1_sig τ₂) <-> τ₁ = Coll τ₂.
  Proof.
    split.
    intros.
    - destruct τ₁; simpl in *.
      destruct τ₂; simpl in *.
      destruct x; try discriminate; simpl in *.
      inversion H. subst.
      clear H.
      assert (Coll (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x0 e0)
              = Coll (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x0 e)).
      apply rtype_fequal. simpl. reflexivity.
      rewrite H.
      reflexivity.
    - intros.
      rewrite H. reflexivity.
  Defined.

  Lemma Coll_inside (τ₁:rtype) (τ₂₀:rtype₀) :
    (proj1_sig τ₁) = Coll₀ τ₂₀ ->
    exists τ₂:rtype,  proj1_sig τ₂ = τ₂₀.
  Proof.
    intros.
    destruct τ₁. simpl in *.
    destruct x; try congruence. simpl in e.
    exists (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e).
    simpl. inversion H; reflexivity.
  Defined.

  Lemma Coll_String_inside (τ₁:rtype) :
    (proj1_sig τ₁) = Coll₀ String₀ ->
    τ₁ = Coll String.
  Proof.
    intros; apply rtype_fequal; auto.
  Defined.

  Lemma map_rtype_nil x0:
    map (fun x2 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
           (fst x2, proj1_sig (snd x2))) x0 = nil <-> x0 = nil.
  Proof.
    split; intros.
    - induction x0; try reflexivity; simpl in *.
      congruence.
    - rewrite H; reflexivity.
  Qed.

  Lemma Rec₀_eq_proj1_Rec {τ k l} :
       proj1_sig τ =
       Rec₀
         k (map
            (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
             (fst x, proj1_sig (snd x))) l) ->
    exists pf, τ = Rec k l pf.
  Proof.
    destruct τ; simpl; intros; subst.
    apply to_Rec.
  Qed.

  Lemma  Nat_canon pf:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Nat₀ pf) = Nat.
  Proof.
    apply rtype_fequal.
    simpl; trivial.
  Qed.

  Lemma  Float_canon pf:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Float₀ pf) = Float.
  Proof.
    apply rtype_fequal.
    simpl; trivial.
  Qed.

  Lemma  String_canon pf:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) String₀ pf) = String.
  Proof.
    apply rtype_fequal.
    simpl; trivial.
  Qed.

  Lemma  Coll_canon x pf:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ x) pf) = Coll (exist _ x pf).
  Proof.
    apply rtype_fequal.
    simpl; trivial.
  Qed.

  Lemma  Coll_String_canon pf:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ String₀) pf) = Coll String.
  Proof.
    apply rtype_fequal.
    simpl; trivial.
  Qed.

  Lemma  Brand_canon x pf:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Brand₀ x) pf) = Brand x.
  Proof.
    apply rtype_fequal.
    simpl in *.
    match_destr_in pf.
    rewrite is_canon_brands_canon_brands; trivial.
  Qed.

  Lemma Foreign_canon ft pf:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Foreign₀ ft) pf) = Foreign ft.
  Proof.
    apply rtype_fequal.
    simpl in *.
    trivial.
  Qed.

  Lemma Either₀_wf_inv {l r} :
    wf_rtype₀ (Either₀ l r) = true ->
    wf_rtype₀ l = true /\ wf_rtype₀ r = true.
  Proof.
    simpl. rewrite andb_true_iff. trivial.
  Qed.

  Lemma  Either_canon l r pf pfl pfr:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Either₀ l r) pf) = Either (exist _ l pfl) (exist _ r pfr).
  Proof.
    apply rtype_fequal.
    simpl; trivial.
  Qed.

  Lemma  Either_canon_ex l r pf:
    exists pfl pfr,
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Either₀ l r) pf) = Either (exist _ l pfl) (exist _ r pfr).
  Proof.
    simpl in pf. destruct (Either₀_wf_inv pf) as [pfl pfr].
    exists pfl; exists pfr.
    apply Either_canon.
  Qed.

  Lemma Arrow₀_wf_inv {l r} :
    wf_rtype₀ (Arrow₀ l r) = true ->
    wf_rtype₀ l = true /\ wf_rtype₀ r = true.
  Proof.
    simpl. rewrite andb_true_iff. trivial.
  Qed.

  Lemma  Arrow_canon l r pf pfl pfr:
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Arrow₀ l r) pf) = Arrow (exist _ l pfl) (exist _ r pfr).
  Proof.
    apply rtype_fequal.
    simpl; trivial.
  Qed.

  Lemma  Arrow_canon_ex l r pf:
    exists pfl pfr,
    (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Arrow₀ l r) pf) = Arrow (exist _ l pfl) (exist _ r pfr).
  Proof.
    simpl in pf. destruct (Arrow₀_wf_inv pf) as [pfl pfr].
    exists pfl; exists pfr.
    apply Arrow_canon.
  Qed.

  Lemma wf_rtype₀_Rec_In {k srl} :
            wf_rtype₀ (Rec₀ k srl) = true ->
            forall a b, In (a,b) srl -> wf_rtype₀ b = true.
  Proof.
    simpl; intros wf a b inn.
    rewrite andb_true_iff in wf. destruct wf.
    rewrite forallb_forall in H0.
    apply (H0 _ inn).
  Defined.

  Lemma wf_rec_pf_sublist {B} {l l'} :
    is_list_sorted ODT_lt_dec (@domain _ B l) = true ->
    sublist l' l ->
    is_list_sorted ODT_lt_dec (domain l') = true.
  Proof.
    intros ? sl.
    eapply is_list_sorted_sublist; eauto 2.
    apply sublist_domain; trivial.
  Qed.

  Lemma lift_Rec₀_injective {k₁ k₂ l1 l2} : lift (Rec₀ k₁) l1 = lift (Rec₀ k₂) l2 -> l1 = l2.
  Proof.
    destruct l1; destruct l2; simpl; trivial; inversion 1; trivial.
  Qed.

  Lemma some_lift_Rec₀ {k₁ k₂ x y} :
    lift (Rec₀ k₁) x = Some (Rec₀ k₂ y) ->
    x = Some y.
  Proof.
    intros eq. apply some_lift in eq. destruct eq; subst.
    inversion e0; congruence.
  Qed.

  Lemma lift_Coll₀_injective {l1 l2} : lift Coll₀ l1 = lift Coll₀ l2 -> l1 = l2.
  Proof.
    intros; eapply lift_injective; eauto.
    inversion 1; trivial.
  Qed.

  Lemma some_lift_Coll₀ {x y} :
    lift Coll₀ x = Some (Coll₀ y) ->
    x = Some y.
  Proof.
    intros eq. apply some_lift in eq. destruct eq; subst.
    inversion e0; congruence.
  Qed.

  Lemma lift_Coll_injective {l1 l2} : lift Coll l1 = lift Coll l2 -> l1 = l2.
  Proof.
    intros; eapply lift_injective; eauto.
    inversion 1; trivial.
    apply rtype_fequal; trivial.
  Qed.

  Lemma some_lift_Coll {x y} :
    lift Coll x = Some (Coll y) ->
    x = Some y.
  Proof.
    intros eq. apply some_lift in eq. destruct eq; subst.
    inversion e0. f_equal. apply rtype_fequal; congruence.
  Qed.

  Lemma lift_col₀_some_col₀ {x y} :
    lift Coll₀ x = Some y ->
    {z | y = Coll₀ z}.
  Proof.
    destruct x; simpl; inversion 1; eauto.
  Qed.

  Lemma lift_col_some_col {x y} :
    lift Coll x = Some y ->
    {z | y = Coll z}.
  Proof.
    destruct x; simpl; inversion 1; eauto.
  Qed.

  Lemma lift_rec₀_some_rec₀ {k x y} :
    lift (Rec₀ k) x = Some y ->
    {z | y = Rec₀ k z}.
  Proof.
    destruct x; simpl; inversion 1; eauto.
  Qed.

  Definition isTop (τ:rtype) : bool.
    destruct τ. destruct x; [ | exact true | .. ]; exact false.
  Defined.

  Lemma istop τ :  {τ = Top} + {isTop τ = false}.
  Proof.
    destruct τ using rtype_rect; intuition.
  Qed.

End other.

Notation "⊥₀" := Bottom₀.
Notation "⊤₀" := Top₀.
Notation "a ~~>₀ b" := (Arrow₀ a b) (at level 99, right associativity).

Notation "⊥" := Bottom.
Notation "⊤" := Top.
Notation "a ~~> b" := (Arrow a b) (at level 99, right associativity).

Ltac rtype_equalizer := 
  repeat match goal with 
           | [H:(@eq rtype₀ (proj1_sig _) (proj1_sig _)) |- _] => apply rtype_fequal in H
           | [H: map
                   (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                      (fst x, proj1_sig (snd x))) _ =
                 map
                   (fun x' : string * {τ₀' : rtype₀ | wf_rtype₀ τ₀' = true} =>
                      (fst x', proj1_sig (snd x'))) _ |- _] => apply map_rtype_fequal in H
         end.

Ltac r_ext := solve [erewrite (rtype_ext); eauto].

Ltac rtype_lift_simpler :=
  match goal with
  | [ |- lift ?f ?x = Some (?f ?y)] => apply (lift_some y); [|reflexivity]
  | [ |- lift ?f ?x = None] => apply lift_none
  | [H:lift ?f ?x = None |- _] => apply none_lift in H
  | [H: lift (Rec₀ _) ?l1 = Some (Rec₀ _ ?l2) |- _ ] => apply some_lift_Rec₀ in H
  | [H: lift (Rec₀ _) ?l1 = lift (Rec₀ _) ?l2 |- _ ] => apply lift_Rec₀_injective in H
  | [H: lift Coll₀ ?l1 = Some (Coll₀ ?l2) |- _ ] => apply some_lift_Coll₀ in H
  | [H: lift Coll₀ ?l1 = lift Coll₀ ?l2 |- _ ] => apply lift_Coll₀_injective in H
  | [H: lift Coll ?l1 = Some (Coll ?l2) |- _ ] => apply some_lift_Coll in H
  | [H: lift Coll ?l1 = lift Coll ?l2 |- _ ] => apply lift_Coll_injective in H
  end.

(** Cases tactic for use with the derived rtypeRectt induction principle *)
Tactic Notation "rtype_rect_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Top"%string
  | Case_aux c "Bottom"%string
  | Case_aux c "Unit"%string
  | Case_aux c "Nat"%string
  | Case_aux c "Float"%string
  | Case_aux c "Bool"%string
  | Case_aux c "String"%string
  | Case_aux c "Coll"%string
  | Case_aux c "Rec"%string
  | Case_aux c "Either"%string
  | Case_aux c "Arrow"%string
  | Case_aux c "Brand"%string
  | Case_aux c "Foreign"%string
  ].

