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
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Morphisms.
Require Import Basics.
Require Import BrandRelation.
Require Import Utils.
Require Import Types.
Require Import ForeignData.
Require Import CommonData.
Require Import ForeignDataTyping.

Section TData.
  (** Data is:
     - unit - used for undefined results.
     - nat - an integer
     - float - a floating point number (IEEE 754 double precision)
     - bool - true or false
     - string - a character string
     - coll - a bag
     - rec - a record
     - left - left sum value
     - right - right sum value
     - foreign - foreign data
   *)

  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Definition Rrec (r1 r2:(string*data)) :=
    ODT_lt_dec (fst r1) (fst r2).

  Inductive data_type : data -> rtype -> Prop :=
  | dttop d : data_normalized brand_relation_brands d -> data_type d Top
  | dtunit : data_type dunit Unit
  | dtnat n : data_type (dnat n) Nat
  | dtfloat n : data_type (dfloat n) Float
  | dtbool b : data_type (dbool b) Bool
  | dtstring s : data_type (dstring s) String               
  | dtcoll dl r : Forall (fun d => data_type d r) dl ->
                  data_type (dcoll dl) (Coll r)
  | dtrec k dl rl rl_sub pf
          (pf':is_list_sorted ODT_lt_dec (domain rl) = true) :
      sublist rl_sub rl ->
      (k = Closed -> rl_sub = rl) ->
      Forall2
        (fun d r => (fst d) = (fst r) /\ data_type (snd d) (snd r))
        dl rl ->
      data_type (drec dl) (Rec k rl_sub pf)
  | dtleft {d τl} τr : data_type d τl -> data_type (dleft d) (Either τl τr)
  | dtright {d} τl {τr} : data_type d τr -> data_type (dright d) (Either τl τr)
  | dtbrand b b' d :
      (* Ensure that only normalized brands are well typed *)
      is_canon_brands brand_relation_brands b ->
      data_normalized brand_relation_brands d ->
      Forall (fun bb =>
                forall τ, 
                  lookup string_dec brand_context_types bb = Some τ ->
                  data_type d τ
                ) b ->
      b ≤ b' ->
      data_type (dbrand b d) (Brand b')
  | dtforeign {fd fτ} :
      foreign_data_typing_has_type fd fτ ->
      data_type (dforeign fd) (Foreign fτ)
  .
  
  Notation "d ▹ r" := (data_type d r) (at level 70). (* \triangleright *)

  Section opt.
    (* synonym for option type *)

    Lemma dtsome {d τ} :
      data_type d τ ->
      data_type (dsome d) (Option τ).
    Proof.
      intros; eapply dtleft; trivial.
    Qed.

    Lemma dtnone τ :
      data_type dnone (Option τ).
    Proof.
      intros; eapply dtright; econstructor.
    Qed.

    Lemma dtsome_inv {d τ} :
      data_type (dsome d) (Option τ) ->
      data_type d τ.
    Proof.
      inversion 1; rtype_equalizer. subst.
      trivial.
    Qed.

  End opt.
  
  Lemma dtrec_closed_inv {dl rl pf} :
    data_type (drec dl) (Rec Closed rl pf) ->
    Forall2
      (fun d r => (fst d) = (fst r) /\ data_type (snd d) (snd r))
      dl rl.
  Proof.
    inversion 1; intuition; subst; rtype_equalizer; subst; trivial.
  Qed.
  
  Lemma dtrec_full k {dl rl} pf:
       Forall2
         (fun d r => (fst d) = (fst r) /\ data_type (snd d) (snd r))
         dl rl ->
       data_type (drec dl) (Rec k rl pf).
  Proof.
    intros. apply (dtrec _ _ rl rl); intuition.
  Qed.

  Lemma dtrec_open {dl : list (string*data)} {rl rl_sub : list (string*rtype)}
        pf (pf':is_list_sorted ODT_lt_dec (domain rl) = true) :
       sublist rl_sub rl ->
       Forall2
         (fun d r => (fst d) = (fst r) /\ data_type (snd d) (snd r))
         dl rl ->
       data_type (drec dl) (Rec Open rl_sub pf).
  Proof.
    intros; apply (dtrec _ _  rl rl_sub); intuition; try discriminate.
  Qed.

  Lemma dtrec_open_pf {dl : list (string*data)} {rl rl_sub : list (string*rtype)}
        (pf':is_list_sorted ODT_lt_dec (domain rl) = true) :
    forall (sub:sublist rl_sub rl),
       Forall2
         (fun d r => (fst d) = (fst r) /\ data_type (snd d) (snd r))
         dl rl ->
       data_type (drec dl) (Rec Open rl_sub (is_list_sorted_sublist pf' (sublist_domain sub))).
  Proof.
    intros; apply (dtrec _ _  rl rl_sub); intuition; try discriminate.
  Qed.

  Lemma dtrec_closed_is_open k dl rl pf :
    data_type (drec dl) (Rec Closed rl pf) ->
    data_type (drec dl) (Rec k rl pf).
  Proof.
    intros dt. apply dtrec_closed_inv in dt; apply dtrec_full; trivial.
  Qed.

  Lemma dtbrand_inv b b' d :
    data_type (dbrand b d) (Brand b') ->
      is_canon_brands brand_relation_brands b /\
      data_normalized brand_relation_brands d /\
      Forall (fun bb =>
                forall τ, 
                  lookup string_dec brand_context_types bb = Some τ ->
                  data_type d τ
                ) b /\
      b ≤ b'.
  Proof.
    inversion 1; subst.
    apply canon_equiv in H2.
    rewrite H2 in H6.
    intuition.
  Qed.

  Lemma dtbrand_refl {b d}:
    is_canon_brands brand_relation_brands b ->
    data_normalized brand_relation_brands d ->
    Forall (fun bb =>
                forall τ, 
                  lookup string_dec brand_context_types bb = Some τ ->
                  data_type d τ
           ) b   ->
    data_type (dbrand b d) (Brand b).
  Proof.
    intros; eapply dtbrand; try eassumption; intuition.
  Qed.

  Lemma  data_type_ext d τ₀ pf1 pf2: 
    d ▹ (exist _ τ₀ pf1) <-> d ▹ (exist _ τ₀ pf2).
  Proof.
    rewrite (wf_rtype₀_ext pf1 pf2). intuition.
  Qed.

  Lemma  data_type_fequal d τ₁ τ₂: 
    (proj1_sig τ₁) = (proj1_sig τ₂) ->
    (d ▹ τ₁ <-> d ▹ τ₂).
  Proof.
    destruct τ₁; destruct τ₂; simpl; intros; subst.
    apply data_type_ext.
  Qed.

  Lemma data_type_not_bottom {d} : d ▹ ⊥ -> False.
  Proof.
    induction d; inversion 1.
  Qed.
    
Section inv.

  Lemma data_type_dunit_inv {τ}:
    isTop τ = false ->
    dunit ▹ τ -> τ = Unit.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros HH HH0; assert False; [inversion HH0|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_dnat_inv {n τ}:
    isTop τ = false ->
    dnat n ▹ τ -> τ = Nat.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_dfloat_inv {n τ}:
    isTop τ = false ->
    dfloat n ▹ τ -> τ = Float.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_dbool_inv {b τ}:
    isTop τ = false ->
    dbool b ▹ τ -> τ = Bool.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_dstring_inv {s τ}:
    isTop τ = false ->
    dstring s ▹ τ -> τ = String.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_dcoll_inv {d τ}:
    isTop τ = false ->
    dcoll d ▹ τ ->
    {τ' | τ = Coll τ'}.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_drec_inv {sdl τ}:
    isTop τ = false ->
    drec sdl ▹ τ ->
    {k : record_kind & {τ' | exists pf, τ = Rec k τ' pf}}.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_dleft_inv {d τ} :
    isTop τ = false ->
    dleft d ▹ τ ->
    {τl : rtype & {τr | τ = Either τl τr}}.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

    Lemma data_type_dright_inv {d τ} :
    isTop τ = false ->
    dright d ▹ τ ->
    {τl : rtype & {τr | τ = Either τl τr}}.
  Proof.
    induction τ using rtype_rect; 
    try solve [intros ? HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_dsome_inv {d τ} :
    isTop τ = false ->
    dsome d ▹ τ ->
    {τl : rtype & {τr | τ = Either τl τr}}.
  Proof.
    apply data_type_dleft_inv.
  Qed.

    Lemma data_type_dnone_inv {τ} :
    isTop τ = false ->
    dnone ▹ τ ->
    {τl : rtype & {τr | τ = Either τl τr}}.
  Proof.
    apply data_type_dright_inv.
  Qed.

  Lemma data_type_Unit_inv {d}:
    d ▹ Unit ->
    d = dunit.
  Proof.
    induction d;
    try solve [intros HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_Nat_inv {d}:
    d ▹ Nat ->
    {n | d = dnat n}.
  Proof.
    induction d;
    try solve [intros HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_Float_inv {d}:
    d ▹ Float ->
    {n | d = dfloat n}.
  Proof.
    induction d;
    try solve [intros HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_Bool_inv {d}:
    d ▹ Bool ->
    {b | d = dbool b}.
  Proof.
    induction d;
    try solve [intros HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_String_inv {d}:
    d ▹ String ->
    {s | d = dstring s}.
  Proof.
    induction d;
    try solve [intros HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma data_type_Col_inv {d τ}:
    d ▹ Coll τ ->
    {dl | d = dcoll dl}.
  Proof.
    revert τ.
    induction d; intros τ;
    try solve [intros HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

  Lemma Col_inv {d τ}:
    dcoll d ▹ Coll τ ->
    Forall (fun c => c ▹ τ) d.
  Proof.
    inversion 1; rtype_equalizer.
    subst.
    trivial.
  Qed.

  Lemma data_type_Rec_inv {d k τ pf} :
    d ▹ Rec k τ pf ->
    {dl | d = drec dl}.
  Proof.
    revert τ pf.
    induction d; intros τ pf;
    try solve [intros HH; assert False; [inversion HH|intuition]];
    eauto; simpl; try discriminate.
  Qed.

    Lemma data_type_Arrow_inv {d τin τout}:
    d ▹ Arrow τin τout ->
    False.
    Proof.
      inversion 1.
    Qed.

    Lemma data_type_Foreign_inv {d ft}:
    d ▹ Foreign ft ->
    {fd | d = dforeign fd}.
    Proof.
      revert ft.
      induction d; intros ft;
        try solve [intros HH; assert False; [inversion HH|intuition]];
        eauto; simpl; try discriminate.
    Qed.

  Lemma data_type_Either_inv {d τl τr}:
    d ▹ Either τl τr ->
    {dl | d = dleft dl /\ dl ▹ τl} + {dr | d = dright dr /\ dr ▹ τr}.
  Proof.
    revert τl τr.
    induction d; intros τ pf;
    try solve [intros HH; assert False; [inversion HH|intuition]].
    - left. econstructor. inversion H; rtype_equalizer. subst; intuition.
    - right. econstructor. inversion H; rtype_equalizer. subst; intuition.
  Qed.

    Lemma data_type_Option_inv {d τ}:
    d ▹ Option τ ->
    {ds | d = dsome ds /\ ds ▹ τ} + {d = dnone}.
    Proof.
      intros inn. apply data_type_Either_inv in inn.
      unfold dsome, dnone.
      destruct inn as [[?[??]]|[?[??]]]; subst; eauto.
      eapply data_type_Unit_inv in H0.
      subst; eauto.
    Qed.

    Lemma data_type_Brand_inv {d br} :
    d ▹ Brand br ->
    {bs:brands & {d' | d = dbrand bs d'}}.
  Proof.
    revert br.
    induction d; intros br;
    try solve [intros H; assert False; [inversion H|intuition]];
    eauto; simpl; try discriminate.
    - intros. assert False; [inversion H0|intuition].
    - intros. assert False; [inversion H0|intuition].
  Qed.

End inv.

(** Inversion tactic for typed data *)
    Ltac data_type_inverter :=
  match goal with
    | [H: dunit ▹ ?τ,  H1: isTop ?τ = false |- _ ] => 
      match τ with
        | Unit => fail 1
        | _ => generalize (data_type_dunit_inv H1 H); intros ?; try subst
      end
    | [H: dnat _ ▹ ?τ,  H1: isTop ?τ = false  |- _ ] => 
      match τ with
        | Nat => fail 1
        | _ => generalize (data_type_dnat_inv H1 H); intros ?; try subst
      end
    | [H: dfloat _ ▹ ?τ,  H1: isTop ?τ = false  |- _ ] => 
      match τ with
        | Float => fail 1
        | _ => generalize (data_type_dfloat_inv H1 H); intros ?; try subst
      end
    | [H: dbool _ ▹ ?τ,  H1: isTop ?τ = false  |- _ ] => 
      match τ with
        | Bool => fail 1
        | _ => generalize (data_type_dbool_inv H1 H); intros ?; try subst
      end
    | [H: dstring _ ▹ ?τ,  H1: isTop ?τ = false  |- _ ] => 
      match τ with
        | String => fail 1
        | _ => generalize (data_type_dstring_inv H1 H); intros ?; try subst
      end
    | [H: dcoll _ ▹ ?τ,  H1: isTop ?τ = false  |- _ ] => 
      match τ with
        | Coll _ => fail 1
        | _ => destruct (data_type_dcoll_inv H1 H); try subst
      end
    | [H: drec _ ▹ ?τ,  H1: isTop ?τ = false  |- _ ] => 
      match τ with
        | Rec _ _ => fail 1
        | _ => destruct (data_type_drec_inv H1 H) as [?[?[??]]]; try subst
      end
  end.

Lemma data_type_Rec_sublist {r k l l' pf} pf' :
      drec r ▹ Rec k l pf ->
      sublist l' l ->
      drec r ▹ Rec Open l' pf'.
Proof.
  inversion 1; subst; intros.
  inversion H2; clear H2; simpl in *; rtype_equalizer; subst.
  econstructor.
  - eassumption.
  - rewrite H0; eassumption.
  - intros; discriminate.
  - trivial.
Qed.

Lemma sorted_forall_same_domain {dl τ}:
    Forall2 (fun (d : string * data) (r : string * rtype) =>
          fst d = fst r /\ data_type (snd d) (snd r)) dl τ ->
    (domain dl) = (domain τ).
Proof.
  intros.
  assert (Forall2 (fun (d : string * data) (r : string * rtype) =>
                     fst d = fst r) dl τ)
    by (eapply Forall2_incl; try apply H; intuition).
  apply Forall2_map in H0.
  apply Forall2_eq in H0.
  assumption.
Qed. 

Lemma data_type_Rec_domain {r k l pf} :
      drec r ▹ Rec k l pf ->
      sublist (domain l) (domain r).
Proof.
  revert l pf. induction r; inversion 1; rtype_equalizer; subst;
               inversion H5; subst; clear H5.
  - apply sublist_nil_r in H3; subst; simpl; auto.
  - simpl. intuition.
    rewrite H0.
    apply sublist_domain in H3.
    rewrite H3.
    simpl.
    apply sublist_cons.
    apply (IHr _ (is_list_sorted_cons_inv _ pf')).
    apply dtrec_full; trivial.
Qed.

Lemma data_type_Rec_closed_domain {r l pf} :
      drec r ▹ Rec Closed l pf ->
      domain r = domain l.
Proof.
  intros.
  symmetry.
  apply sublist_length_eq.
  - apply (data_type_Rec_domain H).
  - apply dtrec_closed_inv in H.
    repeat rewrite domain_length.
    symmetry.
    eapply Forall2_length; eauto.
Qed.

Lemma data_type_Recs_domain {r k l pf l' pf'} :
  drec r ▹ Rec k l pf ->
  drec r ▹ Rec Closed l' pf' ->
  sublist (domain l) (domain l').
Proof.
  intros t1 t2.
  rewrite (data_type_Rec_domain t1).
  rewrite (data_type_Rec_closed_domain t2).
  reflexivity.
Qed.

Lemma data_type_Recs_closed_domain {r l l' pf pf'} :
  drec r ▹ Rec Closed l pf ->
  drec r ▹ Rec Closed l' pf' ->
  domain l = domain l'.
Proof.
  intros t1 t2.
  rewrite <- (data_type_Rec_closed_domain t1).
  rewrite <- (data_type_Rec_closed_domain t2).
  trivial.
Qed.

Lemma dtrec_edot_parts a k τ pf s x y:
  drec a ▹ Rec k τ pf ->
  edot a s = Some x ->
  edot τ s = Some y ->
  x ▹ y.
Proof.
  unfold edot.
  intros dt ina inτ.
  invcs dt; rtype_equalizer.
  subst.
  apply is_list_sorted_NoDup_strlt in pf'.
  apply (assoc_lookupr_nodup_sublist pf' H2 (R_dec:=ODT_eqdec)) in inτ.
  clear H3 H2.
  induction H4; simpl in *; try discriminate.
  destruct x0; destruct y0; destruct H; simpl in *; subst.
  invcs pf'.
  destruct (string_eqdec s s1); unfold Equivalence.equiv in *; subst.
  - apply sorted_forall_same_domain in H4.
    assert (nd2:~ In s1 (domain l)) by (rewrite H4; trivial).
    apply (assoc_lookupr_nin_none) with (dec:=string_eqdec) in H2.
    rewrite H2 in inτ.
    invcs inτ.
    apply (assoc_lookupr_nin_none) with (dec:=string_eqdec) in nd2.
    unfold Equivalence.equiv, RelationClasses.complement, not in *.
    simpl in *.
    rewrite nd2 in ina.
    invcs ina.
    trivial.
  - match_case_in inτ
    ; [intros ? eqq1 | intros eqq1]; rewrite eqq1 in inτ
    ; try discriminate.
    invcs inτ.
    match_case_in ina
    ; [intros ? eqq2 | intros eqq2]; rewrite eqq2 in ina
    ; try discriminate.
    invcs ina.
    intuition.
Qed.

Lemma coll_type_cons a c x:
  dcoll (a :: c) ▹ Coll x ->
  a ▹ x /\ dcoll c ▹ Coll x.
Proof.
  intros.
  inversion H.
  assert (r = x) by (apply rtype_fequal; assumption).
  rewrite Forall_forall in H2; simpl in H2.
  rewrite H3 in *; clear H3 H1.
  split.
  apply (H2 a); left; reflexivity.
  apply dtcoll; rewrite Forall_forall; intros.
  apply (H2 x0); right; assumption.
Qed.

Lemma dcoll_coll_in_inv {d τ a} :
  In a d -> dcoll d ▹ Coll τ -> a ▹ τ.
Proof.
  induction d; [simpl; intuition| ]; intros.
  apply coll_type_cons in H0.
  simpl in *; intuition; subst; intuition.
Qed.

Lemma rec_type_closed_cons {x y l l' pf} pf':
  drec (x :: l) ▹ Rec Closed (y :: l') pf ->
  (snd x) ▹ (snd y) /\ drec l ▹ Rec Closed l' pf'.
Proof.
  intros H.
  apply dtrec_closed_inv in H.
  inversion H; subst; intuition.
  apply dtrec_full; auto.
Qed.

Lemma rec_type_cons {k x y l l' pf} pf':
  drec (x :: l) ▹ Rec k (y :: l') pf ->
  ((fst x) = (fst y) /\ (snd x) ▹ (snd y) /\ drec l ▹ Rec k l' pf')
  \/ ((fst x) <> (fst y) /\ drec l ▹ Rec k (y::l') pf).
Proof.
  intros H.
  inversion H; clear H; subst.
  inversion H5; clear H5; subst.
  destruct rl_sub; simpl in *; try discriminate.
  inversion H2; clear H2.
  rtype_equalizer; subst.
  intuition.
  destruct p; destruct x; destruct y; destruct y0; simpl in *; subst.
  inversion H3; subst.
  - left; intuition.
    econstructor; try apply H7; trivial.
    eapply is_list_sorted_cons_inv; eassumption.
    intros kc; specialize (H4 kc); inversion H4.
    trivial.
  - assert (neq:s2 = s1 -> False).
    + intro; subst.
       generalize pf'0.
       generalize (sublist_In H1 (s1, r0)); clear; simpl; intuition.
       apply (@is_list_sorted_cons string) in pf'0.
       apply (@is_list_sorted_cons string) in pf'0.
       apply is_list_sorted_NoDup in pf'0
       ; [ | eapply StringOrder.lt_strorder].
       inversion pf'0; subst.
       apply in_dom in H.
       tauto.
    + right; split; trivial.
       econstructor; try apply H1; auto.
       apply (is_list_sorted_cons_inv _ pf'0).
       intros kc; specialize (H4 kc).
       inversion H4; subst.
       elim neq; trivial.
Qed.
  
  Lemma sorted_forall_sorted (dl:list (string*data)) (τ:list (string*rtype)):
    is_list_sorted ODT_lt_dec (domain τ) = true ->
    Forall2 (fun (d : string * data) (r : string * rtype) =>
          fst d = fst r /\ data_type (snd d) (snd r)) dl τ ->
    is_list_sorted ODT_lt_dec (domain dl) = true.
  Proof.
    intros.
    assert (domain dl = domain τ).
    apply sorted_forall_same_domain; assumption.
    rewrite H1; assumption.
  Qed.

  Lemma insert_and_foralls_mean_same_sort l1 l2 τ₁ τ₂ x y:
    is_list_sorted ODT_lt_dec (domain (rec_sort (τ₁ ++ τ₂))) = true ->
    Forall2
      (fun (d : string * data) (r : string * rtype) =>
         fst d = fst r /\ data_type (snd d) (snd r))
      (rec_sort (l1 ++ l2)) (rec_sort (τ₁ ++ τ₂)) ->
    (fst x = fst y) ->
    is_list_sorted
      ODT_lt_dec
      (domain
         (insertion_sort_insert rec_field_lt_dec y (rec_sort (τ₁ ++ τ₂)))) = true ->
    is_list_sorted
      ODT_lt_dec
      (domain
         (insertion_sort_insert rec_field_lt_dec x (rec_sort (l1 ++ l2)))) = true.
  Proof.
    intros.
    assert (domain (rec_sort (l1 ++ l2)) = domain (rec_sort (τ₁ ++ τ₂))).
    apply sorted_forall_same_domain; assumption.
    assert (domain (insertion_sort_insert rec_field_lt_dec x (rec_sort (l1 ++ l2))) =
            domain (insertion_sort_insert rec_field_lt_dec y (rec_sort (τ₁ ++ τ₂)))).
    generalize (same_domain_insert (rec_sort (l1++l2)) (rec_sort (τ₁++τ₂)) x y); intros.
    simpl.
    unfold rec_cons_sort in *. rewrite H4; try assumption; try reflexivity.
    rewrite H4; assumption.
  Qed.

  Lemma sorted_cons_skip {A} (l:list (string*A)) (x x0:string*A) :
    is_list_sorted
      ODT_lt_dec
      (domain (rec_cons_sort x (x0 :: l))) = true
    -> is_list_sorted
         ODT_lt_dec
         (domain (rec_cons_sort x l)) = true.
  Proof.
    intros; simpl in *.
    revert H; elim (rec_field_lt_dec x x0); intros.
    assert (is_list_sorted ODT_lt_dec (domain (x :: l)) = true).
    apply (@rec_sorted_skip_second string ODT_string _ l x x0); assumption.
    assert ((rec_cons_sort x l) = x::l).
    apply rec_cons_sorted_id; assumption.
    rewrite H1; assumption.
    revert H; elim (rec_field_lt_dec x0 x); intros.
    apply (@rec_sorted_skip_first string ODT_string _ (rec_cons_sort x l) x0); assumption.
    assert (fst x = fst x0).
    apply lt_contr1; assumption.
    simpl in H.
    rewrite <- H0 in H.
    assert ((rec_cons_sort x l) = x::l).
    apply rec_cons_sorted_id; assumption.
    rewrite H1; assumption.
  Qed.

  Lemma Forall2_cons_sorted l1 l2 x y :
    Forall2
      (fun (d : string * data) (r : string * rtype) =>
         fst d = fst r /\ data_type (snd d) (snd r))
      l1 l2 ->
    is_list_sorted ODT_lt_dec
                   (domain
                      (insertion_sort_insert rec_field_lt_dec x l1)) =
    true ->
    is_list_sorted ODT_lt_dec
                   (domain
                      (insertion_sort_insert rec_field_lt_dec y l2)) =
    true -> fst x = fst y -> data_type (snd x) (snd y) ->
    Forall2
      (fun (d : string * data) (r : string * rtype) =>
         fst d = fst r /\ data_type (snd d) (snd r))
      (insertion_sort_insert rec_field_lt_dec x l1)
      (insertion_sort_insert rec_field_lt_dec y l2).
  Proof.
    intros.
    induction H.
    - apply Forall2_cons.
      split; assumption; apply Forall2_nil.
      apply Forall2_nil.
    - assert (is_list_sorted
                ODT_lt_dec
                (domain (insertion_sort_insert rec_field_lt_dec x l)) = true)
       by (apply (sorted_cons_skip l x x0); assumption).
      assert (is_list_sorted
                ODT_lt_dec
                (domain (insertion_sort_insert rec_field_lt_dec y l')) = true)
        by (apply (sorted_cons_skip l' y y0); assumption).
      specialize (IHForall2 H5 H6).
      simpl in *.
      revert H0 H1.
      elim (rec_field_lt_dec x x0); elim (rec_field_lt_dec y y0); intros.
      + apply Forall2_cons. split; assumption.
        apply Forall2_cons; assumption.
      + revert H1.
        elim (rec_field_lt_dec y0 y); intros.
        apply Forall2_cons.
        elim H; intros; clear H.
        congruence.
        elim H; intros; clear H.
        congruence.
        assert ((fst y) = (fst y0)).
        apply lt_contr1; assumption.
        assert ((fst x) = (fst x0)).
        elim H; intros; clear H.
        rewrite <- H7 in H8.
        rewrite <- H2 in H8.
        rewrite H8; reflexivity.
        congruence.
      + revert H0.
        elim (rec_field_lt_dec x0 x); intros.
        apply Forall2_cons.
        elim H; intros; clear H.
        congruence.
        elim H; intros; clear H.
        congruence.
        assert ((fst x) = (fst x0)).
        apply lt_contr1; assumption.
        assert ((fst y) = (fst y0)).
        elim H; intros; clear H.
        rewrite <- H8.
        rewrite <- H2.
        assumption.
        congruence.
      + revert H0 H1.
        elim (rec_field_lt_dec x0 x); elim (rec_field_lt_dec y0 y); intros.
        apply Forall2_cons; assumption.
        assert ((fst y) = (fst y0)).
        apply lt_contr1; assumption.
        assert ((fst x) = (fst x0)).
        elim H; intros; clear H.
        rewrite <- H7 in H8.
        rewrite <- H2 in H8.
        rewrite H8; reflexivity.
        congruence.
        assert ((fst x) = (fst x0)).
        apply lt_contr1; assumption.
        assert ((fst y) = (fst y0)).
        elim H; intros; clear H.
        rewrite <- H8.
        rewrite <- H2.
        assumption.
        congruence.
        apply Forall2_cons; assumption.
  Qed.

  Lemma dtrec_rec_concat_sort {x xt pfx y yt pfy} pxyt :
    drec x ▹ Rec Closed xt pfx ->
    drec y ▹ Rec Closed yt pfy ->
    drec (rec_concat_sort x y) ▹ Rec Closed (rec_concat_sort xt yt) pxyt.
  Proof.
    intros typ1 typ2.
    apply dtrec_closed_inv in typ1.
    apply dtrec_closed_inv in typ2.
    apply dtrec_full.
    unfold rec_concat_sort.
    apply rec_sort_Forall2.
    - repeat rewrite domain_app.
      rewrite (sorted_forall_same_domain typ1).
      rewrite (sorted_forall_same_domain typ2).
      trivial.
    - apply Forall2_app; trivial.
  Qed.
  
  Lemma dttop' d : data_normalized brand_relation_brands d -> d ▹ ⊤.
  Proof.
    apply dttop.
  Qed.
  Hint Resolve dttop dttop'.

  Lemma Forall_map {A B} P (f:A->B) l :
    Forall P (map f l) <-> Forall (fun x => P (f x)) l.
  Proof.
    induction l; simpl; intuition.
    - inversion H1; subst; auto.
    - inversion H1; subst; auto.
  Qed.

  (** Well typed data must be normalized *)
  Lemma data_type_normalized d τ :
    d ▹ τ -> data_normalized brand_relation_brands d.
  Proof.
    Hint Constructors data_normalized.
    revert τ.
    induction d using dataInd2; intros; try assumption; simpl in *;
    auto 2.
    - constructor. inversion H0; subst.
      + inversion H1; trivial.
      + revert H2; apply Forall_impl_in.
        eauto.
    - inversion H0; subst; trivial.
      constructor; trivial.
      + apply Forall_forall. intros.
        destruct x; simpl.
        specialize (H _ _ H1).
        revert H H1 H4. clear.
        revert rl.
        induction r; inversion 3; subst; simpl in *;
        intuition; subst; simpl in *; subst; eauto.
      + apply sorted_forall_same_domain in H4.
        rewrite H4.
        trivial.
    - inversion H; subst; trivial; eauto.
    - inversion H; subst; trivial; eauto.
    - inversion H; subst; trivial; constructor; eauto.
    - invcs H.
      + eauto.
      + constructor.
        eapply foreign_data_typing_normalized; eauto.
  Qed.

  (** Lemma showing that normalization preserves typing *)
  Lemma normalize_preserves_type d τ :
    d ▹ τ -> normalize_data brand_relation_brands d ▹ τ.
  Proof.
    intros.
    rewrite normalize_normalized_eq; trivial.
    eapply data_type_normalized; eauto.
  Qed.
  
  Lemma dttop_weaken {d τ} : data_type d τ -> data_type d ⊤.
  Proof.
    intros H; apply data_type_normalized in H.
    auto 2.
  Qed.

End TData.

(* expands well-typed data with a specific type *)
Notation "d ▹ r" := (data_type d r) (at level 70). (* \vdash, \triangleright *)

Ltac dtype_inverter
  := repeat progress
            match goal with
            | [H:?d ▹ Unit |- _ ] =>
              apply data_type_Unit_inv in H; try subst d
            | [H:?d ▹ Nat |- _ ] =>
              apply data_type_Nat_inv in H; destruct H; try subst d
            | [H:?d ▹ Float |- _ ] =>
              apply data_type_Float_inv in H; destruct H; try subst d
            | [H:?d ▹ Bool |- _ ] =>
              apply data_type_Bool_inv in H;  destruct H; try subst d
            | [H:?d ▹ String |- _ ] =>
              apply data_type_String_inv in H;  destruct H; try subst d
            | [H:?d ▹ (Coll ?τ) |- _ ] =>
              match d with
              | dcoll ?d => fail 1
              | _ =>
                let XX := fresh in 
                destruct (data_type_Col_inv H) as [XX ?];
                  (discriminate || (subst d; rename XX into d))
              end
            | [H:?d ▹ Arrow _ _ |- _ ] =>
              apply data_type_Arrow_inv in H; tauto
            | [H:?d ▹ (Foreign ?τ) |- _ ] =>
              match d with
              | dforeign _ => fail 1
              | _ =>
                let XX := fresh in 
                destruct (data_type_Foreign_inv H) as [XX ?];
                  (discriminate || (subst d; rename XX into d))
              end
            | [H:?d ▹ (Brand _) |- _ ] =>
              match d with
              | dbrand _ _ => fail 1
              | _ =>
                let XX := fresh in 
                destruct (data_type_Brand_inv H) as [? [XX ?]];
                  (discriminate || (subst d; rename XX into d))
              end
            | [H:?d ▹ (Rec ?k ?τ ?pf) |- _ ] =>
              match d with
              | drec _ => fail 1
              | _ =>
                let XX := fresh in 
                destruct (data_type_Rec_inv H) as [XX ?];
                  (discriminate || (subst d; rename XX into d))
              end
            |   [H:?d ▹ Bool |- _ ] =>
                let XX := fresh in 
                destruct (data_type_Bool_inv H) as [XX ?]; try subst d; clear H;
                rename XX into d
            | [H:proj1_sig _ =
                 Rec₀ Closed
                   (map
                      (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                         (fst x, proj1_sig (snd x))) _) |- _ ] 
              => apply Rec₀_eq_proj1_Rec in H; destruct H as [??]
            end; simpl.

  Ltac dtype_inverter_with_either 
    := repeat progress
              try dtype_inverter; 
      try match goal with
            | [H:?d ▹ (Either _ _) |- _ ] =>
              match d with
                | dleft ?d => fail 1
                | dright ?d => fail 1
                | _ =>
                let XX := fresh in 
                destruct (data_type_Either_inv H) as [[XX [??]]|[XX [??]]];
                  (discriminate || (subst d; rename XX into d))
              end
          end.

(* adds type information about the data when it can be inferred *)
Ltac dtype_enrich :=
  match goal with
    | [H: In ?a ?l, H2: (dcoll ?l) ▹ (Coll ?τ) |- _ ] =>
      extend (dcoll_coll_in_inv H H2)
  end.

Hint Immediate dttop dttop'.
Hint Resolve dttop_weaken.

Section subtype.

  Lemma subtype_Rec_sublist_strengthen
        {fdata:foreign_data}
        {ftype:foreign_type}
        {fdtyping:foreign_data_typing}
        {m:brand_model} {dl rl srl k1 pf srl0 pf0 k2} :
  forall (f2:Forall2
         (fun (d : string * data) (r : string * rtype) =>
            fst d = fst r /\ data_type (snd d) (snd r)) dl rl)
         (subl:sublist srl rl)
         (subt:Rec k1 srl pf <: Rec k2 srl0 pf0)
         (pf3:is_list_sorted ODT_lt_dec (domain rl) = true)
         (ft:Forallt
        (fun ab : string * rtype =>
         forall (d : data) (τ₂ : rtype),
         snd ab <: τ₂ -> data_type d (snd ab) -> data_type d τ₂) srl),
  exists l2,
    Forall2
         (fun (d : string * data) (r : string * rtype) =>
            fst d = fst r /\ data_type (snd d) (snd r)) dl l2
    /\
    sublist srl0 l2.
Proof.
  revert dl srl k1 pf srl0 pf0 k2.
  induction rl; intros dl srl k1 pf srl0 pf0 k2 f2 subl subt pf3; inversion f2; clear f2; subst; intros.
  -  apply sublist_nil_r in subl; subst. exists nil.
     apply subtype_Rec_sublist in subt.
     apply sublist_nil_r in subt.
     unfold domain in subt; apply map_eq_nil in subt. subst.
     intuition.
  - destruct x; destruct a. unfold fst, snd in H2; destruct H2; subst.
    destruct (sublist_cons_inv subl pf3).
    + destruct H as [?[??]]. subst.
      inversion ft; subst; clear ft.
       case_eq (lookup string_dec srl0 s0); intros.
      * (* clear subl. revert x H1 pf subt. *)
         destruct srl0; intros; simpl in H; try discriminate.
         destruct p. destruct (string_dec s0 s).
          inversion H; clear H; subst.
          destruct (Rec_subtype_cons_inv subt) as [? [??]].
          specialize (IHrl _ _ k1 _ _ _ _ H3 H1 H (
                             is_list_sorted_cons_inv ODT_lt_dec pf3) H5).
          destruct (IHrl) as [? [??]].
          exists ((s,r0)::x2); intuition;[ | apply sublist_cons; auto].
          constructor; intuition.
          simpl.
          inversion subt; rtype_equalizer; subst; trivial.
          destruct rl2; inversion H11; rtype_equalizer; clear H11.
          destruct rl1; inversion H8; rtype_equalizer; clear H8.
          destruct p; destruct p0; unfold fst in H11; subst.
          simpl.
          simpl in H0.
          specialize (H10 s0 r1). simpl in H10.
          destruct (string_dec s0 s0); [| congruence].
          destruct H10 as [? [??]]; trivial.
          invcs H7.
          eauto.
          
          generalize (subtype_Rec_sublist subt); intros subl'.
          repeat rewrite domain_cons in subl'; unfold fst in subl'.
          inversion subl'; subst; [congruence | ].
          apply lookup_in in H.
          apply in_dom in H.
          generalize (sublist_In H7 s0); simpl; intuition.
          generalize (is_list_sorted_NoDup _ _ pf).
          inversion 1; congruence.
      * apply Rec_subtype_cons_inv1 in subt; trivial.
          destruct subt as [pf' subt].
          specialize (IHrl _ _ k1 pf' _ pf0 _ H3 H1 subt (
                             is_list_sorted_cons_inv ODT_lt_dec pf3) H5).
          destruct IHrl as [? [? ?]].
          exists ((s0,r)::x0).
          intuition.
          apply sublist_skip; auto 1.
    + simpl in H; destruct H.
      specialize (IHrl _ _ k1 pf _ pf0 _ H3 H1 subt (
                             is_list_sorted_cons_inv ODT_lt_dec pf3) ft).
          destruct IHrl as [? [? ?]].
          exists ((s0,r)::x).
          intuition.
          apply sublist_skip; auto 1.
Qed.

Global Instance data_type_subtype_prop
       {fdata:foreign_data}
       {ftype:foreign_type}
       {fdtyping:foreign_data_typing}
       {m:brand_model} : Proper (eq ==> subtype ==> impl) (data_type).
  Proof.
    unfold Proper, respectful, impl, flip.
    intros ? d ? τ₁ τ₂ sub ; subst.
    Hint Resolve data_type_ext.
    Hint Resolve data_type_not_bottom.
    Hint Resolve dtrec_closed_is_open.
    Hint Constructors data_normalized.
    
    revert d τ₂ sub.
      induction τ₁ using rtype_rect;
        induction τ₂ using rtype_rect; simpl;
        try autorewrite with rtype_join;
        try solve[inversion 1; subst; intros; 
                  try solve [intros; dtype_inverter; eauto 2
                            | eelim data_type_not_bottom; eauto
                            | unfold Top, Bottom, Unit, Nat, Float, Bool, String, Coll, Rec in *;
                              eauto 2; try r_ext]].
    - clear IHτ₂. intros.
      inversion H; rtype_equalizer.
      subst.
      inversion sub; rtype_equalizer.
      + subst; trivial.
      + subst. constructor.
        revert H2; apply Forall_impl; auto. 
    - clear H0.
      intros.
      inversion H0; rtype_equalizer; subst. 
      destruct (subtype_Rec_sublist_strengthen H6 H3 sub) as [?[??]]; trivial.
      eapply dtrec; try exact H1; trivial.
      rewrite <- (sorted_forall_same_domain H1).
      rewrite (sorted_forall_same_domain H6).
      trivial.
      intros; subst.
      generalize (subtype_Rec_closed2_closed1 sub); intros; subst.
      intuition; subst.
      generalize (subtype_Rec_closed_domain sub); intros eqd.
      rewrite <- (sorted_forall_same_domain H6) in eqd.
      rewrite (sorted_forall_same_domain H1) in eqd.
      apply sublist_length_eq; trivial.
      rewrite <- (domain_length srl0), <- (domain_length x).
      congruence.
    - intros e sub. apply subtype_Either_inv in e.
      destruct e as [e1 e2].
      inversion sub; subst; rtype_equalizer.
      + subst. econstructor; intuition.
      + subst. econstructor; intuition.
    - inversion 1; trivial; subst.
      + apply canon_equiv in H1.
        rewrite H1; trivial.
      + apply canon_equiv in H; apply canon_equiv in H0.
        rewrite H, H0 in H1.
        inversion 1; subst.
        apply canon_equiv in H3. rewrite H3 in H8.
        econstructor; trivial.
        etransitivity; eauto.
    - intros sub dt.
      invcs sub; trivial.
      invcs dt.
      constructor.
      eapply foreign_data_typing_subtype; eauto.
  Qed.

  Global Instance data_type_subtype_prop'
         {fdata:foreign_data}
         {ftype:foreign_type}
         {fdtyping:foreign_data_typing}
         {m:brand_model} d : Proper (subtype ==> impl) (data_type d).
  Proof.
    apply data_type_subtype_prop; trivial.
  Qed.

  Lemma join_preserves_data_type
        {fdata:foreign_data}
        {ftype:foreign_type}
        {fdtyping:foreign_data_typing}
        {m:brand_model} {d τ}:
    d ▹ τ -> forall τ₀, d ▹ (τ ⊔ τ₀).
  Proof.
    intros.
    rewrite (join_leq_l τ τ₀) in H; trivial.
  Qed.

  (* Just so we can refer to it in the paper *)
  Theorem subtyping_preserves_data_type
          {fdata:foreign_data}
          {ftype:foreign_type}
          {fdtyping:foreign_data_typing}
          {m:brand_model} {d τ₁ τ₂}:
    d ▹ τ₁ -> τ₁ ≤ τ₂ -> d ▹ τ₂.
  Proof.
    intros.
    rewrite <- H0.
    trivial.
  Qed.

  Lemma map_rtype_meet_cons2_nin
        {ftype:foreign_type}
        {br:brand_relation} s x l1 l2 :
    ~ In s (domain l1) ->
    map_rtype_meet l1 ((s, x) :: l2)
    = map_rtype_meet l1 l2.
  Proof.
    induction l1; simpl; trivial.
    destruct a; simpl.
    intuition.
    rewrite H.
    destruct (string_dec s0 s); intuition.
  Qed.

  Lemma lookup_diff_cons2_nin {A B C} dec s x (l1:list (A*B)) (l2:list (A*C)) :
    ~ In s (domain l1) ->
  lookup_diff dec l1 ((s, x) :: l2)
  = lookup_diff dec l1 l2.
  Proof.
    induction l1; simpl; trivial.
    intuition.
    rewrite H. destruct (dec (fst a) s); intuition.
  Qed.

  Lemma lookup_diff_sublist {A B C} (dec:forall a a':A, {a=a'} + {a<>a'})
        (l1:list (A*B)) (l2:list (A*C)):
    sublist (lookup_diff dec l1 l2) l1.
  Proof.
    induction l1; simpl; trivial.
    - intuition.
    - match_destr.
      + apply sublist_skip; trivial.
      + apply sublist_cons; trivial.
  Qed.
  
  Theorem meet_preserves_data_type
          {fdata:foreign_data}
          {ftype:foreign_type}
          {fdtyping:foreign_data_typing}
          {m:brand_model} {d τ₁ τ₂}:
    d ▹ τ₁ -> d ▹ τ₂ -> d ▹ (τ₁ ⊓ τ₂).
  Proof.
    Hint Resolve data_type_ext.
    Hint Resolve data_type_not_bottom.
    Hint Resolve dtrec_closed_is_open.
    Hint Constructors data_normalized.
    
    revert d τ₂.
      induction τ₁ using rtype_rect;
        induction τ₂ using rtype_rect; simpl;
        try autorewrite with rtype_meet;
        try solve[inversion 1; subst; intros; 
                  try solve [intros; dtype_inverter_with_either; try discriminate; eauto 2
                            | eelim data_type_not_bottom; eauto
                            | unfold Top, Bottom, Unit, Nat, Float, Bool, String, Coll, Rec in *;
                              eauto 2; try r_ext]].
    - intros; dtype_inverter.
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      rtype_equalizer. subst.
      constructor.
      rewrite Forall_forall in *.
      intros ? inn.
      apply IHτ₁; intuition.
    - intros; dtype_inverter.
      invcs H1; rtype_equalizer.
      invcs H2; rtype_equalizer.
      subst.
      match_destr.
      + { clear H0.
          assert (F2:Forall2 (fun (d : string * data) (r : string * rtype) =>
                             fst d = fst r /\ snd d ▹ snd r) d
                          (rec_concat_sort
                             (map_rtype_meet srl srl0)
                             (lookup_diff string_dec rl0 srl))).
          {
            clear H7 H10 r k k0.
            revert rl rl0 srl srl0 pf pf' pf0 pf'0 H H6 H9 H8 H11.
            induction d; simpl; intros;
              invcs H8; invcs H11; simpl.
            - apply sublist_nil_r in H6; subst.
              simpl. constructor.
            - destruct H3; destruct H2; destruct a; destruct y; destruct y0.
              simpl in H, H0, H1, H2 |- *. repeat subst.
              apply sublist_cons_inv_simple in H6;
                [| apply NoDup_domain_NoDup;
                 eapply is_list_sorted_NoDup; [ eapply StringOrder.lt_strorder | ];
                 eauto].
              apply sublist_cons_inv_simple in H9;
                [| apply NoDup_domain_NoDup;
                 eapply is_list_sorted_NoDup; [ eapply StringOrder.lt_strorder | ];
                 eauto].
              destruct H6 as [[srl' [eqq subl']]|[nin subl']].
              + subst. simpl.
                invcs H.
                destruct (string_dec s1 s1); [ | congruence].
                destruct H9 as [[srl0' [eqq0 subl0']]|[nin0 subl'0]].
                * subst. simpl.
                  destruct (string_dec s1 s1); [ | congruence].
                  unfold rec_concat_sort.
                  simpl.
                  { rewrite insertion_sort_insert_forall_lt.
                    - constructor; simpl.
                      + split; eauto.
                      + rewrite map_rtype_meet_cons2_nin;
                        [rewrite lookup_diff_cons2_nin | ].
                        *  apply (IHd l' l'0); trivial;
                           try solve[eapply is_list_sorted_cons_inv; eauto].
                        * apply is_list_sorted_NoDup in pf'0;
                          [ | eapply StringOrder.lt_strorder ].
                          inversion pf'0; subst; trivial.
                        * apply is_list_sorted_NoDup in pf;
                          [ | eapply StringOrder.lt_strorder ].
                          inversion pf; subst; trivial.
                    - apply Forall_sorted.
                      apply Forall_rec_field_lt.
                      simpl.
                      rewrite domain_app.
                      rewrite map_rtype_meet_domain.
                      apply Forall_app.
                      + apply sorted_StronglySorted in pf;
                        [ | eapply StrictOrder_Transitive ].
                        simpl in pf. inversion pf; subst.
                        trivial.
                      + eapply Forall_sublist.
                        * eapply sublist_domain.
                          eapply lookup_diff_sublist.
                      * apply sorted_StronglySorted in pf'0;
                        [ | eapply StrictOrder_Transitive ].
                        simpl in pf'0. inversion pf'0; subst.
                        trivial.
                  }
                * assert (nind: ~ In s1 (domain srl0)).
                  { apply is_list_sorted_NoDup in pf'0;
                    [ | eapply StringOrder.lt_strorder ].
                    inversion pf'0; subst; trivial.
                    intros inn; apply H2. eapply sublist_In; try eapply inn.
                    eapply sublist_domain; trivial.
                  } 
                  apply (lookup_nin_none string_dec) in nind.
                  rewrite nind.
                  unfold rec_concat_sort. simpl.
                  {rewrite insertion_sort_insert_forall_lt.
                    - constructor; simpl.
                      + split; eauto.
                      + rewrite lookup_diff_cons2_nin.
                        *  apply (IHd l' l'0); trivial;
                           try solve[eapply is_list_sorted_cons_inv; eauto].
                        * apply is_list_sorted_NoDup in pf'0;
                          [ | eapply StringOrder.lt_strorder ].
                          inversion pf'0; subst; trivial.
                    - apply Forall_sorted.
                      apply Forall_rec_field_lt.
                      simpl.
                      rewrite domain_app.
                      rewrite map_rtype_meet_domain.
                      apply Forall_app.
                      + apply sorted_StronglySorted in pf;
                        [ | eapply StrictOrder_Transitive ].
                        simpl in pf. inversion pf; subst.
                        trivial.
                      + eapply Forall_sublist.
                        * eapply sublist_domain.
                          eapply lookup_diff_sublist.
                      * apply sorted_StronglySorted in pf'0;
                        [ | eapply StrictOrder_Transitive ].
                        simpl in pf'0. inversion pf'0; subst.
                        trivial.
                  }
              + assert (nind: ~ In s1 (domain srl)).
                  { apply is_list_sorted_NoDup in pf';
                    [ | eapply StringOrder.lt_strorder ].
                    inversion pf'; subst; trivial.
                    intros inn; apply H5. eapply sublist_In; try eapply inn.
                    eapply sublist_domain; trivial.
                  } 
                  apply (lookup_nin_none string_dec) in nind.
                  rewrite nind.
                  unfold rec_concat_sort.
                  unfold rec_sort.
                  rewrite <- insertion_sort_insert_middle.
                * {rewrite insertion_sort_insert_forall_lt.
                   - constructor; simpl.
                      + split; eauto.
                      + destruct H9 as [[srl0' [eqq0 subl0']]|[nin0 subl0']].
                        * subst.
                          { rewrite map_rtype_meet_cons2_nin.
                            - apply (IHd l' ); trivial;
                              try solve[eapply is_list_sorted_cons_inv; eauto].
                            - apply lookup_none_nin in nind; trivial.
                          }
                        * apply (IHd l' ); trivial;
                          try solve[eapply is_list_sorted_cons_inv; eauto].
                   - change (Forall (rec_field_lt (s1, r0))
                                     (rec_sort
                                        (map_rtype_meet srl srl0 ++
                                                        lookup_diff string_dec l'0 srl))).
                      apply Forall_sorted.
                      apply Forall_rec_field_lt.
                      simpl.
                      rewrite domain_app.
                      rewrite map_rtype_meet_domain.
                      apply Forall_app.
                      + apply sorted_StronglySorted in pf';
                        [ | eapply StrictOrder_Transitive ].
                        simpl in pf'. inversion pf'; subst.
                        eapply Forall_sublist; eauto.
                        apply sublist_domain; trivial.
                      + eapply Forall_sublist.  
                        * eapply sublist_domain.
                          eapply lookup_diff_sublist.
                      * apply sorted_StronglySorted in pf'0;
                        [ | eapply StrictOrder_Transitive ].
                        simpl in pf'0. inversion pf'0; subst.
                        trivial.
                  }
                * rewrite map_rtype_meet_domain.
                  apply lookup_none_nin in nind.
                  trivial.
          }
          econstructor; try eapply F2.
          - eapply rec_concat_sort_sorted; reflexivity.
          - unfold rec_concat_sort.
            apply Sorted_incl_sublist; try apply insertion_sort_Sorted.
            intros ? inn.
            rewrite <- rec_sort_perm in inn |- *.
            + rewrite in_app_iff in inn |- *.
              destruct inn as [inn|inn]; [tauto | ].
              right.
              apply lookup_diff_inv in inn.
              destruct inn as [inn ninn].
              destruct x.
              apply (lookup_in string_dec).
              simpl in *.
              rewrite lookup_diff_none2.
              * apply in_lookup_nodup.
                { eapply is_list_sorted_NoDup ;
                  [ eapply StringOrder.lt_strorder | ]; eauto. }
                eapply sublist_In; eauto.
              * apply lookup_nin_none; trivial.
            + apply NoDup_map_rtype_meet_lookup_diff.
              * eapply is_list_sorted_NoDup;
                [ eapply StringOrder.lt_strorder | ].
                apply sublist_domain in H6.
                eapply is_list_sorted_sublist; try eapply H6; eauto.
              * eapply is_list_sorted_NoDup;
                [ eapply StringOrder.lt_strorder | ].
                apply sublist_domain in H9.
                eapply is_list_sorted_sublist; try eapply H9; eauto.
            + rewrite domain_app, map_rtype_meet_domain.
              apply NoDup_app; eauto 2.
              * symmetry; apply lookup_diff_disjoint.
              * apply NoDup_lookup_diff; eauto.
          - intros.
            destruct k; destruct k0; simpl in H0.
            + discriminate.
            + rewrite H10 by trivial; reflexivity.
            + rewrite H7 by trivial.
              repeat rewrite lookup_diff_domain_bounded.
              * reflexivity.
              * rewrite <- (sorted_forall_same_domain H8).
                rewrite <- (sorted_forall_same_domain H11).
                reflexivity.
              * rewrite <- (sorted_forall_same_domain H8).
                rewrite  (sorted_forall_same_domain H11).
                rewrite H9; reflexivity.
            + rewrite H10 by trivial; reflexivity.
        }
      + elim n; clear n.
        assert (domeq:domain rl = domain rl0).
        {
          rewrite <- (sorted_forall_same_domain H8).
          rewrite (sorted_forall_same_domain H11).
          trivial.
        }
        destruct k; destruct k0; simpl; trivial.
        * rewrite H10 in * by trivial.
          rewrite <- domeq.
          apply sublist_domain; trivial.
        *  rewrite H7 in * by trivial.
           rewrite domeq.
           apply sublist_domain; trivial.
        * rewrite H7, H10 by trivial.
          congruence.
    - intros; dtype_inverter_with_either.
      + inversion H; rtype_equalizer. subst.
        econstructor. apply IHτ₁1; trivial.
      + inversion H; rtype_equalizer. subst.
        econstructor. apply IHτ₁2; trivial.
    - intros; dtype_inverter.
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      constructor; trivial.
      apply canon_equiv in H3.
      apply canon_equiv in H2.
      rewrite H3 in H7.
      rewrite H2 in H11.
      apply (meet_most (olattice:=brands_olattice)); trivial.
    - intros dt1 dt2.
      invcs dt1.
      invcs dt2.
      constructor.
      apply foreign_data_typing_meet; trivial.
  Qed.

  Theorem meet_data_type_iff
          {fdata:foreign_data}
          {ftype:foreign_type}
          {fdtyping:foreign_data_typing}
          {m:brand_model} d τ₁ τ₂:
    d ▹ (τ₁ ⊓ τ₂) <-> (d ▹ τ₁ /\ d ▹ τ₂).
  Proof.
    split; intros HH.
    - split.
      + rewrite meet_leq_l in HH; trivial.
      + rewrite meet_leq_r in HH; trivial.
    - apply meet_preserves_data_type; tauto.
  Qed.
  
  Lemma brands_type_Forall
        {fdata:foreign_data}
        {ftype:foreign_type}
        {fdtyping:foreign_data_typing}
        {m:brand_model} d b :
    d ▹ (brands_type b)
     <->
     (data_normalized brand_relation_brands d /\ 
    Forall (fun bb =>
              forall τ, 
                lookup string_dec brand_context_types bb = Some τ ->
                d ▹ τ
           ) b).
  Proof.
    Hint Resolve data_type_normalized.
    rewrite brands_type_alt.
    induction b; simpl; [ intuition; eauto | ].
    destruct IHb as [IHb1 IHb2].
    case_eq ( lookup string_dec brand_context_types a); intros; simpl.
    - generalize (meet_data_type_iff d r (fold_right rtype_meet ⊤ (brands_type_list b))); simpl; intros eqq.
      rewrite eqq; clear eqq.
      { split; intros [dt dtf].
        - split; [eauto | ].
          constructor.
          + rewrite H. intro; inversion 1; subst; trivial.
          + apply IHb1; trivial.
        - inversion dtf; clear dtf; subst.
          specialize (H2 _ H). split; trivial.
          apply IHb2; split; trivial.
      }
    - { split; [intros dt | intros [dt dtf]].
        - split; [ eauto | ].
          constructor.
          + rewrite H; intros; discriminate.
          + apply IHb1; trivial.
        - inversion dtf; clear dtf; subst.
          apply IHb2; split; trivial.
      } 
  Qed.

  Lemma dtbrand'
        {fdata:foreign_data}
        {ftype:foreign_type}
        {fdtyping:foreign_data_typing}
        {m:brand_model} b b' d:
      is_canon_brands brand_relation_brands b ->
      d ▹ (brands_type b) ->
      b ≤ b' ->
      data_type (dbrand b d) (Brand b').
  Proof.
    intros.
    apply brands_type_Forall in H0.
    apply dtbrand; intuition.
  Qed.

  Lemma dtbrand'_inv
        {fdata:foreign_data}
        {ftype:foreign_type}
        {fdtyping:foreign_data_typing}
        {m:brand_model} b b' d:
    data_type (dbrand b d) (Brand b') ->
    is_canon_brands brand_relation_brands b /\
    d ▹ (brands_type b) /\
    b ≤ b'.
  Proof.
    intros dt.
    apply dtbrand_inv in dt.
    intuition.
    apply brands_type_Forall; intuition.
  Qed.
    
(*
  Global Instance data_type_sub_model_prop : Proper (sub_model ==> eq ==> eq ==> impl) (data_type).
  Proof.
    unfold Proper, respectful, flip, impl; intros; subst.
    revert x y H y1 H2.
    Hint Resolve data_type_normalized.
    Hint Constructors data_type.
    induction y0; simpl; inversion 2; subst; eauto 2.
    - constructor. revert H3. apply Forall_impl_in. intros.
      generalize (Forallt_In H _ H1 _ _ H0). eauto.
    -  inversion H2; rtype_equalizer; subst.
       econstructor; eauto. revert H10.
       apply Forall2_incl; intros. intuition.
       generalize (Forallt_In H _ H1 _ _ H0); intros.
       eauto.
    - specialize (IHy0 _ _ H _ H3).
      case_eq (lookup string_dec (brand_context_types y) b); intros.
      + apply lookup_in in H0.
         generalize (Rec_subtype_In H H5 H0); intros.
         rewrite H1 in IHy0. eauto.
      + apply lookup_none_nin in H0.
         eauto.
    - apply dtbrand_unknown; trivial.
      intro inn.
      generalize (SRec_closed_in_domain H _ inn).
      congruence.
  Qed.
*)
End subtype.

Hint Resolve data_type_normalized. 

