  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Program.
  Require Import EquivDec Morphisms.

  Require Import Utils BasicSystem.
  Require Import DNNRC TDNRC.

  Section TDNRCsub.

    Context {m:basic_model}.

    Section typ.
      
  Inductive dnrc_type_sub `{tplug: TAlgPlug} {A} : tdbindings -> @dnrc _ A T -> drtype -> Prop :=
      | TDNRCVar {τ} tenv v : forall (a:A), lookup equiv_dec tenv v = Some τ -> dnrc_type_sub tenv (DNRCVar a v) τ
      | TDNRCConst {τ} tenv c : forall (a:A), data_type (normalize_data brand_relation_brands c) τ -> dnrc_type_sub tenv (DNRCConst a c) (Tlocal τ)
      | TDNRCBinop  {τ₁ τ₂ τ} tenv b e1 e2 :
          forall (a:A),
            binOp_type b τ₁ τ₂ τ ->
            dnrc_type_sub tenv e1 (Tlocal τ₁) ->
            dnrc_type_sub tenv e2 (Tlocal τ₂) ->
            dnrc_type_sub tenv (DNRCBinop a b e1 e2) (Tlocal τ)
      | TDNRCUnop {τ₁ τ} tenv u e1 :
          forall (a:A), 
            unaryOp_type u τ₁ τ ->
            dnrc_type_sub tenv e1 (Tlocal τ₁) ->
            dnrc_type_sub tenv (DNRCUnop a u e1) (Tlocal τ)
      | TDNRCLet {τ₁ τ₂} v tenv e1 e2 :
          forall (a:A), 
            dnrc_type_sub tenv e1 τ₁ ->
            dnrc_type_sub ((v,τ₁)::tenv) e2 τ₂ ->
            dnrc_type_sub tenv (DNRCLet a v e1 e2) τ₂
      | TDNRCFor {τ₁ τ₂} v tenv e1 e2 :
          forall (a:A), 
            dnrc_type_sub tenv e1 (Tlocal (Coll τ₁)) ->
            dnrc_type_sub ((v,(Tlocal τ₁))::tenv) e2 (Tlocal τ₂) ->
            dnrc_type_sub tenv (DNRCFor a v e1 e2) (Tlocal (Coll τ₂))
      | TDNRCIf {τ} tenv e1 e2 e3 :
          forall (a:A), 
            dnrc_type_sub tenv e1 (Tlocal Bool) ->
            dnrc_type_sub tenv e2 τ ->
            dnrc_type_sub tenv e3 τ ->
            dnrc_type_sub tenv (DNRCIf a e1 e2 e3) τ
      | TDNRCEither {τ τl τr} tenv ed xl el xr er :
          forall (a:A), 
            dnrc_type_sub tenv ed (Tlocal (Either τl τr)) ->
            dnrc_type_sub ((xl,(Tlocal τl))::tenv) el τ ->
            dnrc_type_sub ((xr,(Tlocal τr))::tenv) er τ ->
            dnrc_type_sub tenv (DNRCEither a ed xl el xr er) τ
      | TDNRCCollect {τ} tenv e :
          forall (a:A),
            dnrc_type_sub tenv e (Tdistr τ) ->
            dnrc_type_sub tenv (DNRCCollect a e) (Tlocal (Coll τ))
      | TDNRCDispatch {τ} tenv e :
          forall (a:A),
            dnrc_type_sub tenv e (Tlocal (Coll τ)) ->
            dnrc_type_sub tenv (DNRCDispatch a e) (Tdistr τ)
      (* Note: algebra 'plugged' expression is only well typed within distributed
         NNRC if it returns a collection *)
      | TDNRCAlg {τl τout} tenv tbindings plug_abst tclosure nl :
        forall (a:A),
          Forall2 (fun n τ => dnrc_type_sub tenv n τ) nl τl ->
          tcombine (fst tclosure) τl = Some tbindings ->
           plug_typing (snd tclosure) tbindings (Coll τout) -> 
           dnrc_type_sub tenv (DNRCAlg a plug_abst nl) (Tdistr τout)
      | TDNRCSubsumption {τenv τout} τenv' τout' e:
         tdbindings_sub τenv' τenv ->
         drtype_sub τout τout' ->
         dnrc_type_sub τenv e τout ->
         dnrc_type_sub τenv' e τout'
      .

      Global Instance dnrc_type_sub_proper `{tplug: TAlgPlug} {A} :
        Proper (tdbindings_sub --> eq ==> drtype_sub ==> impl) (dnrc_type_sub (A:=A)).
      Proof.
        unfold Proper, respectful, flip, impl; intros.
        subst.
        eapply TDNRCSubsumption; eauto.
      Qed.
      
     Global Instance dbindings_type_proper :
       Proper (eq ==> tdbindings_sub ==> impl) dbindings_type.
     Proof.
       unfold Proper, respectful, flip, impl, tdbindings_sub, dbindings_type; intros.
       subst.
       revert y y0 H0 H1.
       induction x0; intros x y0 F1 F2
       ; invcs F1; invcs F2; trivial.
       destruct a; destruct y; destruct x1; intuition; simpl in *; subst.
       rewrite H0 in H2.
       auto.
     Qed.    

      (* Print dnrc_type_sub_ind. We will need a special inductive principle because of the list of expressions in TDNRAlg *)
      
  End typ.

    Section lift.

      Lemma dnrc_type_to_dnrc_type_sub {A} {T} (plug:AlgPlug) {tplug:TAlgPlug} {τ} (env:dbindings) (tenv:tdbindings) (e:@dnrc _ A T) :
        dnrc_type tenv e τ ->
        dnrc_type_sub tenv e τ.
      Proof.
        Hint Constructors dnrc_type_sub.
        induction 1; trivial; eauto 2.
        econstructor; eauto.
        (* same problem with the induction principle.  I should fix this *)
        - admit.
      Admitted.

    End lift.

    (** Main lemma for the type correctness of DNNRC *)
    Theorem typed_dnrc_yields_typed_data {A} {T} (plug:AlgPlug) {tplug:TAlgPlug} {τ} (env:dbindings) (tenv:tdbindings) (e:@dnrc _ A T) :
    dbindings_type env tenv ->
    dnrc_type_sub tenv e τ ->
    (exists x, (dnrc_eval env e) = Some x /\ (ddata_type x τ)).
    Proof.
    intros.
    revert env H.
    dependent induction H0; simpl; intros.
    - unfold dbindings_type in *.
      dependent induction H0.
      simpl in *; congruence.
      simpl in *.
      destruct x; simpl in *.
      elim H0; clear H0; intros.
      destruct y; simpl in *.
      rewrite H0 in *; clear H0.
      revert H.
      elim (equiv_dec v s0); intros.
      exists d.
      inversion H.
      rewrite H3 in *; clear H3 H a.
      split; [reflexivity|assumption].
      specialize (IHForall2 H); clear H.
      assumption.
    - exists (Dlocal (normalize_data brand_relation_brands c)).
      intros. split; [reflexivity|constructor; assumption].
    - specialize (IHdnrc_type_sub1 env H0); specialize (IHdnrc_type_sub2 env H0).
      elim IHdnrc_type_sub1; intros; clear IHdnrc_type_sub1;
      elim IHdnrc_type_sub2; intros; clear IHdnrc_type_sub2.
      elim H1; clear H1; intros.
      elim H2; clear H2; intros.
      rewrite H1; rewrite H2.
      simpl.
      inversion H3; clear H3; subst.
      inversion H4; clear H4; subst.
      elim (@typed_binop_yields_typed_data _ _ _ _ _ _ _ _ τ₁ τ₂ τ _ _ b H7 H6 H); intros.
      elim H3; clear H3; intros.
      exists (Dlocal x); simpl.
      split.
      + rewrite H3; reflexivity.
      + constructor; assumption.
    - specialize (IHdnrc_type_sub env H1).
      elim IHdnrc_type_sub; intros; clear IHdnrc_type_sub.
      elim H2; clear H2; intros.
      rewrite H2; clear H2.
      inversion H3; clear H3; intros; subst.
      elim (@typed_unop_yields_typed_data _ _ _ _ _ _ _ _ τ₁ τ _ u H5 H); intros.
      elim H2; clear H2; intros.
      exists (Dlocal x); simpl.
      split.
      + rewrite H2; reflexivity.
      + constructor; assumption.
    - destruct (IHdnrc_type_sub1 _ H) as [?[re1 ?]].
      destruct (IHdnrc_type_sub2 ((v,x)::env)) as [?[re2 ?]].
      + apply Forall2_cons; intuition.
      + unfold var in *.
        rewrite re1, re2.
        eauto.
    - specialize (IHdnrc_type_sub1 env H).
      elim IHdnrc_type_sub1; intros; clear IHdnrc_type_sub1.
      elim H0; clear H0; intros.
      rewrite H0; clear H0; simpl.
      inversion H1; clear H1; subst.
      dependent induction H3.
      induction dl; simpl in *.
      + exists (Dlocal (dcoll [])).
        split; [reflexivity|].
        constructor; apply dtcoll; apply Forall_nil.
      + rewrite Forall_forall in *.
        simpl in H0.
        assert (forall x : data, In x dl -> data_type x r)
          by (intros; apply (H0 x0); right; assumption).
        specialize (IHdl H1); clear H1.
        elim IHdl; intros; clear IHdl.
        elim H1; clear H1; intros.
        unfold lift in H1.
        unfold var in *.
        assert (exists x1, rmap
           (fun d1 : data =>
            olift checkLocal
              (dnrc_eval ((v, Dlocal d1) :: env) e2))
           dl = Some x1 /\ (Dlocal (dcoll x1)) = x0).
        revert H1.
        elim (rmap
       (fun d1 : data =>
        olift checkLocal
              (dnrc_eval ((v, Dlocal d1) :: env) e2)) dl); intros.
        inversion H1; simpl in *. subst; clear H1.
        exists a1; split; reflexivity.
        congruence.
        elim H3; clear H3; intros.
        elim H3; clear H3; intros.
        rewrite H3.
        rewrite <- H4 in *; clear H1 H3 H4; simpl.
        specialize (IHdnrc_type_sub2 ((v,Dlocal a0)::env)).
        assert (dbindings_type ((v, Dlocal a0) :: env) ((v, Tlocal τ₁) :: tenv)).
        unfold dbindings_type.
        apply Forall2_cons; try assumption.
        simpl; split; try reflexivity.
        assert (r = τ₁) by (apply rtype_fequal; assumption).
        rewrite H1 in *; clear H1 x.
        constructor. apply (H0 a0); left; reflexivity.
        specialize (IHdnrc_type_sub2 H1); clear H1.
        elim IHdnrc_type_sub2; clear IHdnrc_type_sub2; intros.
        elim H1; clear H1; intros.
        rewrite H1; simpl.
        inversion H3; clear H3; subst.
        exists (Dlocal (dcoll (d::x1))); split; try reflexivity.
        constructor; apply dtcoll.
        rewrite Forall_forall; simpl; intros.
        elim H3; clear H3; intros.
        rewrite H3 in *; assumption.
        inversion H2; clear H2; subst.
        dependent induction H7.
        rewrite Forall_forall in *.
        assert (r0 = τ₂) by (apply rtype_fequal; assumption).
        subst.
        apply (H2 x2); assumption.
    - specialize (IHdnrc_type_sub1 env H); specialize (IHdnrc_type_sub2 env H); specialize (IHdnrc_type_sub3 env H).
      elim IHdnrc_type_sub1; intros; clear IHdnrc_type_sub1;
      elim IHdnrc_type_sub2; intros; clear IHdnrc_type_sub2;
      elim IHdnrc_type_sub3; intros; clear IHdnrc_type_sub3.
      elim H0; clear H0; intros.
      elim H1; clear H1; intros.
      elim H2; clear H2; intros.
      rewrite H0.
      simpl.
      inversion H3; clear H3; subst.
      dependent induction H8.
      destruct b.
      + rewrite H1.
        exists x0; split; [reflexivity|assumption].
      + rewrite H2.
        exists x1; split; [reflexivity|assumption].
    - destruct (IHdnrc_type_sub1 _ H) as [dd [evald typd]].
      inversion typd; clear typd; subst.
      apply data_type_Either_inv in H2.
      rewrite evald.
      simpl.
      destruct H2 as [[ddl[? typd]]|[ddr[? typd]]]; subst.
      + destruct (IHdnrc_type_sub2 ((xl,Dlocal ddl)::env));
        unfold dbindings_type in *; auto.
        apply Forall2_cons; auto; split; [auto|constructor;auto].
        exists x; auto.
      + destruct (IHdnrc_type_sub3 ((xr,Dlocal ddr)::env));
        unfold dbindings_type in *; auto.
        apply Forall2_cons; auto; split; [auto|constructor;auto].
        exists x; auto.
    - elim (IHdnrc_type_sub env H); intros.
      elim H1; clear H1; intros.
      rewrite H1; simpl.
      inversion H2; clear H2; subst.
      exists (Dlocal (dcoll dl)).
      simpl. split; [reflexivity|].
      constructor.
      constructor.
      assumption.
    - elim (IHdnrc_type_sub env H); intros.
      elim H1; clear H1; intros.
      rewrite H1; simpl.
      inversion H2; clear H2; subst; simpl.
      dependent induction H5.
      exists (Ddistr dl).
      simpl. split; [reflexivity|].
      constructor.
      assert (r = τ) by (apply rtype_fequal; assumption).
      subst; assumption.
    - admit.
      (* We will need a special inductive principle because of the list of expressions in TDNRAlg *)
    - rewrite H in H2.
      destruct (IHdnrc_type_sub _ H2) as [dd [dd_eval dd_typ]].
      rewrite H0 in dd_typ.
      eauto.
  Admitted.

  End TDNRCsub.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
