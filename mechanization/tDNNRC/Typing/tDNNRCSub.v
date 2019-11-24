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
Require Import Arith.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import DNNRCSystem.
Require Import tDNNRC.

Section tDNNRCSub.

  Context {m:basic_model}.

  Section typ.
    Context (τconstants:tdbindings).
      
    Inductive dnnrc_base_type_sub {A plug_type:Set}
              {plug:AlgPlug plug_type} {tplug: TAlgPlug} :
      tdbindings -> @dnnrc_base _ A plug_type -> drtype -> Prop :=
    | TDNNRCGetConstant {τout} tenv s :
        forall (a:A),
          tdot τconstants s = Some τout ->
          dnnrc_base_type_sub tenv (DNNRCGetConstant a s) τout
    | TDNNRCVar {τ} tenv v :
        forall (a:A),
          lookup equiv_dec tenv v = Some τ ->
          dnnrc_base_type_sub tenv (DNNRCVar a v) τ
    | TDNNRCConst {τ} tenv c :
        forall (a:A),
          data_type (normalize_data brand_relation_brands c) τ ->
          dnnrc_base_type_sub tenv (DNNRCConst a c) (Tlocal τ)
    | TDNNRCBinop  {τ₁ τ₂ τ} tenv b e1 e2 :
        forall (a:A),
          binary_op_type b τ₁ τ₂ τ ->
          dnnrc_base_type_sub tenv e1 (Tlocal τ₁) ->
          dnnrc_base_type_sub tenv e2 (Tlocal τ₂) ->
          dnnrc_base_type_sub tenv (DNNRCBinop a b e1 e2) (Tlocal τ)
    | TDNNRCUnop {τ₁ τ} tenv u e1 :
        forall (a:A), 
          unary_op_type u τ₁ τ ->
          dnnrc_base_type_sub tenv e1 (Tlocal τ₁) ->
          dnnrc_base_type_sub tenv (DNNRCUnop a u e1) (Tlocal τ)
    | TDNNRCLet {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A), 
          dnnrc_base_type_sub tenv e1 τ₁ ->
          dnnrc_base_type_sub ((v,τ₁)::tenv) e2 τ₂ ->
          dnnrc_base_type_sub tenv (DNNRCLet a v e1 e2) τ₂
    | TDNRCForLocal {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A),
          dnnrc_base_type_sub tenv e1 (Tlocal (Coll τ₁)) ->
          dnnrc_base_type_sub ((v,(Tlocal τ₁))::tenv) e2 (Tlocal τ₂) ->
          dnnrc_base_type_sub tenv (DNNRCFor a v e1 e2) (Tlocal (Coll τ₂))
    | TDNRCForDist {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A),
          dnnrc_base_type_sub tenv e1 (Tdistr τ₁) ->
          dnnrc_base_type_sub ((v,(Tlocal τ₁))::tenv) e2 (Tlocal τ₂) ->
          dnnrc_base_type_sub tenv (DNNRCFor a v e1 e2) (Tdistr τ₂)                      
    | TDNRCIf {τ} tenv e1 e2 e3 :
        forall (a:A), 
          dnnrc_base_type_sub tenv e1 (Tlocal Bool) ->
          dnnrc_base_type_sub tenv e2 τ ->
          dnnrc_base_type_sub tenv e3 τ ->
          dnnrc_base_type_sub tenv (DNNRCIf a e1 e2 e3) τ
    | TDNNRCEither {τ τl τr} tenv ed xl el xr er :
        forall (a:A), 
          dnnrc_base_type_sub tenv ed (Tlocal (Either τl τr)) ->
          dnnrc_base_type_sub ((xl,(Tlocal τl))::tenv) el τ ->
          dnnrc_base_type_sub ((xr,(Tlocal τr))::tenv) er τ ->
          dnnrc_base_type_sub tenv (DNNRCEither a ed xl el xr er) τ
    | TDNNRCCollect {τ} tenv e :
        forall (a:A),
          dnnrc_base_type_sub tenv e (Tdistr τ) ->
          dnnrc_base_type_sub tenv (DNNRCCollect a e) (Tlocal (Coll τ))
    | TDNNRCDispatch {τ} tenv e :
        forall (a:A),
          dnnrc_base_type_sub tenv e (Tlocal (Coll τ)) ->
          dnnrc_base_type_sub tenv (DNNRCDispatch a e) (Tdistr τ)
    (* Note: algebra 'plugged' expression is only well typed within distributed
         NNNRC if it returns a collection *)
    | TDNNRCAlg {τout} tenv tbindings op nl :
        forall (a:A),
          Forall2 (fun n τ => fst n = fst τ
                              /\ dnnrc_base_type_sub tenv (snd n) (Tdistr (snd τ)))
                  nl tbindings ->
          plug_typing op tbindings (Coll τout) -> 
          dnnrc_base_type_sub tenv (DNNRCAlg a op nl) (Tdistr τout)
    | TDNNRCSubsumption {τenv τout} τenv' τout' e:
        tdbindings_sub τenv' τenv ->
        drtype_sub τout τout' ->
        dnnrc_base_type_sub τenv e τout ->
        dnnrc_base_type_sub τenv' e τout'
    .

    Global Instance dnnrc_base_type_sub_proper {A plug_type:Set} {plug:AlgPlug plug_type} {tplug: TAlgPlug} :
      Proper (tdbindings_sub --> eq ==> drtype_sub ==> impl) (dnnrc_base_type_sub (A:=A)).
    Proof.
      unfold Proper, respectful, flip, impl; intros.
      subst.
      eapply TDNNRCSubsumption; eauto.
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

  End typ.

  Section lift.
    
    Lemma dnnrc_base_type_to_dnnrc_base_type_sub {A} (plug_type:Set) (plug:AlgPlug plug_type) {tplug:TAlgPlug} {τc} {τ} (tenv:tdbindings) (e:@dnnrc_base _ A plug_type) :
      dnnrc_base_type τc tenv e τ ->
      dnnrc_base_type_sub τc tenv e τ.
    Proof.
      Hint Constructors dnnrc_base_type_sub.
      revert tenv τ.
      induction e; simpl; intros tenv τ dt; invcs dt; eauto.
      - econstructor; try eassumption.
        revert H5.
        apply Forall2_incl.
        rewrite Forall_forall in H.
        intros ? ? inn1 inn2 [eqq1 eqq2].
        auto.
    Qed.
    
  End lift.
  
(** Main lemma for the type correctness of DNNNRC *)
  Theorem typed_dnnrc_base_yields_typed_data {A} {plug_type:Set} (plug:AlgPlug plug_type) {tplug:TAlgPlug} {τc} {τ} (cenv env:dbindings) (tenv:tdbindings) (e:@dnnrc_base _ A plug_type) :
    dbindings_type cenv τc ->
    dbindings_type env tenv ->
    dnnrc_base_type_sub τc tenv e τ ->
    (exists x, (dnnrc_base_eval brand_relation_brands cenv env e) = Some x /\ (ddata_type x τ)).
  Proof.
    intro Hcenv; intros.
    revert env H.
    dependent induction H0; simpl; intros.
    - unfold tdot in *.
      unfold edot in *.
      destruct (Forall2_lookupr_some Hcenv H) as [? [eqq1 eqq2]].
      rewrite eqq1.
      eauto.
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
    - specialize (IHdnnrc_base_type_sub1 env H0); specialize (IHdnnrc_base_type_sub2 env H0).
      elim IHdnnrc_base_type_sub1; intros; clear IHdnnrc_base_type_sub1;
        elim IHdnnrc_base_type_sub2; intros; clear IHdnnrc_base_type_sub2.
      elim H1; clear H1; intros.
      elim H2; clear H2; intros.
      rewrite H1; rewrite H2.
      simpl.
      inversion H3; clear H3; subst.
      inversion H4; clear H4; subst.
      elim (@typed_binary_op_yields_typed_data _ _ _ _ _ _ τ₁ τ₂ τ _ _ b H7 H6 H); intros.
      elim H3; clear H3; intros.
      exists (Dlocal x); simpl.
      split.
      + rewrite H3; reflexivity.
      + constructor; assumption.
    - specialize (IHdnnrc_base_type_sub env H1).
      elim IHdnnrc_base_type_sub; intros; clear IHdnnrc_base_type_sub.
      elim H2; clear H2; intros.
      rewrite H2; clear H2.
      inversion H3; clear H3; intros; subst.
      elim (@typed_unary_op_yields_typed_data _ _ _ _ _ _ _ τ₁ τ _ u H5 H); intros.
      elim H2; clear H2; intros.
      exists (Dlocal x); simpl.
      split.
      + rewrite H2; reflexivity.
      + constructor; assumption.
    - destruct (IHdnnrc_base_type_sub1 _ H) as [?[re1 ?]].
      destruct (IHdnnrc_base_type_sub2 ((v,x)::env)) as [?[re2 ?]].
      + apply Forall2_cons; intuition.
      + unfold var in *.
        rewrite re1.
        assert ((@dnnrc_base_eval (@basic_model_runtime m) A plug_type
             (@brand_relation_brands
                (@brand_model_relation (@basic_model_foreign_type m)
                   (@basic_model_brand_model m))) cenv plug
             (@cons (prod string (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
                (@pair string (@ddata (@foreign_runtime_data (@basic_model_runtime m))) v x)
                env) e2) = (@dnnrc_base_eval (@basic_model_runtime m) A plug_type
             (@brand_relation_brands
                (@brand_model_relation (@basic_model_foreign_type m)
                   (@basic_model_brand_model m))) cenv plug
             (@cons
                (prod DNNRCBase.var (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
                (@pair DNNRCBase.var (@ddata (@foreign_runtime_data (@basic_model_runtime m)))
                   v x) env) e2)) by reflexivity.
        rewrite H2 in re2; clear H2.
        rewrite re2.
        eauto.
    - specialize (IHdnnrc_base_type_sub1 env H).
      elim IHdnnrc_base_type_sub1; intros; clear IHdnnrc_base_type_sub1.
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
        assert (exists x1, lift_map
           (fun d1 : data =>
            olift checkLocal
              (dnnrc_base_eval brand_relation_brands cenv ((v, Dlocal d1) :: env) e2))
           dl = Some x1 /\ (Dlocal (dcoll x1)) = x0).
        revert H1.
        assert (@lift_map (@data (@foreign_runtime_data (@basic_model_runtime m)))
              (@data (@foreign_runtime_data (@basic_model_runtime m)))
              (fun d1 : @data (@foreign_runtime_data (@basic_model_runtime m)) =>
               @olift (@ddata (@foreign_runtime_data (@basic_model_runtime m)))
                 (@data (@foreign_runtime_data (@basic_model_runtime m)))
                 (@checkLocal (@foreign_runtime_data (@basic_model_runtime m)))
                 (@dnnrc_base_eval (@basic_model_runtime m) A plug_type
                    (@brand_relation_brands
                       (@brand_model_relation (@basic_model_foreign_type m)
                          (@basic_model_brand_model m))) cenv plug
                    (@cons
                       (prod DNNRCBase.var
                          (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
                       (@pair DNNRCBase.var
                          (@ddata (@foreign_runtime_data (@basic_model_runtime m))) v
                          (@Dlocal (@foreign_runtime_data (@basic_model_runtime m)) d1)) env)
                    e2)) dl = (@lift_map (@data (@foreign_runtime_data (@basic_model_runtime m)))
             (@data (@foreign_runtime_data (@basic_model_runtime m)))
             (fun d1 : @data (@foreign_runtime_data (@basic_model_runtime m)) =>
              @olift (@ddata (@foreign_runtime_data (@basic_model_runtime m)))
                (@data (@foreign_runtime_data (@basic_model_runtime m)))
                (@checkLocal (@foreign_runtime_data (@basic_model_runtime m)))
                (@dnnrc_base_eval (@basic_model_runtime m) A plug_type
                   (@brand_relation_brands
                      (@brand_model_relation (@basic_model_foreign_type m)
                         (@basic_model_brand_model m))) cenv plug
                   (@cons
                      (prod string (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
                      (@pair string (@ddata (@foreign_runtime_data (@basic_model_runtime m))) v
                         (@Dlocal (@foreign_runtime_data (@basic_model_runtime m)) d1)) env) e2))
             dl)) by reflexivity.
        rewrite H1; clear H1.
        elim (lift_map
                (fun d1 : data =>
                   olift checkLocal
                         (dnnrc_base_eval brand_relation_brands cenv ((v, Dlocal d1) :: env) e2)) dl); intros.
        inversion H1; simpl in *. subst; clear H1;
        exists a1; split; congruence.
        congruence.
        elim H3; clear H3; intros.
        elim H3; clear H3; intros.
        assert ((@lift_map (@data (@foreign_runtime_data (@basic_model_runtime m)))
            (@data (@foreign_runtime_data (@basic_model_runtime m)))
            (fun d1 : @data (@foreign_runtime_data (@basic_model_runtime m)) =>
             @olift (@ddata (@foreign_runtime_data (@basic_model_runtime m)))
               (@data (@foreign_runtime_data (@basic_model_runtime m)))
               (@checkLocal (@foreign_runtime_data (@basic_model_runtime m)))
               (@dnnrc_base_eval (@basic_model_runtime m) A plug_type
                  (@brand_relation_brands
                     (@brand_model_relation (@basic_model_foreign_type m)
                        (@basic_model_brand_model m))) cenv plug
                  (@cons
                     (prod string (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
                     (@pair string (@ddata (@foreign_runtime_data (@basic_model_runtime m))) v
                        (@Dlocal (@foreign_runtime_data (@basic_model_runtime m)) d1)) env) e2))
            dl) = (@lift_map (@data (@foreign_runtime_data (@basic_model_runtime m)))
                      (@data (@foreign_runtime_data (@basic_model_runtime m)))
                      (fun d1 : @data (@foreign_runtime_data (@basic_model_runtime m)) =>
                       @olift (@ddata (@foreign_runtime_data (@basic_model_runtime m)))
                         (@data (@foreign_runtime_data (@basic_model_runtime m)))
                         (@checkLocal (@foreign_runtime_data (@basic_model_runtime m)))
                         (@dnnrc_base_eval (@basic_model_runtime m) A plug_type
                            (@brand_relation_brands
                               (@brand_model_relation (@basic_model_foreign_type m)
                                  (@basic_model_brand_model m))) cenv plug
                            (@cons
                               (prod DNNRCBase.var
                                  (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
                               (@pair DNNRCBase.var
                                  (@ddata (@foreign_runtime_data (@basic_model_runtime m))) v
                                  (@Dlocal (@foreign_runtime_data (@basic_model_runtime m)) d1))
                               env) e2)) dl)) by reflexivity.
        rewrite <- H5; clear H5.
        rewrite H3.
        rewrite <- H4 in *; clear H1 H3 H4; simpl.
        specialize (IHdnnrc_base_type_sub2 ((v,Dlocal a0)::env)).
        assert (dbindings_type ((v, Dlocal a0) :: env) ((v, Tlocal τ₁) :: tenv)).
        unfold dbindings_type.
        apply Forall2_cons; try assumption.
        simpl; split; try reflexivity.
        assert (r = τ₁) by (apply rtype_fequal; assumption).
        rewrite H1 in *; clear H1 x.
        constructor. apply (H0 a0); left; reflexivity.
        specialize (IHdnnrc_base_type_sub2 H1); clear H1.
        elim IHdnnrc_base_type_sub2; clear IHdnnrc_base_type_sub2; intros.
        elim H1; clear H1; intros.
        assert ((@dnnrc_base_eval (@basic_model_runtime m) A plug_type
            (@brand_relation_brands
               (@brand_model_relation (@basic_model_foreign_type m)
                  (@basic_model_brand_model m))) cenv plug
            (@cons (prod string (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
               (@pair string (@ddata (@foreign_runtime_data (@basic_model_runtime m))) v
                  (@Dlocal (@foreign_runtime_data (@basic_model_runtime m)) a0)) env) e2) =
               (@dnnrc_base_eval (@basic_model_runtime m) A plug_type
                    (@brand_relation_brands
                       (@brand_model_relation (@basic_model_foreign_type m)
                          (@basic_model_brand_model m))) cenv plug
                    (@cons
                       (prod DNNRCBase.var
                          (@ddata (@foreign_runtime_data (@basic_model_runtime m))))
                       (@pair DNNRCBase.var
                          (@ddata (@foreign_runtime_data (@basic_model_runtime m))) v
                          (@Dlocal (@foreign_runtime_data (@basic_model_runtime m)) a0)) env)
                    e2)) by reflexivity.
        rewrite <- H4; clear H4.
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
    - admit.
    - specialize (IHdnnrc_base_type_sub1 env H); specialize (IHdnnrc_base_type_sub2 env H); specialize (IHdnnrc_base_type_sub3 env H).
      elim IHdnnrc_base_type_sub1; intros; clear IHdnnrc_base_type_sub1;
      elim IHdnnrc_base_type_sub2; intros; clear IHdnnrc_base_type_sub2;
      elim IHdnnrc_base_type_sub3; intros; clear IHdnnrc_base_type_sub3.
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
    - destruct (IHdnnrc_base_type_sub1 _ H) as [dd [evald typd]].
      inversion typd; clear typd; subst.
      apply data_type_Either_inv in H2.
      rewrite evald.
      simpl.
      destruct H2 as [[ddl[? typd]]|[ddr[? typd]]]; subst.
      + destruct (IHdnnrc_base_type_sub2 ((xl,Dlocal ddl)::env));
        unfold dbindings_type in *; auto.
        apply Forall2_cons; auto; split; [auto|constructor;auto].
        exists x; auto.
      + destruct (IHdnnrc_base_type_sub3 ((xr,Dlocal ddr)::env));
        unfold dbindings_type in *; auto.
        apply Forall2_cons; auto; split; [auto|constructor;auto].
        exists x; auto.
    - elim (IHdnnrc_base_type_sub env H); intros.
      elim H1; clear H1; intros.
      rewrite H1; simpl.
      inversion H2; clear H2; subst.
      exists (Dlocal (dcoll dl)).
      simpl. split; [reflexivity|].
      constructor.
      constructor.
      assumption.
    - elim (IHdnnrc_base_type_sub env H); intros.
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
      destruct (IHdnnrc_base_type_sub _ H2) as [dd [dd_eval dd_typ]].
      rewrite H0 in dd_typ.
      eauto.
  Admitted.

End tDNNRCSub.

