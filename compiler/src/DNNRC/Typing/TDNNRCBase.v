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
Require Import DNNRCBase.

Section TDNNRCBase.

  Context {m:basic_model}.
  Section tplug.
      
    Class TAlgPlug {plug_type:Set} {plug:AlgPlug plug_type} :=
      mkTAlgPlug {
          plug_typing : plug_type -> tbindings -> rtype -> Prop;
        }.
    
  End tplug.

  (* Global Arguments TAlgPlug plug_type {plug} : clear implicits.  *)

  (** Typing rules for NNRC *)
  Section typ.
    Context (τconstants:tdbindings).

    (* When applying the parameters to an algebra closure, we need to check that
         those parameters are distributed *)
    Fixpoint tcombine (l:list string) (l':list drtype) {struct l} : option tbindings :=
      match l with
      | [] => Some []
      | x :: tl =>
        match l' with
        | [] => Some []
        | (Tlocal _) :: _ => None
        | (Tdistr y) :: tl' =>
          match tcombine tl tl' with
          | Some tl'' => Some ((x,y) :: tl'')
          | None => None
          end
        end
      end.

    Inductive dnnrc_base_type `{tplug: TAlgPlug} {A} : tdbindings -> @dnnrc_base _ A plug_type -> drtype -> Prop :=
    | TDNNRCGetConstant {τout} tenv s :
        forall (a:A),
          tdot τconstants s = Some τout ->
          dnnrc_base_type tenv (DNNRCGetConstant a s) τout
    | TDNNRCVar {τout} tenv v :
        forall (a:A),
          lookup equiv_dec tenv v = Some τout ->
          dnnrc_base_type tenv (DNNRCVar a v) τout
    | TDNNRCConst {τout} tenv c :
        forall (a:A),
          data_type (normalize_data brand_relation_brands c) τout ->
          dnnrc_base_type tenv (DNNRCConst a c) (Tlocal τout)
    | TDNNRCBinop  {τ₁ τ₂ τout} tenv b e1 e2 :
        forall (a:A),
          binary_op_type b τ₁ τ₂ τout ->
          dnnrc_base_type tenv e1 (Tlocal τ₁) ->
          dnnrc_base_type tenv e2 (Tlocal τ₂) ->
          dnnrc_base_type tenv (DNNRCBinop a b e1 e2) (Tlocal τout)
    | TDNNRCUnop {τ₁ τout} tenv u e1 :
        forall (a:A), 
          unary_op_type u τ₁ τout ->
          dnnrc_base_type tenv e1 (Tlocal τ₁) ->
          dnnrc_base_type tenv (DNNRCUnop a u e1) (Tlocal τout)
    | TDNNRCLet {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A), 
          dnnrc_base_type tenv e1 τ₁ ->
          dnnrc_base_type ((v,τ₁)::tenv) e2 τ₂ ->
          dnnrc_base_type tenv (DNNRCLet a v e1 e2) τ₂
    | TDNNRCForLocal {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A),
          dnnrc_base_type tenv e1 (Tlocal (Coll τ₁)) ->
          dnnrc_base_type ((v,(Tlocal τ₁))::tenv) e2 (Tlocal τ₂) ->
          dnnrc_base_type tenv (DNNRCFor a v e1 e2) (Tlocal (Coll τ₂))
    | TDNNRCForDist {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A),
          dnnrc_base_type tenv e1 (Tdistr τ₁) ->
          dnnrc_base_type ((v,(Tlocal τ₁))::tenv) e2 (Tlocal τ₂) ->
          dnnrc_base_type tenv (DNNRCFor a v e1 e2) (Tdistr τ₂)
    | TDNNRCIf {τout} tenv e1 e2 e3 :
        forall (a:A), 
          dnnrc_base_type tenv e1 (Tlocal Bool) ->
          dnnrc_base_type tenv e2 τout ->
          dnnrc_base_type tenv e3 τout ->
          dnnrc_base_type tenv (DNNRCIf a e1 e2 e3) τout
    | TDNNRCEither {τout τl τr} tenv ed xl el xr er :
        forall (a:A), 
          dnnrc_base_type tenv ed (Tlocal (Either τl τr)) ->
          dnnrc_base_type ((xl,(Tlocal τl))::tenv) el τout ->
          dnnrc_base_type ((xr,(Tlocal τr))::tenv) er τout ->
          dnnrc_base_type tenv (DNNRCEither a ed xl el xr er) τout
    | TDNNRCCollect {τ} tenv e :
        forall (a:A),
          dnnrc_base_type tenv e (Tdistr τ) ->
          dnnrc_base_type tenv (DNNRCCollect a e) (Tlocal (Coll τ))
    | TDNNRCDispatch {τ} tenv e :
        forall (a:A),
          dnnrc_base_type tenv e (Tlocal (Coll τ)) ->
          dnnrc_base_type tenv (DNNRCDispatch a e) (Tdistr τ)
    (* Note: algebra 'plugged' expression is only well typed within distributed
         NNNRC if it returns a collection *)
    | TDNNRCAlg {τout} tenv tbindings op nl :
        forall (a:A),
          Forall2 (fun n τ => fst n = fst τ
                              /\ dnnrc_base_type tenv (snd n) (Tdistr (snd τ)))
                  nl tbindings ->
          plug_typing op tbindings (Coll τout) -> 
          dnnrc_base_type tenv (DNNRCAlg a op nl) (Tdistr τout)
    .

    (* Print dnnrc_base_type_ind. We will need a special inductive principle because of the list of expressions in TDNRAlg *)
  End typ.

  (** Main lemma for the type correctness of DNNRC *)

  Theorem typed_dnnrc_base_yields_typed_data {A:Set} {plug_type:Set} {τc} {τ} `{tplug:TAlgPlug plug_type} (cenv env:dbindings) (tenv:tdbindings) (e:@dnnrc_base _ A plug_type) :
    dbindings_type cenv τc ->
    dbindings_type env tenv ->
    dnnrc_base_type τc tenv e τ ->
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
    - specialize (IHdnnrc_base_type1 env H0); specialize (IHdnnrc_base_type2 env H0).
      elim IHdnnrc_base_type1; intros; clear IHdnnrc_base_type1;
      elim IHdnnrc_base_type2; intros; clear IHdnnrc_base_type2.
      elim H1; clear H1; intros.
      elim H2; clear H2; intros.
      rewrite H1; rewrite H2.
      simpl.
      inversion H3; clear H3; subst.
      inversion H4; clear H4; subst.
      elim (@typed_binary_op_yields_typed_data _ _ _ _ _ _ τ₁ τ₂ τout _ _ b H7 H6 H); intros.
      elim H3; clear H3; intros.
      exists (Dlocal x); simpl.
      split.
      + rewrite H3; reflexivity.
      + constructor; assumption.
    - specialize (IHdnnrc_base_type env H1).
      elim IHdnnrc_base_type; intros; clear IHdnnrc_base_type.
      elim H2; clear H2; intros.
      rewrite H2; clear H2.
      inversion H3; clear H3; intros; subst.
      elim (@typed_unary_op_yields_typed_data _ _ _ _ _ _ _ τ₁ τout _ u H5 H); intros.
      elim H2; clear H2; intros.
      exists (Dlocal x); simpl.
      split.
      + rewrite H2; reflexivity.
      + constructor; assumption.
    - destruct (IHdnnrc_base_type1 _ H) as [?[re1 ?]].
      destruct (IHdnnrc_base_type2 ((v,x)::env)) as [?[re2 ?]].
      + apply Forall2_cons; intuition.
      + unfold var in *.
        rewrite re1, re2.
        eauto.
    - specialize (IHdnnrc_base_type1 env H).
      elim IHdnnrc_base_type1; intros; clear IHdnnrc_base_type1.
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
        elim (lift_map
       (fun d1 : data =>
        olift checkLocal
              (dnnrc_base_eval brand_relation_brands cenv ((v, Dlocal d1) :: env) e2)) dl); intros.
        inversion H1; simpl in *. subst; clear H1.
        exists a1; split; reflexivity.
        congruence.
        elim H3; clear H3; intros.
        elim H3; clear H3; intros.
        rewrite H3.
        rewrite <- H4 in *; clear H1 H3 H4; simpl.
        specialize (IHdnnrc_base_type2 ((v,Dlocal a0)::env)).
        assert (dbindings_type ((v, Dlocal a0) :: env) ((v, Tlocal τ₁) :: tenv)).
        unfold dbindings_type.
        apply Forall2_cons; try assumption.
        simpl; split; try reflexivity.
        assert (r = τ₁) by (apply rtype_fequal; assumption).
        rewrite H1 in *; clear H1 x.
        constructor. apply (H0 a0); left; reflexivity.
        specialize (IHdnnrc_base_type2 H1); clear H1.
        elim IHdnnrc_base_type2; clear IHdnnrc_base_type2; intros.
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
    - specialize (IHdnnrc_base_type1 env H).
      elim IHdnnrc_base_type1; intros; clear IHdnnrc_base_type1.
      elim H0; clear H0; intros.
      rewrite H0; clear H0; simpl.
      inversion H1; clear H1; subst.
      induction dl; simpl in *.
      + exists (Ddistr []).
        split; [reflexivity|].
        constructor; apply Forall_nil.
      + rewrite Forall_forall in *.
        simpl in *.
        assert (forall x : data, In x dl -> data_type x τ₁)
          by (intros; apply (H3 x); right; assumption).
        specialize (IHdl H0); clear H0.
        elim IHdl; intros; clear IHdl.
        elim H0; clear H0; intros.
        unfold lift in H0.
        unfold var in *.
        assert (exists x1, lift_map
           (fun d1 : data =>
            olift checkLocal
              (dnnrc_base_eval brand_relation_brands cenv ((v, Dlocal d1) :: env) e2))
           dl = Some x1 /\ (Ddistr x1) = x).
        revert H0.
        elim (lift_map
                (fun d1 : data =>
                   olift checkLocal
                         (dnnrc_base_eval brand_relation_brands cenv ((v, Dlocal d1) :: env) e2)) dl); intros.
        inversion H0; simpl in *. subst; clear H0.
        exists a1; split; reflexivity.
        congruence.
        elim H2; clear H2; intros.
        elim H2; clear H2; intros.
        subst.
        inversion H1; subst.
        specialize (IHdnnrc_base_type2 ((v,Dlocal a0)::env)).
        assert (dbindings_type ((v, Dlocal a0) :: env) ((v, Tlocal τ₁) :: tenv)).
        unfold dbindings_type.
        apply Forall2_cons; try assumption.
        simpl; split; try reflexivity.
        constructor.
        apply (H3 a0); left; reflexivity.
        specialize (IHdnnrc_base_type2 H4); clear H4.
        elim IHdnnrc_base_type2; clear IHdnnrc_base_type2; intros.
        elim H4; clear H4; intros.
        rewrite H4; simpl.
        inversion H5; clear H5; subst.
        exists (Ddistr (d::x0)); split; try reflexivity.
        simpl.
        revert H0.
        elim (lift_map
       (fun d1 : data =>
        olift checkLocal
              (dnnrc_base_eval brand_relation_brands cenv ((v, Dlocal d1) :: env) e2)) dl); intros.
        inversion H0.
        subst.
        reflexivity.
        congruence.
        constructor.
        rewrite Forall_forall in *; simpl; intros.
        elim H5; clear H5; intros.
        subst; assumption.
        auto.
    - specialize (IHdnnrc_base_type1 env H); specialize (IHdnnrc_base_type2 env H); specialize (IHdnnrc_base_type3 env H).
      elim IHdnnrc_base_type1; intros; clear IHdnnrc_base_type1;
      elim IHdnnrc_base_type2; intros; clear IHdnnrc_base_type2;
      elim IHdnnrc_base_type3; intros; clear IHdnnrc_base_type3.
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
    - destruct (IHdnnrc_base_type1 _ H) as [dd [evald typd]].
      inversion typd; clear typd; subst.
      apply data_type_Either_inv in H2.
      rewrite evald.
      simpl.
      destruct H2 as [[ddl[? typd]]|[ddr[? typd]]]; subst.
      + destruct (IHdnnrc_base_type2 ((xl,Dlocal ddl)::env));
        unfold dbindings_type in *; auto.
        apply Forall2_cons; auto; split; [auto|constructor;auto].
        exists x; auto.
      + destruct (IHdnnrc_base_type3 ((xr,Dlocal ddr)::env));
        unfold dbindings_type in *; auto.
        apply Forall2_cons; auto; split; [auto|constructor;auto].
        exists x; auto.
    - elim (IHdnnrc_base_type env H); intros.
      elim H1; clear H1; intros.
      rewrite H1; simpl.
      inversion H2; clear H2; subst.
      exists (Dlocal (dcoll dl)).
      simpl. split; [reflexivity|].
      constructor.
      constructor.
      assumption.
    - elim (IHdnnrc_base_type env H); intros.
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
  Admitted.

End TDNNRCBase.

(* Global Arguments TAlgPlug {m} plug_type {plug} : clear implicits.  *)

