(*
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
Require Import DataSystem.
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
  

End tDNNRCSub.

