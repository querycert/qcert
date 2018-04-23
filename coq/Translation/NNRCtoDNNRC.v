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
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCSystem.
Require Import DNNRCSystem.
Require Import NRAEnvRuntime.
Require Import Dataframe.

Section NNRCtoDNNRC.
  Context {fruntime:foreign_runtime}.
  
  Fixpoint nnrc_to_dnnrc_base {A:Set} {plug_type:Set} (annot:A) (ctenv tenv:list (var*dlocalization)) (n:nnrc) : @dnnrc_base _ A plug_type :=
    match n with
    | NNRCGetConstant v =>
      match assoc_lookupr equiv_dec ctenv v with
      | None => DNNRCGetConstant annot v (* urghh... *)
      | Some Vlocal => DNNRCGetConstant annot v
      | Some Vdistr => DNNRCCollect annot (DNNRCGetConstant annot v)
      end
    | NNRCVar v =>
      match lookup equiv_dec tenv v with
      | None => DNNRCVar annot v (* urghh... *)
      | Some Vlocal => DNNRCVar annot v
      | Some Vdistr => DNNRCCollect annot (DNNRCVar annot v)
      end
    | NNRCConst d => DNNRCConst annot d
    | NNRCBinop b n1 n2 => DNNRCBinop annot b (nnrc_to_dnnrc_base annot ctenv tenv n1) (nnrc_to_dnnrc_base annot ctenv tenv n2)
    | NNRCUnop u n1 => DNNRCUnop annot u (nnrc_to_dnnrc_base annot ctenv tenv n1)
    | NNRCLet v n1 n2 => DNNRCLet annot v (nnrc_to_dnnrc_base annot ctenv tenv n1) (nnrc_to_dnnrc_base annot ctenv ((v,Vlocal)::tenv) n2)
    | NNRCFor v n1 n2 => DNNRCFor annot v (nnrc_to_dnnrc_base annot ctenv tenv n1) (nnrc_to_dnnrc_base annot ctenv ((v,Vlocal)::tenv) n2)
    | NNRCIf n1 n2 n3 => DNNRCIf annot (nnrc_to_dnnrc_base annot ctenv tenv n1) (nnrc_to_dnnrc_base annot ctenv tenv n2) (nnrc_to_dnnrc_base annot ctenv tenv n3)
    | NNRCEither n0 v1 n1 v2 n2 =>
      DNNRCEither annot (nnrc_to_dnnrc_base annot ctenv tenv n0) v1 (nnrc_to_dnnrc_base annot ctenv ((v1,Vlocal)::tenv) n1) v2 (nnrc_to_dnnrc_base annot ctenv ((v2,Vlocal)::tenv) n2)
    | NNRCGroupBy g sl n1 =>
      DNNRCGroupBy annot g sl (nnrc_to_dnnrc_base annot ctenv tenv n1)
    end.

  Definition wf_localization (tl:option dlocalization) (dl:option ddata) :=
    match tl, dl with
    | None, None => True
    | Some Vlocal, Some (Dlocal _) => True
    | Some Vlocal, Some (Ddistr _) => False
    | Some Vdistr, Some (Ddistr _) => True
    | Some Vdistr, Some (Dlocal _) => False
    | _, _ => False
    end.
    
  Definition wf_denv (tenv:list (var*dlocalization)) (denv:list (var*ddata)) :=
    (domain tenv = domain denv) /\
    forall v, wf_localization (lookup equiv_dec tenv v) (lookup equiv_dec denv v).

  Definition wf_cdenv (tenv:list (var*dlocalization)) (denv:list (var*ddata)) :=
    (domain tenv = domain denv) /\
    forall v, wf_localization (assoc_lookupr equiv_dec tenv v) (assoc_lookupr equiv_dec denv v).

  Lemma wf_denv_cons v d tenv denv :
    wf_denv tenv denv -> wf_denv ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv).
  Proof.
    intros.
    unfold wf_denv in *; simpl.
    elim H; intros; clear H.
    split; [rewrite H0; reflexivity| ]; intros.
    destruct (equiv_dec v0 v).
    - reflexivity.
    - apply H1; assumption.
  Qed.

  Lemma domain_lookup_none {A B} (l1:list (string*A)) (l2:list (string*B)) (v:string) :
    domain l1 = domain l2 ->
    assoc_lookupr equiv_dec l1 v = None ->
    assoc_lookupr equiv_dec l2 v = None.
  Proof.
    intros.
    revert l2 H.
    induction l1; simpl in *; intros.
    - destruct l2; try congruence. reflexivity.
      destruct p; simpl in *.
      congruence.
    - destruct a; simpl in *.
      destruct l2; simpl in *.
      reflexivity.
      destruct p; simpl in *.
      inversion H; clear H; intros.
      subst.
      destruct (equiv_dec v s0).
      + destruct (assoc_lookupr equiv_dec l1 v); congruence.
      + destruct (assoc_lookupr equiv_dec l1 v); try congruence.
        specialize (IHl1 eq_refl l2 H3).
        rewrite IHl1; reflexivity.
  Qed.

  Lemma domain_lookup_some {A B} (l1:list (string*A)) (l2:list (string*B)) (v:string) :
    domain l1 = domain l2 ->
    (exists x, assoc_lookupr equiv_dec l1 v = Some x) ->
    (exists x', assoc_lookupr equiv_dec l2 v = Some x').
  Proof.
    intros.
    revert l2 H.
    induction l1; simpl in *; intros.
    - destruct l2; try congruence.
      elim H0; intros; congruence.
      destruct p; simpl in *.
      congruence.
    - destruct a; simpl in *.
      destruct (equiv_dec v s); simpl in *.
      rewrite e in *; clear e; simpl in *.
      destruct l2; simpl in *.
      congruence.
      destruct p; simpl in *.
      inversion H; clear H; intros; subst.
      destruct (equiv_dec s0 s0); try congruence.
      + destruct (assoc_lookupr equiv_dec l2 s0).
        exists b0; reflexivity.
        exists b; reflexivity.
      + destruct l2; simpl in *.
        congruence.
        destruct p; simpl in *.
        inversion H; clear H; intros; subst.
        elim H0; clear H0; intros.
        destruct (assoc_lookupr equiv_dec l1 v); simpl in *.
        inversion H; clear H; intros; subst.
        assert (exists x0:A, Some x = Some x0) by (exists x; reflexivity).
        elim (IHl1 H l2 H3); clear IHl1; intros.
        rewrite H0; simpl.
        exists x0; reflexivity.
        congruence.
  Qed.

  Lemma wf_cdenv_cons v d tenv denv :
    wf_cdenv tenv denv -> wf_cdenv ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv).
  Proof.
    intros.
    unfold wf_cdenv, var in *; simpl in *.
    elim H; intros; clear H.
    split; [rewrite H0; reflexivity| ]; intros.
    destruct (equiv_dec v0 v).
    rewrite e in *; clear e.
    - case_eq (assoc_lookupr equiv_dec tenv v); intros; simpl. 
      assert (exists x : dlocalization, assoc_lookupr equiv_dec tenv v = Some x)
       by (exists d0; auto).
      generalize (domain_lookup_some tenv denv v H0 H2); clear H2; intros.
      elim H2; clear H2; intros.
      rewrite H2.
      destruct d0.
      specialize (H1 v).
      unfold wf_localization in H1.
      rewrite H in H1. rewrite H2 in H1.
      auto.
      specialize (H1 v).
      unfold wf_localization in H1.
      rewrite H in H1. rewrite H2 in H1.
      auto.
      generalize (domain_lookup_none tenv denv v H0 H); intros.
      specialize (H1 v).
      unfold wf_localization in H1.
      rewrite H in H1.
      destruct (assoc_lookupr equiv_dec denv v); try congruence.
    - specialize (H1 v0).
      unfold wf_localization in *.
      case_eq (assoc_lookupr equiv_dec tenv v0); intros;
      rewrite H in *;
      case_eq (assoc_lookupr equiv_dec denv v0); intros.
      rewrite H2 in *.
      assumption.
      rewrite H2 in *.
      assumption.
      rewrite H2 in H1.
      contradiction.
      trivial.
  Qed.

  Lemma lookup_denv_local v d denv :
    lookup equiv_dec denv v = Some (Dlocal d) ->
    lift Dlocal (lookup equiv_dec (unlocalize_constants denv) v) =
    lookup equiv_dec denv v.
  Proof.
    intros; induction denv; simpl in *; [reflexivity| ].
    destruct a; simpl in *.
    destruct (equiv_dec v s); try congruence.
    - rewrite e in *; clear e.
      inversion H; subst; clear H.
      reflexivity.
    - apply (IHdenv H).
  Qed.

  Lemma rev_localize_comm denv :
    rev (unlocalize_constants denv) = unlocalize_constants (rev denv).
  Proof.
    unfold unlocalize_constants.
    rewrite map_rev.
    reflexivity.
  Qed.

  Lemma lookupr_denv_local v d denv :
    assoc_lookupr equiv_dec denv v = Some (Dlocal d) ->
    lift Dlocal (assoc_lookupr equiv_dec (unlocalize_constants denv) v) =
    assoc_lookupr equiv_dec denv v.
  Proof.
    intros.
    rewrite (@assoc_lookupr_lookup string _ equiv_dec).
    rewrite (@assoc_lookupr_lookup string _ equiv_dec).
    rewrite (@assoc_lookupr_lookup string _ equiv_dec) in H.
    rewrite rev_localize_comm.
    rewrite (lookup_denv_local v d); [reflexivity|assumption].
  Qed.

  Lemma lookup_denv_distr v l denv :
    lookup equiv_dec denv v = Some (Ddistr l) ->
    lift Dlocal (lookup equiv_dec (unlocalize_constants denv) v) =
    lift Dlocal (olift checkDistrAndCollect (lookup equiv_dec denv v)).
  Proof.
    intros.
    induction denv; [reflexivity| ]; simpl in *.
    destruct a; simpl in *.
    destruct (equiv_dec v s); simpl in *.
    - inversion H; subst; reflexivity.
    - apply IHdenv. apply H.
  Qed.

  Lemma lift_map_nnrc_to_dnnrc_base_correct {A:Set} {plug_type:Set} {plug:AlgPlug plug_type} (h:brand_relation_t) (annot:A) ctenv tenv cdenv denv v l n2 :
    wf_denv tenv denv ->
    (forall (tenv : list (var * dlocalization))
            (denv : list (var * ddata)),
        wf_denv tenv denv ->
        lift Dlocal (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n2) =
        dnnrc_base_eval h cdenv denv (nnrc_to_dnnrc_base annot ctenv tenv n2)) ->
    lift_map
      (fun d1 : data =>
         olift checkLocal
               (dnnrc_base_eval h cdenv ((v, Dlocal d1) :: denv)
                          (nnrc_to_dnnrc_base annot ctenv ((v, Vlocal) :: tenv) n2))) l = lift_map (fun d1 : data => nnrc_core_eval h (unlocalize_constants cdenv) ((v, d1) :: unlocalize_constants denv) n2) l.
  Proof.
    intros Hwf; intros.
    induction l; [reflexivity| ]; simpl.
    unfold olift.
    specialize (H ((v, Vlocal) :: tenv) ((v, Dlocal a) :: denv)).
    rewrite <- H; simpl.
    unfold lift.
    assert (@nnrc_core_eval fruntime h (@unlocalize_constants (@foreign_runtime_data fruntime) cdenv)
        (@cons (prod var (@data (@foreign_runtime_data fruntime)))
           (@pair var (@data (@foreign_runtime_data fruntime)) v a)
           (@unlocalize_constants (@foreign_runtime_data fruntime) denv)) n2 =
            @nnrc_core_eval fruntime h (@unlocalize_constants (@foreign_runtime_data fruntime) cdenv)
            (@cons (prod string (@data (@foreign_runtime_data fruntime)))
               (@pair string (@data (@foreign_runtime_data fruntime)) v a)
               (@unlocalize_constants (@foreign_runtime_data fruntime) denv)) n2).
    reflexivity.
    rewrite H0; clear H0.
    destruct (@nnrc_core_eval fruntime h (@unlocalize_constants (@foreign_runtime_data fruntime) cdenv)
            (@cons (prod string (@data (@foreign_runtime_data fruntime)))
               (@pair string (@data (@foreign_runtime_data fruntime)) v a)
               (@unlocalize_constants (@foreign_runtime_data fruntime) denv)) n2); try reflexivity.
    rewrite <- IHl.
    reflexivity.
    apply wf_denv_cons.
    assumption.
  Qed.

  Lemma assoc_lookupr_map_snd_comm {A B} (l:list (string*A)) (f:A->B) (v:string) :
    assoc_lookupr equiv_dec (map (fun x: string * A => (fst x, f (snd x))) l) v =
    lift f (assoc_lookupr equiv_dec l v).
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl.
      rewrite IHl.
      destruct a; simpl in *.
      destruct (assoc_lookupr equiv_dec l v); simpl.
      reflexivity.
      destruct (equiv_dec v s); reflexivity.
  Qed.

  Lemma lookup_map_snd_comm {A B} (l:list (string*A)) (f:A->B) (v:string) :
    lookup equiv_dec (map (fun x: string * A => (fst x, f (snd x))) l) v =
    lift f (lookup equiv_dec l v).
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl.
      destruct a; simpl in *.
      destruct (equiv_dec v s); simpl in *.
      rewrite e in *; clear e; simpl in *.
      reflexivity.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma nnrc_to_dnnrc_base_get_constant_correct
        h
        (A plug_type:Set) (plug:AlgPlug plug_type) (annot:A) (v : var)
        (ctenv : list (var * dlocalization))
        (cdenv denv : list (var * ddata))
        (Hcdenv : wf_cdenv ctenv cdenv) :
    lift Dlocal (edot (unlocalize_constants cdenv) v) =
    dnnrc_base_eval h cdenv denv
               match assoc_lookupr equiv_dec ctenv v with
               | Some Vlocal => DNNRCGetConstant annot v
               | Some Vdistr => DNNRCCollect annot (DNNRCGetConstant annot v)
               | None => DNNRCGetConstant annot v
               end.
  Proof.
    unfold wf_cdenv in *; simpl in *.
    unfold edot; simpl in *.
    elim Hcdenv; clear Hcdenv; intros.
    specialize (H0 v).
    unfold wf_localization in H0.
    unfold unlocalize_constants.
    rewrite assoc_lookupr_map_snd_comm.
    unfold lift in *.
    unfold equiv_dec in *; simpl in *.
    assert (@assoc_lookupr var (@ddata (@foreign_runtime_data fruntime))
                           (@equiv var (@eq var) (@eq_equivalence var))
                           (@complement var (@equiv var (@eq var) (@eq_equivalence var))) string_eqdec
                           cdenv v
            = @assoc_lookupr string (@ddata (@foreign_runtime_data fruntime))
                             (@equiv string (@eq string) (@eq_equivalence string))
                             (@complement string (@equiv string (@eq string) (@eq_equivalence string)))
                             string_eqdec cdenv v) by reflexivity.
    rewrite H1 in H0; clear H1.
    destruct (@assoc_lookupr var dlocalization (@equiv var (@eq var) (@eq_equivalence var))
                             (@complement var (@equiv var (@eq var) (@eq_equivalence var))) string_eqdec ctenv v); simpl.
    - destruct d; simpl in *.
      + unfold edot; simpl in *.
        destruct (assoc_lookupr string_eqdec cdenv v).
        destruct d; simpl in *; [reflexivity|contradiction].
        contradiction.
      + unfold edot; simpl in *.
        destruct (assoc_lookupr string_eqdec cdenv v).
        destruct d; simpl; [contradiction|reflexivity].
        contradiction.
    - unfold edot; simpl.
      case_eq (assoc_lookupr string_eqdec cdenv v); intros.
      rewrite H1 in H0; simpl in H0.
      contradiction.
      reflexivity.
  Qed.
    
  Global Arguments dnnrc_base : clear implicits.
  Lemma nnrc_to_dnnrc_base_correct {A plug_type:Set} (annot:A) {plug:AlgPlug plug_type} h (ctenv tenv:list (var*dlocalization)) (n:nnrc) :
    forall cdenv denv:list (var*ddata),
      wf_cdenv ctenv cdenv ->
      wf_denv tenv denv ->
      lift Dlocal (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n)
      = dnnrc_base_eval h cdenv denv (nnrc_to_dnnrc_base annot ctenv tenv n).
  Proof.
    intros cdenv ? Hcdenv ?.
    revert tenv denv H; nnrc_cases (induction n) Case; intros; simpl; intros.
    - Case "NNRCGetConstant"%string.
      rewrite (nnrc_to_dnnrc_base_get_constant_correct h A plug_type plug annot v ctenv cdenv denv).
      reflexivity.
      assumption.
    - Case "NNRCVar"%string.
      unfold wf_denv in *; elim H; intros; clear H.
      specialize (H1 v).
      case_eq (lookup equiv_dec tenv v); simpl; intros.
      + case_eq d; simpl; intros.
        * unfold wf_localization in H1. subst.
          rewrite H in *.
          case_eq (lookup equiv_dec denv v); intros;
          rewrite H2 in H1. destruct d; try contradiction.
          apply (lookup_denv_local v d denv H2).
          contradiction.
        * unfold wf_localization in H1. subst.
          rewrite H in *.
          case_eq (lookup equiv_dec denv v); intros;
          rewrite H2 in H1. destruct d; try contradiction.
          apply (lookup_denv_distr v l denv H2).
          contradiction.
      + (* Because of well-formedness of env, the variable has to exists in both tenv and denv *)
        unfold wf_localization in H1.
        rewrite H in *.
        case_eq (lookup equiv_dec denv v); simpl; intros.
        rewrite H2 in H1; contradiction.
        unfold unlocalize_constants.
        rewrite lookup_map_snd_comm.
        assert ((@lookup var (@ddata (@foreign_runtime_data fruntime))
                         (@equiv_dec var (@eq var) (@eq_equivalence var) string_eqdec) denv v)
               = (@lookup string (@ddata (@foreign_runtime_data fruntime))
                          (@equiv_dec string (@eq string) (@eq_equivalence string) string_eqdec) denv v))
          by reflexivity.
        rewrite H3 in H2.
        rewrite H2.
        reflexivity.
    - Case "NNRCConst"%string.
      reflexivity.
    - Case "NNRCBinop"%string.
      unfold lift in *.
      specialize (IHn1 tenv denv H).
      specialize (IHn2 tenv denv H).
      case_eq (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n1);
        case_eq (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n2); intros;
        rewrite H0 in *; rewrite H1 in *; simpl in *;
        rewrite <- IHn1; rewrite <- IHn2; simpl in *; reflexivity.
    - Case "NNRCUnop"%string.
      specialize (IHn tenv denv H).
      case_eq (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn; simpl in *; reflexivity.
    - Case "NNRCLet"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      specialize (IHn2 ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv)).
      apply IHn2; apply wf_denv_cons; apply H.
    - Case "NNRCFor"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl in *; try reflexivity.
      unfold lift.
      rewrite lift_map_nnrc_to_dnnrc_base_correct; try assumption.
      assert (@lift_map (@data (@foreign_runtime_data fruntime)) (@data (@foreign_runtime_data fruntime))
          (fun d1 : @data (@foreign_runtime_data fruntime) =>
           @nnrc_core_eval fruntime h (@unlocalize_constants (@foreign_runtime_data fruntime) cdenv)
             (@cons (prod Var.var (@data (@foreign_runtime_data fruntime)))
                (@pair Var.var (@data (@foreign_runtime_data fruntime)) v d1)
                (@unlocalize_constants (@foreign_runtime_data fruntime) denv)) n2) l = @lift_map (@data (@foreign_runtime_data fruntime)) (@data (@foreign_runtime_data fruntime))
        (fun d1 : @data (@foreign_runtime_data fruntime) =>
         @nnrc_core_eval fruntime h (@unlocalize_constants (@foreign_runtime_data fruntime) cdenv)
           (@cons (prod var (@data (@foreign_runtime_data fruntime)))
              (@pair var (@data (@foreign_runtime_data fruntime)) v d1)
              (@unlocalize_constants (@foreign_runtime_data fruntime) denv)) n2) l) by reflexivity.
      rewrite <- H1. clear H1.
      destruct (lift_map
                  (fun d1 : data => nnrc_core_eval h (unlocalize_constants cdenv)
                  ((v, d1) :: unlocalize_constants denv) n2)
                  l); try reflexivity.
    - Case "NNRCIf"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl; try reflexivity.
      destruct b; simpl.
      + specialize (IHn2 tenv denv); apply IHn2; apply H.
      + specialize (IHn3 tenv denv); apply IHn3; apply H.
    - Case "NNRCEither"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl; try reflexivity.
      + specialize (IHn2 ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv)).
        rewrite <- unlocalize_constants_cons.
        apply IHn2; apply wf_denv_cons; apply H.
      + specialize (IHn3 ((v0, Vlocal) :: tenv) ((v0, Dlocal d) :: denv)).
        rewrite <- unlocalize_constants_cons.
        apply IHn3; apply wf_denv_cons; apply H.
    - Case "NNRCGroupBy"%string.
      reflexivity. (* XXX TODO: Currently both fail in core NNRC and in DNNRC XXX *)
  Qed.

  Lemma nnrc_to_dnnrc_base_correct_lift {A plug_type:Set} (annot:A) {plug:AlgPlug plug_type} h (ctenv tenv:list (var*dlocalization)) (n:nnrc) :
    forall cdenv denv:list (var*ddata),
      wf_cdenv ctenv cdenv ->
      wf_denv tenv denv ->
      nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n
      = lift unlocalize_data (dnnrc_base_eval h cdenv denv (nnrc_to_dnnrc_base annot ctenv tenv n)).
  Proof.
    intros.
    rewrite <- nnrc_to_dnnrc_base_correct; auto.
    unfold unlocalize_data.
    unfold lift; simpl.
    destruct (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv)); auto.
  Qed.

  Section Top.
    Context {ftype: ForeignType.foreign_type}.

    Definition nnrc_to_dnnrc {A:Set} (annot:A) (tenv:vdbindings) (q:nnrc) :=
      @nnrc_to_dnnrc_base A dataframe annot (rec_sort tenv) nil
                     (nnrc_to_nnrc_base q).

    Definition nnrc_to_dnnrc_top (tenv:vdbindings) (q:nnrc) : dnnrc :=
      nnrc_to_dnnrc tt tenv q.

    Lemma rec_sort_unlocalize_constants_comm l :
      (rec_sort (unlocalize_constants l) = (unlocalize_constants (rec_sort l))).
    Proof.
      unfold unlocalize_constants.
      rewrite map_rec_sort.
      reflexivity.
      intros.
      split.
      destruct x; simpl in *.
      auto.
      simpl.
      auto.
    Qed.

    Lemma wf_cdenv_rec_sort tenv cdenv :
      wf_cdenv tenv cdenv -> wf_cdenv (rec_sort tenv) (rec_sort cdenv).
    Proof.
      intros.
      unfold wf_cdenv in *.
      elim H; clear H; intros.
      split.
      - apply same_domain_rec_sort; assumption.
      - intros.
        specialize (H0 v).
        assert (assoc_lookupr ODT_eqdec (rec_sort tenv) v =
                assoc_lookupr equiv_dec (rec_sort tenv) v) by reflexivity.
        rewrite <- H1; clear H1.
        rewrite assoc_lookupr_drec_sort.
        assert (assoc_lookupr ODT_eqdec (rec_sort cdenv) v =
                assoc_lookupr equiv_dec (rec_sort cdenv) v) by reflexivity.
        rewrite <- H1; clear H1.
        rewrite assoc_lookupr_drec_sort.
        assumption.
    Qed.

    Theorem nnrc_to_dnnrc_top_correct h (tenv:vdbindings) (q:nnrc) :
      forall cdenv:dbindings,
        wf_cdenv tenv cdenv ->
        nnrc_eval_top h q (unlocalize_constants cdenv) =
        dnnrc_eval_top h (nnrc_to_dnnrc_top tenv q) cdenv.
    Proof.
      unfold nnrc_to_dnnrc_top.
      unfold nnrc_eval_top.
      unfold nnrc_eval.
      unfold nnrc_to_dnnrc.
      unfold dnnrc_eval_top.
      intros.
      unfold lift_nnrc_core.
      assert (nil = unlocalize_constants nil) by reflexivity.
      rewrite H0.
      rewrite rec_sort_unlocalize_constants_comm.
      generalize (wf_cdenv_rec_sort tenv cdenv H); intros; clear H.
      apply (nnrc_to_dnnrc_base_correct_lift tt).
      assumption.
      unfold wf_denv.
      split; [reflexivity| ].
      intros.
      unfold wf_localization.
      simpl.
      trivial.
    Qed.
  End Top.
  
End NNRCtoDNNRC.

