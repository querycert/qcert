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

Section NNRCtoDNNRC.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.

  Require Import Utils BasicRuntime.
  Require Import NNRC.
  Require Import DData DNNRC.

  Context {fruntime:foreign_runtime}.
  
  Fixpoint nrc_to_dnrc {A:Set} {plug_type:Set} (annot:A) (tenv:list (var*dlocalization)) (n:nrc) : dnrc A plug_type :=
    match n with
    | NRCVar v =>
      match lookup equiv_dec tenv v with
      | None => DNRCVar annot v (* urghh... *)
      | Some Vlocal => DNRCVar annot v
      | Some Vdistr => DNRCCollect annot (DNRCVar annot v)
      end
    | NRCConst d => DNRCConst annot d
    | NRCBinop b n1 n2 => DNRCBinop annot b (nrc_to_dnrc annot tenv n1) (nrc_to_dnrc annot tenv n2)
    | NRCUnop u n1 => DNRCUnop annot u (nrc_to_dnrc annot tenv n1)
    | NRCLet v n1 n2 => DNRCLet annot v (nrc_to_dnrc annot tenv n1) (nrc_to_dnrc annot ((v,Vlocal)::tenv) n2)
    | NRCFor v n1 n2 => DNRCFor annot v (nrc_to_dnrc annot tenv n1) (nrc_to_dnrc annot ((v,Vlocal)::tenv) n2)
    | NRCIf n1 n2 n3 => DNRCIf annot (nrc_to_dnrc annot tenv n1) (nrc_to_dnrc annot tenv n2) (nrc_to_dnrc annot tenv n3)
    | NRCEither n0 v1 n1 v2 n2 =>
      DNRCEither annot (nrc_to_dnrc annot tenv n0) v1 (nrc_to_dnrc annot ((v1,Vlocal)::tenv) n1) v2 (nrc_to_dnrc annot ((v2,Vlocal)::tenv) n2)
    end.

  Definition wf_localization (tl:option dlocalization) (dl:option ddata) :=
    match tl, dl with
    | Some Vlocal, Some (Dlocal _) => True
    | Some Vlocal, Some (Ddistr _) => False
    | Some Vdistr, Some (Ddistr _) => True
    | Some Vdistr, Some (Dlocal _) => False
    | _, _ => False
    end.
    
  Definition wf_denv (tenv:list (var*dlocalization)) (denv:list (var*ddata)) :=
    (domain tenv = domain denv) /\
    forall v, wf_localization (lookup equiv_dec tenv v) (lookup equiv_dec denv v).

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

  Definition localize_denv (denv:list (var*ddata)) :=
    map (fun x => (fst x, localize_data (snd x))) denv.

  Lemma localize_denv_cons v d (denv:list (var*ddata)) :
    localize_denv ((v,Dlocal d) :: denv) = (v,d) :: localize_denv denv.
  Proof.
    reflexivity.
  Qed.

  Lemma lookup_denv_local v d denv :
    lookup equiv_dec denv v = Some (Dlocal d) ->
    lift Dlocal (lookup equiv_dec (localize_denv denv) v) =
    lookup equiv_dec denv v.
  Proof.
    intros; induction denv; simpl in *; [reflexivity| ].
    destruct a; simpl in *.
    destruct (equiv_dec v v0); try congruence.
    - rewrite e in *; clear e.
      inversion H; subst; clear H.
      reflexivity.
    - apply (IHdenv H).
  Qed.

  Lemma lookup_denv_distr v l denv :
    lookup equiv_dec denv v = Some (Ddistr l) ->
    lift Dlocal (lookup equiv_dec (localize_denv denv) v) =
    lift Dlocal (olift checkDistrAndCollect (lookup equiv_dec denv v)).
  Proof.
    intros.
    induction denv; [reflexivity| ]; simpl in *.
    destruct a; simpl in *.
    destruct (equiv_dec v v0); simpl in *.
    - inversion H; subst; reflexivity.
    - apply IHdenv. apply H.
  Qed.

  Lemma rmap_nrc_to_dnrc_correct {A:Set} {plug_type:Set} {plug:AlgPlug plug_type} (h:brand_relation_t) (annot:A) tenv denv v l n2 :
    wf_denv tenv denv ->
    (forall (tenv : list (var * dlocalization))
            (denv : list (var * ddata)),
        wf_denv tenv denv ->
        lift Dlocal (nrc_eval h (localize_denv denv) n2) =
        dnrc_eval h denv (nrc_to_dnrc annot tenv n2)) ->
    rmap
      (fun d1 : data =>
         olift checkLocal
               (dnrc_eval h ((v, Dlocal d1) :: denv)
                          (nrc_to_dnrc annot ((v, Vlocal) :: tenv) n2))) l = rmap (fun d1 : data => nrc_eval h ((v, d1) :: localize_denv denv) n2) l.
  Proof.
    intros Hwf; intros.
    induction l; [reflexivity| ]; simpl.
    unfold olift.
    specialize (H ((v, Vlocal) :: tenv) ((v, Dlocal a) :: denv)).
    rewrite <- H; simpl.
    unfold lift.
    destruct (nrc_eval h ((v, a) :: localize_denv denv) n2); try reflexivity.
    simpl.
    rewrite <- IHl.
    reflexivity.
    apply wf_denv_cons.
    assumption.
  Qed.

  Global Arguments dnrc : clear implicits.
  Lemma nrc_to_dnrc_correct {A plug_type:Set} (annot:A) {plug:AlgPlug plug_type} h (tenv:list (var*dlocalization)) (n:nrc) :
    forall denv:list (var*ddata),
      wf_denv tenv denv ->
      lift Dlocal (nrc_eval h (localize_denv denv) n) = dnrc_eval h denv (nrc_to_dnrc annot tenv n).
  Proof.
    revert tenv; nrc_cases (induction n) Case; intros; simpl; intros.
    unfold wf_denv in H;
      elim H; intros; clear H.
    - Case "NRCVar"%string.
      case_eq (lookup equiv_dec tenv v); simpl; intros.
      + case_eq d; simpl; intros; specialize (H1 v).
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
      + specialize (H1 v). (* Because of well-formedness of env, the variable has to exists in both tenv and denv *)
        unfold wf_localization in H1.
        rewrite H in *.
        contradiction.
    - Case "NRCConst"%string.
      reflexivity.
    - Case "NRCBinop"%string.
      unfold lift in *.
      specialize (IHn1 tenv denv H).
      specialize (IHn2 tenv denv H).
      case_eq (nrc_eval h (localize_denv denv) n1);
        case_eq (nrc_eval h (localize_denv denv) n2); intros;
        rewrite H0 in *; rewrite H1 in *; simpl in *;
        rewrite <- IHn1; rewrite <- IHn2; simpl in *; reflexivity.
    - Case "NRCUnop"%string.
      specialize (IHn tenv denv H).
      case_eq (nrc_eval h (localize_denv denv) n); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn; simpl in *; reflexivity.
    - Case "NRCLet"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nrc_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      specialize (IHn2 ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv)).
      apply IHn2; apply wf_denv_cons; apply H.
    - Case "NRCFor"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nrc_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl in *; try reflexivity.
      unfold lift.
      rewrite rmap_nrc_to_dnrc_correct; try assumption.
      assert (@rmap (@data (@foreign_runtime_data fruntime))
         (@data (@foreign_runtime_data fruntime))
         (fun d1 : @data (@foreign_runtime_data fruntime) =>
          @nrc_eval fruntime h
            (@cons (prod var (@data (@foreign_runtime_data fruntime)))
               (@pair var (@data (@foreign_runtime_data fruntime)) v d1)
               (localize_denv denv)) n2) l = rmap
         (fun d1 : data => nrc_eval h ((v, d1) :: localize_denv denv) n2)
         l) by reflexivity.
      rewrite H1. clear H1.
      destruct (rmap
                  (fun d1 : data => nrc_eval h ((v, d1) :: localize_denv denv) n2)
                  l); reflexivity.
    - Case "NRCIf"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nrc_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl; try reflexivity.
      destruct b; simpl.
      + specialize (IHn2 tenv denv); apply IHn2; apply H.
      + specialize (IHn3 tenv denv); apply IHn3; apply H.
    - Case "NRCEither"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nrc_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl; try reflexivity.
      + specialize (IHn2 ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv)).
        rewrite <- localize_denv_cons.
        apply IHn2; apply wf_denv_cons; apply H.
      + specialize (IHn3 ((v0, Vlocal) :: tenv) ((v0, Dlocal d) :: denv)).
        rewrite <- localize_denv_cons.
        apply IHn3; apply wf_denv_cons; apply H.
  Qed.

  Require Import NRAEnvRuntime.
  Definition nrc_to_dnrc_algenv {A} := @nrc_to_dnrc A algenv.
  Require Import SparkIR.
  Context {ftype: ForeignType.foreign_type}.
  Definition nrc_to_dnrc_dataset {A} := @nrc_to_dnrc A dataset.

End NNRCtoDNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
