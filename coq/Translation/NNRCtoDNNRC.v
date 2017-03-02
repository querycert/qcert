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
  Require Import NNRCSystem.
  Require Import DData DNNRC.

  Context {fruntime:foreign_runtime}.
  
  Fixpoint nnrc_to_dnnrc {A:Set} {plug_type:Set} (annot:A) (tenv:list (var*dlocalization)) (n:nnrc) : @dnnrc _ A plug_type :=
    match n with
    | NNRCVar v =>
      match lookup equiv_dec tenv v with
      | None => DNNRCVar annot v (* urghh... *)
      | Some Vlocal => DNNRCVar annot v
      | Some Vdistr => DNNRCCollect annot (DNNRCVar annot v)
      end
    | NNRCConst d => DNNRCConst annot d
    | NNRCBinop b n1 n2 => DNNRCBinop annot b (nnrc_to_dnnrc annot tenv n1) (nnrc_to_dnnrc annot tenv n2)
    | NNRCUnop u n1 => DNNRCUnop annot u (nnrc_to_dnnrc annot tenv n1)
    | NNRCLet v n1 n2 => DNNRCLet annot v (nnrc_to_dnnrc annot tenv n1) (nnrc_to_dnnrc annot ((v,Vlocal)::tenv) n2)
    | NNRCFor v n1 n2 => DNNRCFor annot v (nnrc_to_dnnrc annot tenv n1) (nnrc_to_dnnrc annot ((v,Vlocal)::tenv) n2)
    | NNRCIf n1 n2 n3 => DNNRCIf annot (nnrc_to_dnnrc annot tenv n1) (nnrc_to_dnnrc annot tenv n2) (nnrc_to_dnnrc annot tenv n3)
    | NNRCEither n0 v1 n1 v2 n2 =>
      DNNRCEither annot (nnrc_to_dnnrc annot tenv n0) v1 (nnrc_to_dnnrc annot ((v1,Vlocal)::tenv) n1) v2 (nnrc_to_dnnrc annot ((v2,Vlocal)::tenv) n2)
    | NNRCGroupBy g sl n1 =>
      DNNRCGroupBy annot g sl (nnrc_to_dnnrc annot tenv n1)
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

  Lemma lookup_denv_local v d denv :
    lookup equiv_dec denv v = Some (Dlocal d) ->
    lift Dlocal (lookup equiv_dec (localize_denv denv) v) =
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

  Lemma lookup_denv_distr v l denv :
    lookup equiv_dec denv v = Some (Ddistr l) ->
    lift Dlocal (lookup equiv_dec (localize_denv denv) v) =
    lift Dlocal (olift checkDistrAndCollect (lookup equiv_dec denv v)).
  Proof.
    intros.
    induction denv; [reflexivity| ]; simpl in *.
    destruct a; simpl in *.
    destruct (equiv_dec v s); simpl in *.
    - inversion H; subst; reflexivity.
    - apply IHdenv. apply H.
  Qed.

  Lemma rmap_nnrc_to_dnnrc_correct {A:Set} {plug_type:Set} {plug:AlgPlug plug_type} (h:brand_relation_t) (annot:A) tenv denv v l n2 :
    wf_denv tenv denv ->
    (forall (tenv : list (var * dlocalization))
            (denv : list (var * ddata)),
        wf_denv tenv denv ->
        lift Dlocal (nnrc_core_eval h (localize_denv denv) n2) =
        dnnrc_eval h denv (nnrc_to_dnnrc annot tenv n2)) ->
    rmap
      (fun d1 : data =>
         olift checkLocal
               (dnnrc_eval h ((v, Dlocal d1) :: denv)
                          (nnrc_to_dnnrc annot ((v, Vlocal) :: tenv) n2))) l = rmap (fun d1 : data => nnrc_core_eval h ((v, d1) :: localize_denv denv) n2) l.
  Proof.
    intros Hwf; intros.
    induction l; [reflexivity| ]; simpl.
    unfold olift.
    specialize (H ((v, Vlocal) :: tenv) ((v, Dlocal a) :: denv)).
    rewrite <- H; simpl.
    unfold lift.
    assert (@nnrc_core_eval fruntime h
        (@cons (prod var (@data (@foreign_runtime_data fruntime)))
           (@pair var (@data (@foreign_runtime_data fruntime)) v a)
           (@localize_denv (@foreign_runtime_data fruntime) denv)) n2 =
            @nnrc_core_eval fruntime h
            (@cons (prod string (@data (@foreign_runtime_data fruntime)))
               (@pair string (@data (@foreign_runtime_data fruntime)) v a)
               (@localize_denv (@foreign_runtime_data fruntime) denv)) n2).
    reflexivity.
    rewrite <- H0; clear H0.
    destruct (nnrc_core_eval h ((v, a) :: localize_denv denv) n2); try reflexivity.
    simpl.
    rewrite <- IHl.
    reflexivity.
    apply wf_denv_cons.
    assumption.
  Qed.

  Global Arguments dnnrc : clear implicits.
  Lemma nnrc_to_dnnrc_correct {A plug_type:Set} (annot:A) {plug:AlgPlug plug_type} h (tenv:list (var*dlocalization)) (n:nnrc) :
    forall denv:list (var*ddata),
      wf_denv tenv denv ->
      lift Dlocal (nnrc_core_eval h (localize_denv denv) n) = dnnrc_eval h denv (nnrc_to_dnnrc annot tenv n).
  Proof.
    revert tenv; nnrc_cases (induction n) Case; intros; simpl; intros.
    unfold wf_denv in H;
      elim H; intros; clear H.
    - Case "NNRCVar"%string.
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
    - Case "NNRCConst"%string.
      reflexivity.
    - Case "NNRCBinop"%string.
      unfold lift in *.
      specialize (IHn1 tenv denv H).
      specialize (IHn2 tenv denv H).
      case_eq (nnrc_core_eval h (localize_denv denv) n1);
        case_eq (nnrc_core_eval h (localize_denv denv) n2); intros;
        rewrite H0 in *; rewrite H1 in *; simpl in *;
        rewrite <- IHn1; rewrite <- IHn2; simpl in *; reflexivity.
    - Case "NNRCUnop"%string.
      specialize (IHn tenv denv H).
      case_eq (nnrc_core_eval h (localize_denv denv) n); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn; simpl in *; reflexivity.
    - Case "NNRCLet"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      specialize (IHn2 ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv)).
      apply IHn2; apply wf_denv_cons; apply H.
    - Case "NNRCFor"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl in *; try reflexivity.
      unfold lift.
      rewrite rmap_nnrc_to_dnnrc_correct; try assumption.
      assert (@rmap (@data (@foreign_runtime_data fruntime))
         (@data (@foreign_runtime_data fruntime))
         (fun d1 : @data (@foreign_runtime_data fruntime) =>
          @nnrc_core_eval fruntime h
            (@cons (prod var (@data (@foreign_runtime_data fruntime)))
               (@pair var (@data (@foreign_runtime_data fruntime)) v d1)
               (localize_denv denv)) n2) l = rmap
         (fun d1 : data => nnrc_core_eval h ((v, d1) :: localize_denv denv) n2)
         l) by reflexivity.
      rewrite H1. clear H1.
      destruct (rmap
                  (fun d1 : data => nnrc_core_eval h ((v, d1) :: localize_denv denv) n2)
                  l); reflexivity.
    - Case "NNRCIf"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl; try reflexivity.
      destruct b; simpl.
      + specialize (IHn2 tenv denv); apply IHn2; apply H.
      + specialize (IHn3 tenv denv); apply IHn3; apply H.
    - Case "NNRCEither"%string.
      specialize (IHn1 tenv denv H).
      case_eq (nnrc_core_eval h (localize_denv denv) n1); intros;
      rewrite H0 in *; simpl in *;
      rewrite <- IHn1; simpl in *; try reflexivity.
      destruct d; simpl; try reflexivity.
      + specialize (IHn2 ((v, Vlocal) :: tenv) ((v, Dlocal d) :: denv)).
        rewrite <- localize_denv_cons.
        apply IHn2; apply wf_denv_cons; apply H.
      + specialize (IHn3 ((v0, Vlocal) :: tenv) ((v0, Dlocal d) :: denv)).
        rewrite <- localize_denv_cons.
        apply IHn3; apply wf_denv_cons; apply H.
    - Case "NNRCGroupBy"%string.
      reflexivity. (* XXX TODO: Currently both fail in core NNRC and in DNNRC XXX *)
  Qed.

  Require Import NRAEnvRuntime.
  Require Import Dataset.
  Context {ftype: ForeignType.foreign_type}.
  Definition nnrc_to_dnnrc_dataset {A:Set} (annot:A) (tenv:list (var*dlocalization)) (n:nnrc) := @nnrc_to_dnnrc A dataset annot (mkConstants tenv) n.

End NNRCtoDNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
