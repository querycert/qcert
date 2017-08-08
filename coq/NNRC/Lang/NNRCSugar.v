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

(** This module contains some additional properties for extended operators in NNRC. Some of those are notably useful later on for proving translations from NRAEnv. *)

Section NNRCSugar.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import Arith.
  Require Import Max.
  Require Import Bool.
  Require Import Peano_dec.
  Require Import EquivDec.
  Require Import Decidable.
  Require Import Utils.
  Require Import BasicRuntime.
  Require Import cNNRC.
  Require Import NNRC.

  Context {fruntime:foreign_runtime}.
  Context {h:brand_relation_t}.

  (** * Group By *)

  (** This is an alternative macro for group by. This is used as a scafolding to prove translation from the GroupBy in NRAEnv to the one in NNRC correct. *)
  
  Definition nnrc_group_by_from_nraenv (vid venv:var) (g:string) (sl:list string) (e:nnrc) :=
    (NNRCLet (fresh_var "tappe$" (vid :: venv :: nil))
             (NNRCUnop (ARec "$pregroup") e)
             (NNRCFor
                (fresh_var "tmap$"
                           (vid :: fresh_var "tappe$" (vid :: venv :: nil) :: nil))
                (NNRCUnop ADistinct
                          (NNRCFor
                             (fresh_var "tmap$"
                                        (vid :: fresh_var "tappe$" (vid :: venv :: nil) :: nil))
                             (NNRCUnop (ADot "$pregroup")
                                       (NNRCVar (fresh_var "tappe$" (vid :: venv :: nil))))
                             (NNRCUnop (ARecProject sl)
                                       (NNRCVar
                                          (fresh_var "tmap$"
                                                     (vid
                                                        :: fresh_var "tappe$" (vid :: venv :: nil)
                                                        :: nil))))))
                (NNRCBinop AConcat
                           (NNRCUnop (ARec g)
                                     (NNRCLet
                                        (fresh_var "tappe$"
                                                   (fresh_var "tmap$"
                                                              (vid
                                                                 :: fresh_var "tappe$" (vid :: venv :: nil)
                                                                 :: nil)
                                                              :: fresh_var "tappe$" (vid :: venv :: nil) :: nil))
                                        (NNRCBinop AConcat
                                                   (NNRCUnop (ARec "$key")
                                                             (NNRCVar
                                                                (fresh_var "tmap$"
                                                                           (vid
                                                                              :: fresh_var "tappe$" (vid :: venv :: nil)
                                                                              :: nil))))
                                                   (NNRCVar (fresh_var "tappe$" (vid :: venv :: nil))))
                                        (NNRCUnop AFlatten
                                                  (NNRCFor
                                                     (fresh_var "tsel$"
                                                                (fresh_var "tmap$"
                                                                           (vid
                                                                              :: fresh_var "tappe$" (vid :: venv :: nil)
                                                                              :: nil)
                                                                           :: fresh_var "tappe$"
                                                                           (fresh_var "tmap$"
                                                                                      (vid
                                                                                         :: fresh_var "tappe$"
                                                                                         (vid :: venv :: nil) :: nil)
                                                                                      :: fresh_var "tappe$"
                                                                                      (vid :: venv :: nil) :: nil)
                                                                           :: nil))
                                                     (NNRCUnop (ADot "$pregroup")
                                                               (NNRCVar
                                                                  (fresh_var "tappe$"
                                                                             (fresh_var "tmap$"
                                                                                        (vid
                                                                                           :: fresh_var "tappe$"
                                                                                           (vid :: venv :: nil) :: nil)
                                                                                        :: fresh_var "tappe$"
                                                                                        (vid :: venv :: nil) :: nil))))
                                                     (NNRCIf
                                                        (NNRCBinop AEq
                                                                   (NNRCUnop (ARecProject sl)
                                                                             (NNRCVar
                                                                                (fresh_var "tsel$"
                                                                                           (fresh_var "tmap$"
                                                                                                      (vid
                                                                                                         :: fresh_var "tappe$"
                                                                                                         (vid :: venv :: nil)
                                                                                                         :: nil)
                                                                                                      :: fresh_var "tappe$"
                                                                                                      (fresh_var "tmap$"
                                                                                                                 (vid
                                                                                                                    :: 
                                                                                                                    fresh_var "tappe$"
                                                                                                                    (vid :: venv :: nil)
                                                                                                                    :: nil)
                                                                                                                 :: 
                                                                                                                 fresh_var "tappe$"
                                                                                                                 (vid :: venv :: nil)
                                                                                                                 :: nil) :: nil))))
                                                                   (NNRCUnop (ADot "$key")
                                                                             (NNRCVar
                                                                                (fresh_var "tappe$"
                                                                                           (fresh_var "tmap$"
                                                                                                      (vid
                                                                                                         :: fresh_var "tappe$"
                                                                                                         (vid :: venv :: nil)
                                                                                                         :: nil)
                                                                                                      :: fresh_var "tappe$"
                                                                                                      (vid :: venv :: nil) :: nil)))))
                                                        (NNRCUnop AColl
                                                                  (NNRCVar
                                                                     (fresh_var "tsel$"
                                                                                (fresh_var "tmap$"
                                                                                           (vid
                                                                                              :: fresh_var "tappe$"
                                                                                              (vid :: venv :: nil) :: nil)
                                                                                           :: fresh_var "tappe$"
                                                                                           (fresh_var "tmap$"
                                                                                                      (vid
                                                                                                         :: 
                                                                                                         fresh_var "tappe$"
                                                                                                         (vid :: venv :: nil)
                                                                                                         :: nil)
                                                                                                      :: fresh_var "tappe$"
                                                                                                      (vid :: venv :: nil)
                                                                                                      :: nil) :: nil))))
                                                        (NNRCConst (dcoll nil)))))))
                           (NNRCVar
                              (fresh_var "tmap$"
                                         (vid :: fresh_var "tappe$" (vid :: venv :: nil) :: nil)))))).
  
  Lemma pick_fresh_distinct_second v v1 v2 rest:
    exists v3,
      v3 = (fresh_var v (v1 :: v2 :: rest)) /\
      v2 <> v3.
  Proof.
    exists (fresh_var v (v1 :: v2 :: rest)).
    split;[reflexivity| ].
    apply fresh_var_fresh2.
  Qed.

  Lemma build_group_ext (x:data) (o1 o2:option data) :
    o1 = o2 ->
    match o1 with
    | Some dunit => None
    | Some (dnat _) => None
    | Some (dbool _) => None
    | Some (dstring _) => None
    | Some (dcoll _) => None
    | Some (drec r1) =>
      match x with
      | dunit => None
      | dnat _ => None
      | dbool _ => None
      | dstring _ => None
      | dcoll _ => None
      | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
      | dleft _ => None
      | dright _ => None
      | dbrand _ _ => None
      | dforeign _ => None
      end
    | Some (dleft _) => None
    | Some (dright _) => None
    | Some (dbrand _ _) => None
    | Some (dforeign _) => None
    | None => None
    end =
    match o2 with
    | Some dunit => None
    | Some (dnat _) => None
    | Some (dbool _) => None
    | Some (dstring _) => None
    | Some (dcoll _) => None
    | Some (drec r1) =>
      match x with
      | dunit => None
      | dnat _ => None
      | dbool _ => None
      | dstring _ => None
      | dcoll _ => None
      | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
      | dleft _ => None
      | dright _ => None
      | dbrand _ _ => None
      | dforeign _ => None
      end
    | Some (dleft _) => None
    | Some (dright _) => None
    | Some (dbrand _ _) => None
    | Some (dforeign _) => None
    | None => None
    end.
  Proof.
    intros Hinput; rewrite Hinput; clear Hinput.
    reflexivity.
  Qed.

  (** The following states that the principal definition for group by and this alternative are equivalent. *)
  
  Lemma nnrc_core_eval_group_by_eq {cenv} env (g:string) (sl:list string) (e1 e2:nnrc):
    nnrc_core_eval h cenv env e1 = nnrc_core_eval h cenv env e2 ->
    forall vid venv,
      nnrc_core_eval h cenv env (nnrc_group_by g sl e1)
      = nnrc_core_eval h cenv env (nnrc_group_by_from_nraenv vid venv g sl e2).
  Proof.
    intro Heval; intros.
    unfold nnrc_group_by, nnrc_group_by_from_nraenv.
    Opaque fresh_var.
    simpl.
    rewrite <- Heval; clear Heval.
    destruct (nnrc_core_eval h cenv env e1); [|reflexivity]; simpl; clear e1 e2.
    generalize (fresh_var "tappe$" (vid :: venv :: nil)); intro v0.
    destruct (equiv_dec v0 v0); try congruence.
    destruct d; try reflexivity; simpl.
    generalize (pick_fresh_distinct_second "tmap$" vid v0 nil); intros Hpick.
    elim Hpick; clear Hpick; intro v1; intros.
    elim H; clear H; intros.
    assert ((fresh_var
               (String
                  (Ascii.Ascii false false true false true true true false)
                  (String
                     (Ascii.Ascii true false true true false true true false)
                     (String
                        (Ascii.Ascii true false false false false true true
                                     false)
                        (String
                           (Ascii.Ascii false false false false true true true
                                        false)
                           (String
                              (Ascii.Ascii false false true false false true
                                           false false) EmptyString)))))
               (@cons string vid (@cons string v0 (@nil string)))) =
            fresh_var "tmap$" (vid :: v0 :: nil)).
    reflexivity.
    rewrite H1 in H; clear H1.
    rewrite <- H; clear H.
    destruct (equiv_dec v1 v1); try congruence; clear e0.
    rewrite <- rmap_with_rproject.
    destruct (rmap
                (fun d1 : data =>
                   match d1 with
                   | dunit => None
                   | dnat _ => None
                   | dbool _ => None
                   | dstring _ => None
                   | dcoll _ => None
                   | drec r => Some (drec (rproject r sl))
                   | dleft _ => None
                   | dright _ => None
                   | dbrand _ _ => None
                   | dforeign _ => None
                   end) l); try reflexivity; simpl.
    f_equal.
    apply rmap_ext; intros. simpl.
    destruct (equiv_dec v0 v1); try congruence; clear c; simpl.
    destruct (equiv_dec (fresh_var "tappe$" (v1 :: v0 :: nil))
                        (fresh_var "tappe$" (v1 :: v0 :: nil))); try congruence;
      simpl; clear e0.
    unfold olift2.
    apply build_group_ext.
    f_equal.
    f_equal.
    f_equal.
    apply rmap_ext; intros.
    unfold olift.
    generalize (fresh_var "tappe$" (v1 :: v0 :: nil)); intros v2.
    destruct (equiv_dec (fresh_var "tsel$" (v1 :: v2 :: nil))
                        (fresh_var "tsel$" (v1 :: v2 :: nil))); try congruence;
      clear e0; simpl.
    generalize (pick_fresh_distinct_second "tsel$" v1 v2 nil); intros Hpick.
    elim Hpick; clear Hpick; intro v3; intros.
    elim H2; clear H2; intros.
    rewrite <- H2; clear H2.
    destruct (equiv_dec v2 v3); try congruence; clear c.
    simpl.
    reflexivity.
  Qed.

  (** * Unnest *)
  
  Definition unnest_from_nraenv vid venv a b n1 := 
    (NNRCFor (fresh_var "tmap$" (vid :: venv :: nil))
             (NNRCUnop AFlatten
                       (NNRCFor (fresh_var "tmc$" (vid :: venv :: nil))
                                n1
                                (NNRCFor
                                   (fresh_var "tmc$" (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil))
                                   (NNRCFor (fresh_var "tmap$" (vid :: venv :: nil))
                                            (NNRCUnop (ADot a) (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil))))
                                            (NNRCUnop (ARec b) (NNRCVar (fresh_var "tmap$" (vid :: venv :: nil)))))
                                   (NNRCBinop AConcat (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil)))
                                              (NNRCVar
                                                 (fresh_var "tmc$"
                                                            (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil)))))))
             (NNRCUnop (ARecRemove a) (NNRCVar (fresh_var "tmap$" (vid :: venv :: nil))))).
  
  Definition unnest_from_nraenv_core vid venv a b n1 :=
    (NNRCFor (fresh_var "tmap$" (vid :: venv :: nil))
             (NNRCUnop AFlatten
                       (NNRCFor (fresh_var "tmc$" (vid :: venv :: nil))
                                n1
                                (NNRCFor
                                   (fresh_var "tmc$" (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil))
                                   (NNRCFor
                                      (fresh_var "tmap$" (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil))
                                      (NNRCUnop (ADot a) (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil))))
                                      (NNRCUnop (ARec b)
                                                (NNRCVar
                                                   (fresh_var "tmap$"
                                                              (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil)))))
                                   (NNRCBinop AConcat (NNRCVar (fresh_var "tmc$" (vid :: venv :: nil)))
                                              (NNRCVar
                                                 (fresh_var "tmc$"
                                                            (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil)))))))
             (NNRCUnop (ARecRemove a) (NNRCVar (fresh_var "tmap$" (vid :: venv :: nil))))).

  Lemma unnest_from_nraenv_and_nraenv_core_eq {cenv} vid venv env a b op1 op1' :
    nnrc_core_eval h cenv env op1 = nnrc_core_eval h cenv env op1' ->
    nnrc_core_eval h cenv env (unnest_from_nraenv vid venv a b op1) =
    nnrc_core_eval h cenv env (unnest_from_nraenv_core vid venv a b op1').
  Proof.
    intros Hind.
    Opaque fresh_var.
    simpl.
    rewrite Hind; clear Hind.
    destruct (nnrc_core_eval h cenv env op1'); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct (equiv_dec (fresh_var "tmap$" (vid :: venv :: nil))
                        (fresh_var "tmap$" (vid :: venv :: nil))); try congruence.
    destruct (equiv_dec (fresh_var "tmc$" (vid :: venv :: nil))
                        (fresh_var "tmc$" (vid :: venv :: nil))); try congruence.
    simpl in *.
    destruct (equiv_dec
                (fresh_var "tmc$"
                           (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil))
                (fresh_var "tmc$"
                           (fresh_var "tmc$" (vid :: venv :: nil) :: vid :: venv :: nil)));
      try congruence; simpl.
    destruct (equiv_dec
                (fresh_var "tmap$"
                           (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil))
                (fresh_var "tmap$"
                           (fresh_var "tmc$" (vid :: venv :: nil) :: venv :: nil))); try congruence; simpl in *.
    destruct (equiv_dec (fresh_var "tmc$" (vid :: venv :: nil))
                        (fresh_var "tmc$"
                                   (fresh_var "tmc$" (vid :: venv :: nil)
                                              :: vid :: venv :: nil))). auto.
    clear e e0 e1 e2 c.
    f_equal.
    induction l; [reflexivity| ]; simpl.
    destruct a0; try reflexivity.
  Qed.
  
End NNRCSugar.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
