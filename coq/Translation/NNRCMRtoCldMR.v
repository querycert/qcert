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

Section NNRCMRToCldMR.
  Require Import String.
  Require Import List.
  Require Import Sorting.Mergesort.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.
  Require Import NNRCRuntime.
  Require Import NNRCMRRuntime.
  Require Import ForeignCloudant.
  Require Import ForeignToCloudant.
  Require Import CldMRUtil.
  Require Import CldMR.
  
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {fcloudant:foreign_cloudant}.
  Context {ftocloudant:foreign_to_cloudant}.

  Context (h:list(string*string)).

  (********************************
   * NNRCMR to ♥ NNRCMRCloudant ♥ *
   ********************************)

  (* unless provided, the input var for the emit is assumed to be the
     same as the input var for the map ... *)
  (* Java equivalent: NrcmrToCldmr.MRtoMapCld *)
  Definition MRtoMapCld (mrmap: NNRCMR.map_fun) (collectflag:bool) (index:nat) : cld_map :=
    let emit :=
        if collectflag then CldEmitCollect O else CldEmitDist
    in
    match mrmap with
    | MapDist (x, n) => mkMapCld (CldMapId (x, n)) emit
    | MapDistFlatten (x, n) => mkMapCld (CldMapFlatten (x, n)) emit
    | MapScalar (x, n) => mkMapCld (CldMapFlatten (x,n)) emit
    end.

  (* Java equivalent: NrcmrtoCldmr.pushReduce *)
  Definition pushReduce (avoiddb: list var) (r:(var*nnrc)) : cld_reduce * (var*cld_map) :=
    let fresh_outputdb := fresh_var "output_" avoiddb in
    let pushed_reduce := collectReduce (Some fresh_outputdb) in
    let v_red := fst r in
    let f_red := snd r in
    (* Deals with Cloudant's implicit mapping of results into 'key'/'value' records *)
    let pushed_map := MRtoMapCld (MapScalar (v_red,NNRCUnop OpBag f_red)) true 0 in
    (pushed_reduce, (fresh_outputdb, pushed_map)).

  (* Java equivalent: NrcmrtoCldmr.pushMR *)
  Definition pushMR (dbinput dboutput:var) (pushed_map: cld_map) (mrempty:option nnrc) :=
    mkMRCld dbinput pushed_map (Some (idReduce (Some dboutput))) mrempty.
  
  Definition pushMRNoRed (dbinput:var) (pushed_map: cld_map) (mrempty:option nnrc) :=
    mkMRCld dbinput pushed_map None mrempty.

  Definition minMap :=
    let x := "x"%string in
    let map_fun := (x, NNRCUnop (OpDot "min") (NNRCVar x)) in
    mkMapCld (CldMapId map_fun) (CldEmitCollect O).

  Definition minMR (stats_v out_v: var) :=
    mkMRCld stats_v minMap (Some (idReduce (Some out_v))).

  Definition minMRNoRed (stats_v: var) :=
    mkMRCld stats_v minMap None.

  Definition maxMap :=
    let x := "x"%string in
    let map_fun := (x, NNRCUnop (OpDot "max") (NNRCVar x)) in
    mkMapCld (CldMapId map_fun) (CldEmitCollect O).

  Definition maxMR (stats_v out_v: var) :=
    mkMRCld stats_v maxMap (Some (idReduce (Some out_v))).

  Definition maxMRNoRed (stats_v: var) :=
    mkMRCld stats_v maxMap None.

  (* Java equivalent: NrcmrToCldmr.MRtoReduceCld *)
  Definition MRtoReduceCld (v_key:var) (out_v:var) (avoiddb: list var) (mrr: NNRCMR.reduce_fun) (mrempty:option nnrc) :
    bool * cld_reduce * (option cldmr_step) * (list var) :=
    match mrr with
    | RedId => (false, idReduce (Some out_v), None, avoiddb)
    | RedCollect redf =>
      let '(pushed_red, (newdbout,pushed_map)) := pushReduce avoiddb redf in
      let pushed_mr := pushMR newdbout out_v pushed_map mrempty in
      (true, pushed_red, Some pushed_mr, newdbout::avoiddb)
    | RedOp op =>
      match op with
      | RedOpForeign frop =>
        (true, opReduce (foreign_to_cloudant_reduce_op frop) (Some out_v), None, avoiddb)
      end
    | RedSingleton => (true, idReduce (Some out_v), None, avoiddb)
    end.

  (* Java equivalent: NrcmrToCldmr.MRtoMRCld *)
  Definition MRtoMRCld (avoiddb: list var) (mr: mr) : (list cldmr_step) * (list var) :=
    let cld_input := mr_input mr in
    let cld_output := mr_output mr in
    let mrmap := mr_map mr in
    let mrred := mr_reduce mr in
    let mrempty := mr_reduce_empty h mr in
    let v_key :=
        match mrmap with
        | MapDist (x, _) => x
        | MapDistFlatten (x, _) => x
        | MapScalar (x, _) => x
        end
    in
    let '(collectflag, first_reduce,pushedmr,avoiddb') := MRtoReduceCld v_key cld_output avoiddb mrred mrempty in
    let cld_map := MRtoMapCld mrmap collectflag 0 in
    match pushedmr with
    | None => (mkMRCld cld_input cld_map (Some first_reduce) mrempty :: nil, avoiddb')
    | Some nextmr => ((mkMRCld cld_input cld_map (Some first_reduce) (Some (NNRCConst (dcoll nil)))) :: nextmr :: nil, avoiddb')
                       (* EMPTY REDUCE IS EMPTY COLL IF REDUCE IS PUSHED! *)
    end.
  
  Definition cld_data_of_localized_data (locd:ddata) : list data :=
    match locd with
    | Dlocal d => (d::nil)
    | Ddistr dl => dl
    end.

  (* For now keep that based on single inputdb ... *)
  (*
  Definition cldmr_eval_pair (initdb initunit:var) (mrl:cldmr) (coll:list data) :
    option (list data) :=
    let cenv := (initdb, coll) :: nil in
    let env := cld_load_init_env initunit cenv in
    lift snd (cldmr_eval h env mrl).
   *)

  Lemma rmap_with_key (prefix:list nat) (i:nat) (v:var) (n:nnrc) (coll: list data) :
    (rmap
       (fun d : data * data =>
          let (k, v0) := d in
          match nnrc_core_eval h nil ((v, v0) :: nil) n with
          | Some res => Some (k, res)
          | None => None
          end) (init_keys_aux prefix i coll)) =
    lift (init_keys_aux prefix i)
         (rmap (fun d : data => nnrc_core_eval h nil ((v, d) :: nil) n) coll).
  Proof.
    revert i.
    induction coll; try reflexivity; simpl; intros.
    destruct (nnrc_core_eval h nil ((v, a) :: nil) n); try reflexivity; simpl.
    rewrite (IHcoll (S i)); clear IHcoll.
    destruct ((rmap (fun d0 : data => nnrc_core_eval h nil ((v, d0) :: nil) n) coll)); reflexivity.
  Qed.

  Lemma rmap_eval_through_init_keys (l:list data) (n:nnrc) (v:var) :
    (rmap (fun d : data * data =>
             let (k, v0) := d in
             match nnrc_core_eval h nil ((v, v0) :: nil) n with
             | Some res0 => Some (k, res0)
             | None => None
             end) (init_keys l))
    = lift init_keys (rmap (fun d : data => nnrc_core_eval h nil ((v, d) :: nil) n) l).
  Proof.
    unfold init_keys.
    apply rmap_with_key.
  Qed.

  Lemma MRtoMRCld_preserves_causally_consistent (init_unit:var) (mr:mr) :
    mr.(mr_input) <> mr.(mr_output) ->
    mr.(mr_output) <> init_unit ->
    init_unit <> mr.(mr_input) ->
    cldmr_chain_causally_consistent (fst (MRtoMRCld (mr.(mr_input) :: mr.(mr_output) :: init_unit :: nil) mr)) = true.
  Proof.
    intros.
    unfold MRtoMRCld.
    unfold MRtoReduceCld.
    destruct mr; simpl in *.
    destruct mr_reduce;
      unfold
        cldmr_chain_causally_consistent,
      cldmr_step_causally_consistent,
      nequiv_decb, equiv_decb; simpl.
    - match_destr.
      congruence.
    - destruct (equiv_dec mr_input mr_output); [ congruence | ].
      (** TODO: currently false *)
      admit.
    - destruct r; simpl;
      match_destr;
      try congruence.
    - match_destr; congruence.
  Admitted.


(*
  Lemma MRtoMRCld_correct (init_unit:var) (mr: mr) :
    mr.(mr_input) <> mr.(mr_output) ->
    mr.(mr_output) <> init_unit ->
    init_unit <> mr.(mr_input) ->
    forall (locd:localized_data),
    forall (res: localized_data),
      mr_eval h mr locd = Some res ->
      cldmr_eval_pair (mr.(mr_input)) init_unit
                        (fst (MRtoMRCld nil mr)) (cld_data_of_localized_data locd) =
      Some (cld_data_of_localized_data res).
  Proof.
    intros Hio Hou Hui.
    intros.
    destruct mr; simpl in *.
    unfold mr_eval, cldmr_eval_pair, cldmr_eval; simpl.
    unfold MRtoMRCld; simpl.
    destruct mr_map; simpl.
    (* MapDist *)
    - destruct p; simpl in *.
      destruct locd; simpl in *; unfold mr_eval in *; simpl in *; try congruence.
      destruct mr_reduce; simpl in *.
      (* RedId *)
      + unfold cldmr_eval_inner; simpl.
        unfold equiv_dec; destruct (string_eqdec mr_input init_unit); try congruence; clear c.
        unfold equiv_dec; destruct (string_eqdec mr_input mr_input); try congruence; clear e.
        simpl.
        rewrite pre_pack_pack_unpack_kvl_id; simpl.
        unfold cldmr_step_eval; simpl.
        unfold cldmr_step_map_eval; simpl.
        unfold apply_map_fun_with_keys; simpl.
        rewrite rmap_eval_through_init_keys.
        revert H; generalize (rmap (fun d : data => nnrc_core_eval h ((v, d) :: nil) n) l);
        intros omap1res; intros.
        destruct omap1res; simpl in *; try congruence.
        inversion H.
        subst; clear H.
        unfold cld_merge_env; simpl.
        unfold equiv_dec; destruct (string_eqdec mr_output mr_input); try congruence; clear c.
        unfold equiv_dec; destruct (string_eqdec mr_output init_unit); try congruence; clear c.
        simpl.
        rewrite get_values_of_init_same; try reflexivity.
      (* RedCollect *)
      + admit.
      (* RedOp *)
      + admit.
      (* RedSingleton *)
      + admit.
    (* MapDistFlatten *)
    - destruct p; simpl.
      destruct locd; simpl in *; unfold mr_eval in *; simpl in *; try congruence.
      destruct mr_reduce; simpl in *.
      (* RedId *)
      + unfold cldmr_eval_inner; simpl.
        unfold equiv_dec; destruct (string_eqdec mr_input init_unit); try congruence; clear c.
        unfold equiv_dec; destruct (string_eqdec mr_input mr_input); try congruence; clear e.
        simpl.
        rewrite pre_pack_pack_unpack_kvl_id; simpl.
        unfold cldmr_step_eval; simpl.
        unfold cldmr_step_map_eval; simpl.
        unfold apply_map_fun_with_keys; simpl.
        rewrite rmap_eval_through_init_keys.
        revert H; generalize (rmap (fun d : data => nnrc_core_eval h ((v, d) :: nil) n) l);
        intros omap1res; intros.
        destruct omap1res; simpl in *; try congruence.
        unfold mr_reduce_eval in *; simpl in *.
        admit.
      (* RedCollect *)
      + admit.
      (* RedOp *)
      + admit.
      (* RedSingleton *)
      + admit.
    (* MapScalar *)
    - destruct p; simpl.
      destruct locd; simpl in *; unfold mr_eval in *; simpl in *; try congruence.
      destruct mr_reduce; simpl in *.
      (* RedId *)
      + unfold cldmr_eval_inner; simpl.
        unfold equiv_dec; destruct (string_eqdec mr_input init_unit); try congruence; clear c.
        unfold equiv_dec; destruct (string_eqdec mr_input mr_input); try congruence; clear e.
        simpl.
        unfold cldmr_step_eval; simpl.
        unfold cldmr_step_map_eval; simpl.
        unfold apply_map_fun_with_keys; simpl.
        destruct (nnrc_core_eval h ((v, d) :: nil)); simpl in *; try congruence.
        destruct d0; simpl in *; try congruence.
        inversion H; subst; clear H.
        rename l into mapres; simpl in *.
        unfold cldmr_step_reduce_eval; simpl.
        rewrite (init_like_first_map_index 0); simpl.
        unfold cld_merge_env; simpl.
        unfold equiv_dec; destruct (string_eqdec mr_output mr_input); try congruence; clear c.
        unfold equiv_dec; destruct (string_eqdec mr_output init_unit); try congruence; clear c.
        simpl.
        rewrite app_nil_r.
        rewrite get_values_of_prefixed_init_same; try reflexivity.
      (* RedCollect *)
      + admit.
      (* RedOp *)
      + admit.
      (* RedSingleton *)
      + admit.
  Admitted.
*)

  (* Java equivalent: NrcmrToCldmr.mr_chain_to_cldmr_chain *)
  Fixpoint mr_chain_to_cldmr_chain (avoiddb: list var) (l: list mr) : list cldmr_step :=
    match l with
    | nil => nil
    | mr :: l' =>
      let (cldmr_step,avoiddb') := (MRtoMRCld avoiddb mr) in
      cldmr_step ++ (mr_chain_to_cldmr_chain avoiddb' l')
    end.

  (* Java equivalent: NrcmrToCldmr.mr_last_to_cldmr_last *)
  Definition mr_last_to_cldmr_last
             (mr_last_closure:(list var * nnrc) * list (var * dlocalization))
    : (list var * nnrc) * list var :=
    let (fvs, mr_last) := fst mr_last_closure in
    let vars_loc := snd mr_last_closure in
    let cldmr_last :=
        List.fold_right
          (fun fv k =>
             match lookup equiv_dec vars_loc fv with
             | None => k (* assert false: should not occur *)
             | Some Vdistr =>
               (* let kv : var := really_fresh_in "$"%string "kv"%string nil k in *)
               NNRCLet fv (NNRCVar fv) k
             | Some Vlocal =>
               NNRCLet fv
                      (NNRCEither (NNRCUnop OpSingleton (NNRCVar fv))
                                 fv (NNRCVar fv)
                                 fv (NNRCConst dunit)) (* must not be executed *)
                      k
             end)
          mr_last fvs
    in
    ((fvs, cldmr_last), map fst vars_loc).

  (* Java equivalent: nrcmrToCldmr.NNRCMRtoNNRCMRCloudant *)
  Definition NNRCMRtoNNRCMRCloudant (avoiddb: list var) (mrl: nnrcmr) : cldmr :=
    (* Used to compute a separate var_locs distinct from mr_last effective params -- removed now.
       This should be reviewed by Louis *)
    mkMRCldChain
      (mr_chain_to_cldmr_chain avoiddb mrl.(mr_chain))
      (mr_last_to_cldmr_last mrl.(mr_last)).

  Require Import Bool.

  Lemma MRtoMRCld_causally_consistent
        avoiddb (mr:mr) :
    In mr.(mr_input) avoiddb ->
    mr_causally_consistent mr mr = true ->
    forall x,
    forallb (fun y => cldmr_step_input y <>b mr.(mr_output)) x = true ->
    cldmr_chain_causally_consistent x = true ->
    incl (mr.(mr_output) :: map cldmr_step_input x) avoiddb ->
         cldmr_chain_causally_consistent (x ++ fst (MRtoMRCld avoiddb mr)) = true.
Proof.
    intros.
    unfold MRtoMRCld.
    unfold MRtoReduceCld.
    destruct mr; simpl in *.
    destruct mr_reduce;
      unfold
        cldmr_chain_causally_consistent,
      cldmr_step_causally_consistent,
      mr_causally_consistent,
      nequiv_decb, equiv_decb in *; simpl.
    - apply forallb_ordpairs_refl_app_cons; trivial.
    - rewrite app_cons_cons_expand.
      apply forallb_ordpairs_refl_app_cons; simpl.
      + apply forallb_ordpairs_refl_app_cons; simpl in *; trivial.
        * match_destr.
          rewrite e in H.
          apply fresh_var_fresh in H.
          intuition.
        * rewrite forallb_forall in *.
          intros aa inn.
          match_destr.
          unfold incl in H3.
          specialize (H3 (cldmr_step_input aa)).
          rewrite e in H3.
          eelim fresh_var_fresh.
          apply H3.
          simpl.
          rewrite in_map_iff.
          eauto.
      + match_destr.
        rewrite <- e in H3.
        unfold incl in H3.
        simpl in H3.
        eelim fresh_var_fresh.
        intuition.
      + simpl in *.
        match_destr_in H0.
        rewrite forallb_app; simpl. rewrite H1.
        match_destr; simpl.
        congruence.
        intuition.
    - destruct r;
      try solve [ apply forallb_ordpairs_refl_app_cons; simpl; trivial ].
    - apply forallb_ordpairs_refl_app_cons; simpl; trivial.
  Qed.

  Lemma MRtoMRCid_avoids avoiddb a :
    let '(l0, l1) := MRtoMRCld avoiddb a in
    incl (mr_input a :: nil) avoiddb ->
    incl (avoiddb ++ map cldmr_step_input l0) l1.
  Proof.
    unfold MRtoMRCld, MRtoReduceCld.
    destruct a; simpl.
    destruct mr_reduce; simpl.
    - unfold incl; simpl; intros.
      repeat rewrite in_app_iff in H0.
      intuition.
    - unfold incl; simpl; intros.
      repeat rewrite in_app_iff in H0; simpl in H0.
      intuition.
    - destruct r; simpl;
      unfold incl; simpl; intros;
      repeat rewrite in_app_iff in H0; simpl in H0;
      intuition.
    - unfold incl; simpl; intros.
      repeat rewrite in_app_iff in H0; simpl in H0.
      intuition.
  Qed.

  Lemma MRtoMRCid_input_avoids avoiddb a :
    let '(l0, l1) := MRtoMRCld avoiddb a in
    Forall (fun x => cldmr_step_input x = mr_input a \/ ~ In (cldmr_step_input x) avoiddb) l0.
  Proof.
    Hint Resolve fresh_var_fresh.
    unfold MRtoMRCld, MRtoReduceCld.
    destruct a; simpl.
    destruct mr_reduce; simpl.
    - eauto.
    - econstructor; simpl; [intuition | ].
      econstructor; simpl; [| intuition ].
      eauto.
    - destruct r;
      eauto.
    - eauto.
  Qed.
  
  Lemma NNRCMRtoNNRCMRCloudant_causally_consistent avoiddb l :
    mr_chain_causally_consistent l = true ->
    forall x,
      cldmr_chain_causally_consistent x = true ->
      forallb (fun a => forallb (fun y : cldmr_step => cldmr_step_input y <>b mr_output a) x) l = true ->
      incl (map mr_input l ++ map mr_output l ++ map cldmr_step_input x) avoiddb ->
      cldmr_chain_causally_consistent (x ++ mr_chain_to_cldmr_chain avoiddb l) = true.
  Proof.
    unfold mr_chain_causally_consistent, cldmr_chain_causally_consistent.
    revert avoiddb.
    induction l; intros avoiddb lcc x xcc avoided.
    { rewrite app_nil_r; trivial. }
    simpl in *.
    repeat rewrite andb_true_iff in * .
    intuition.
    destruct l.
    - admit. (* XXXXXXXXXXXXX *)
      (* rewrite app_nil_r. *)
      (* apply MRtoMRCldLast_causually_consistent; trivial. *)
      (* simpl in *. *)
      (* unfold incl in *; simpl in *; intuition. *)
    - match_case; intros.
       rewrite <- app_ass.
       apply IHl.
       + simpl in * .
         repeat rewrite andb_true_iff in * .
         intuition.
       + generalize (MRtoMRCld_causally_consistent avoiddb a).
         rewrite H0; simpl; intros HH.
         apply HH; clear HH; simpl; trivial.
         * unfold incl in *; simpl in *.
           intuition.
         * unfold incl in *.
           simpl.
           intros aa inn.
           specialize (H aa).
           repeat (simpl in H; rewrite in_app_iff in H).
           intuition.
       + simpl in *.
         repeat rewrite andb_true_iff in *.
         rewrite forallb_app.
         intuition.
         * generalize (MRtoMRCid_input_avoids avoiddb a).
           rewrite H0.
           rewrite Forall_forall, forallb_forall.
           intros HH ? inn2.
           specialize (HH _ inn2).
           unfold nequiv_decb, equiv_decb.
           match_destr.
           rewrite e in * .
           { destruct HH as [eqq|inn3].
             - unfold mr_causally_consistent in H3.
               unfold nequiv_decb, equiv_decb in H3.
               match_destr_in H3.
               congruence.
             - elim inn3.
               apply (H (mr_output m)).
               repeat (simpl; rewrite in_app_iff); intuition.
           } 
         * rewrite forallb_forall in H8 |- *.
           intros ? inn.
           specialize (H8 _ inn).
           rewrite forallb_app.
           split; trivial.
           generalize (MRtoMRCid_input_avoids avoiddb a).
           rewrite H0.
           rewrite Forall_forall, forallb_forall.
           intros HH ? inn2.
           specialize (HH _ inn2).
           unfold nequiv_decb, equiv_decb.
           match_destr.
           rewrite e in * .
           { destruct HH as [eqq|inn3].
             - rewrite forallb_forall in H9.
               specialize (H9 _ inn).
               unfold mr_causally_consistent in H9.
               unfold nequiv_decb, equiv_decb in H9.
               match_destr_in H9.
               congruence.
             - elim inn3.
               apply (H (mr_output x0)).
               cut (In (mr_output x0) (map mr_output l)).
               + repeat (simpl; rewrite in_app_iff); intuition.
               + rewrite in_map_iff. eauto.
           } 
       + generalize (MRtoMRCid_avoids avoiddb a).
         rewrite H0; intros inc.
         rewrite <- inc; clear inc; unfold incl in *; simpl in *;
           intros aa inn;
           specialize (H aa);
             repeat (rewrite in_app_iff in H; simpl in H).
         * rewrite in_app_iff.
           rewrite map_app in inn.
           repeat (rewrite in_app_iff in inn; simpl in inn).
           intuition.
         * intuition.
  Admitted.

(*
  Definition NNRCMRtoNNRCMRCloudantInit (avoiddb: list var) (l: nnrcmr) : cldmr :=
    match l with
    | nil => nil
    | mrtop :: nil =>
      (MRtoMRCldLast avoiddb mrtop) ++ nil
    | mr :: l' =>
      let (cld_mr,avoiddb') := MRtoMRCld avoiddb mr in
      cld_mr ++ (NNRCMRtoNNRCMRCloudant avoiddb' l')
    end.

    Lemma NNRCMRtoNNRCMRCloudantInit_causally_consistent avoiddb l :
    nnrcmr_causally_consistent l = true ->
    forall x,
      cld_mr_chain_causally_consistent x = true ->
      forallb (fun a => forallb (fun y : cld_mr => cld_mr_input y <>b mr_output a) x) l = true ->
      incl (map mr_input l ++ map mr_output l ++ map cld_mr_input x) avoiddb ->
      cld_mr_chain_causally_consistent (x ++ NNRCMRtoNNRCMRCloudantInit avoiddb l) = true.
    Proof.
      intros.
      unfold NNRCMRtoNNRCMRCloudantInit.
      destruct l.
      - rewrite app_nil_r; trivial.
      - destruct l.
        + rewrite app_nil_r.
           apply MRtoMRCldLast_causually_consistent; trivial.
          * unfold nnrcmr_causally_consistent in H.
            simpl in H.
            repeat rewrite andb_true_iff in H.
            intuition.
          * unfold incl in * ; simpl in *.
            intuition.
        + match_case; intros ? ? eqq.
          rewrite <- app_ass.
          apply NNRCMRtoNNRCMRCloudant_causally_consistent; simpl; trivial.
          * unfold nrcmr_causally_consistent in * ; simpl in *.
            repeat rewrite andb_true_iff in * .
            intuition.
          * generalize (MRtoMRCld_causally_consistent avoiddb m).
            rewrite eqq; simpl.
            { intros HH; apply HH; clear HH.
              - apply H2. simpl; intuition.
              - unfold nnrcmr_causally_consistent in H.
                simpl in H.
                repeat rewrite andb_true_iff in H; intuition.
              - simpl in H1.
                repeat rewrite andb_true_iff in H1; intuition.
              - trivial.
              - unfold incl in *; simpl in *.
                intros aa inn.
                apply (H2 aa).
                repeat (simpl; rewrite in_app_iff).
                intuition.
            } 
          * simpl in *. repeat rewrite andb_true_iff in *.
           generalize (MRtoMRCid_input_avoids avoiddb m).
           rewrite eqq.
           rewrite Forall_forall.
           intros inn1.
           rewrite forallb_app.
           { intuition.
             - rewrite forallb_forall in * .
               intros ? inn2.
               specialize (inn1 _ inn2).
               unfold nequiv_decb, equiv_decb.
               match_destr.
               rewrite e in inn1.
               destruct inn1 as [eqq3|inn3].
               + unfold nnrcmr_causally_consistent in H.
                 simpl in H.
                 repeat rewrite andb_true_iff in H.
                 intuition.
                 unfold mr_causally_consistent in H6.
                 unfold nequiv_decb, equiv_decb in H6.
                 match_destr_in H6.
                 congruence.
               + elim inn3.
                 specialize (H2 (mr_output m0)).
                 repeat (simpl in H2; rewrite in_app_iff in H2).
                 intuition.
             - rewrite forallb_forall.
               intros ? inn2.
               rewrite forallb_app.
               rewrite forallb_forall in H5.
               specialize (H5 _ inn2).
               split; trivial.
               rewrite forallb_forall in * .
               intros ? inn3.
               unfold nequiv_decb, equiv_decb.
               match_destr.
               specialize (inn1 _ inn3).
               rewrite e in inn1.
               destruct inn1 as [eqq4|inn4].
               + unfold nnrcmr_causally_consistent in H.
                 simpl in H.
                 repeat rewrite andb_true_iff in H.
                 intuition.
                 unfold mr_causally_consistent in H9.
                 rewrite forallb_forall in H9.
                 specialize (H9 _ inn2).
                 unfold nequiv_decb, equiv_decb in H9.
                 match_destr_in H9.
                 congruence.
               + elim inn4.
                 specialize (H2 (mr_output x0)).
                 repeat (simpl in H2; rewrite in_app_iff in H2).
                 intuition.
                 apply H9.
                 rewrite in_map_iff.
                 eauto.
           }
          *  generalize (MRtoMRCid_avoids avoiddb m).
             rewrite eqq; intros inc.
             { rewrite <- inc; clear inc; unfold incl in *; simpl in *;
               intros aa inn;
               specialize (H2 aa);
               repeat (rewrite in_app_iff in H2; simpl in H2).
               - rewrite in_app_iff.
                 rewrite map_app in inn.
                 repeat (rewrite in_app_iff in inn; simpl in inn).
                 intuition.
               -  intuition.
             } 
    Qed.
*)

  (* Java equivalent: NrcmrToCldmr.convert *)
  Definition nnrcmr_to_cldmr_top (mrl: nnrcmr) : cldmr :=
    let avoiddb := List.map mr_input mrl.(mr_chain) ++ List.map mr_output mrl.(mr_chain) in
    NNRCMRtoNNRCMRCloudant avoiddb mrl.

  Lemma nnrcmr_to_cldmr_top_causally_consistent mrl :
    nnrcmr_causally_consistent mrl = true ->
    cldmr_chain_causally_consistent (nnrcmr_to_cldmr_top mrl).(cldmr_chain) = true.
  Proof.
    intros cc.
    unfold nnrcmr_to_cldmr_top.
  (*   generalize (NNRCMRtoNNRCMRCloudantInit_causally_consistent *)
  (*                 (List.map mr_input l ++ List.map mr_output l) l cc nil); simpl; *)
  (*     intros HH. *)
  (*   apply HH. *)
  (*   - reflexivity. *)
  (*   - rewrite forallb_forall; intuition. *)
  (*   - rewrite app_nil_r. reflexivity. *)
  (* Qed. *)
  Admitted.

End NNRCMRToCldMR.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
