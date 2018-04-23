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
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRCRuntime.
Require Import NNRCRuntime.
Require Import NNRCMR.
Require Import ForeignReduceOps.

Section NNRCMRRewrite.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.

  Context (h:list(string*string)).


  (****************************
   * NNRC function properties *
   ****************************)

  (* Id Function *)

  (* Java equivalent: MROptimizer.is_id_function *)  
  Definition is_id_function (f: var * nnrc) :=
    let (x, n) := f in
    match n with
    | NNRCVar y => equiv_decb x y
    | NNRCUnop OpIdentity (NNRCVar y) => equiv_decb x y
    | _ => false
    end.

  (* Coll Function *)

  (* Java equivalent: MROptimizer.is_coll_function *)  
  Definition is_coll_function (f: var * nnrc) :=
    let (x, n) := f in
    match n with
    | NNRCUnop OpBag (NNRCVar y) => equiv_decb x y
    | _ => false
    end.

  (* Constant Function *)
  
  Definition is_constant_function (f: var * nnrc) :=
    let (x, n) := f in
    match n with
    | NNRCConst _ => true
    | _ => false
    end.

  (* Flatten Function *)

  (* Java equivalent: MROptimizer.is_flatten_function *)
  Definition is_flatten_function (f: var * nnrc) :=
    let (x, n) := f in
    match n with
    | NNRCUnop OpFlatten (NNRCVar y) => equiv_decb x y
    | NNRCLet a (NNRCUnop OpFlatten (NNRCVar y)) (NNRCVar b) => equiv_decb x y && equiv_decb a b
    | _ => false
    end.

  Lemma is_flatten_function_correct (x:var) (n:nnrc) (env:bindings) :
    is_flatten_function (x,n) = true ->
    forall d,
      lookup equiv_dec env x = Some d ->
      (nnrc_core_eval h empty_cenv env n) = lift_oncoll (fun l => (lift dcoll (oflatten l))) d.
  Proof.
    intros Hfun d Henv.
    simpl in *.
    destruct n; try congruence; simpl in *.
    - destruct u; try congruence; simpl in *.
      destruct n; try congruence; simpl in *.
      unfold equiv_decb in *.
      dest_eqdec; try congruence.
      rewrite Henv; simpl.
      reflexivity.
    - destruct n1; try congruence; simpl in *.
      destruct u; try congruence; simpl in *.
      destruct n1; try congruence; simpl in *.
      destruct n2; try congruence; simpl in *.
      rewrite Bool.andb_true_iff in Hfun.
      destruct Hfun.
      unfold equiv_decb in *.
      repeat dest_eqdec; try congruence.
      rewrite Henv; simpl.
      destruct (lift_oncoll (fun l : list data => lift dcoll (oflatten l)) d); reflexivity.
  Qed.

  (* Coll/Uncoll functions *)

  Definition is_uncoll_function_arg (f: var * nnrc) :=
    let (x, n) := f in
    match n with
    | NNRCLet a
             (NNRCEither (NNRCUnop OpSingleton (NNRCVar y))
                        b (NNRCVar b')
                        c (NNRCConst dunit))
             n' =>
      equiv_decb x y && equiv_decb b b' && equiv_decb a x
    | _ => false
    end.


  (******************
   * Map properties *
   ******************)

  (* ID Map *)

  (* Java equivalent: MROptimizer.is_id_scalar_map *)
  Definition is_id_scalar_map map :=
    match map with
    | MapDist f => false
    | MapDistFlatten f => false
    | MapScalar f => is_coll_function f
    end.

  Lemma id_scalar_map_correct mr_map d :
    is_id_scalar_map mr_map = true ->
    mr_map_eval h mr_map (Dlocal d) = Some (d::nil).
  Proof.
    intros H_is_id_map.
    destruct mr_map; simpl in *; try congruence.
    destruct p; try congruence; simpl in *.
    destruct n; try congruence; simpl in *.
    destruct u; try congruence; simpl in *.
    destruct n; try congruence; simpl in *.
    unfold equiv_decb in *.
    repeat dest_eqdec; try congruence.
    simpl.
    reflexivity.
  Qed.

  (* Java equivalent: MROptimizer.is_id_dist_map *)
  Definition is_id_dist_map map :=
    match map with
    | MapDist f => is_id_function f
    | MapDistFlatten f => is_coll_function f
    | MapScalar _ => false
    end.

  Lemma id_dist_map_correct mr_map coll :
    is_id_dist_map mr_map = true ->
    mr_map_eval h mr_map (Ddistr coll) = Some coll.
  Proof.
    intros H_is_id_dist_map.
    destruct mr_map.
    - Case "MapDist"%string.
        destruct p; try congruence; simpl in *.
        destruct n; try congruence; simpl in *.
        * unfold equiv_decb in *.
          repeat dest_eqdec; try congruence.
          apply lift_map_id.
        * destruct u; try congruence; simpl in *.
          destruct n; try congruence; simpl in *.
          unfold equiv_decb in *.
          repeat dest_eqdec; try congruence.
          simpl.
          apply lift_map_id.
    - Case "MapDistFlatten"%string.
      destruct p; try congruence; simpl in *.
      destruct n; try congruence; simpl in *.
      destruct u; try congruence; simpl in *.
      destruct n; try congruence; simpl in *.
      unfold equiv_decb in *.
      repeat dest_eqdec; try congruence.
      simpl.
      autorewrite with alg.
      reflexivity.
    - Case "MapScalar"%string.
      inversion H_is_id_dist_map.
  Qed.


  (* Dispatch Map *)

  (* Java equivalent: MROptimizer.is_dispatch_map *)
  Definition is_dispatch_map map :=
    match map with
    | MapScalar f => is_id_function f
    | _ => false
    end.

  Lemma dispatch_map_correct mr_map coll:
    is_dispatch_map mr_map = true ->
    mr_map_eval h mr_map (Dlocal (dcoll coll)) = Some coll.
  Proof.
    intros.
    unfold mr_map_eval; simpl.
    destruct mr_map; simpl in *; try congruence.
    destruct p; try congruence; simpl in *.
    destruct n; try congruence; simpl in *.
    + unfold equiv_decb in *.
      repeat dest_eqdec; try congruence; simpl.
    + destruct u; try congruence; simpl in *.
      destruct n; try congruence; simpl in *.
      unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
      reflexivity.
  Qed.

  (* Scalar Map *)

  Definition is_scalar_map map :=
    match map with
    | MapScalar _ => true
    | _ => false
    end.

  (* Flatten Map *)

  (* Java equivalent: MROptimizer.is_flatten_dist_map *)
  Definition is_flatten_dist_map map :=
    match map with
    | MapDistFlatten f => is_id_function f
    | _ => false
    end.

  Lemma flatten_dist_map_correct mr_map coll:
    is_flatten_dist_map mr_map = true ->
    mr_map_eval h mr_map (Ddistr coll) = oflatten coll.
  Proof.
    intros.
    unfold mr_map_eval; simpl.
    destruct mr_map; simpl in *; try congruence.
    destruct p; try congruence; simpl in *.
    destruct n; try congruence; simpl in *.
    + unfold equiv_decb in *.
      repeat dest_eqdec; try congruence; simpl.
      rewrite lift_map_id.
      reflexivity.
    + destruct u; try congruence; simpl in *.
      destruct n; try congruence; simpl in *.
      unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
      rewrite lift_map_id.
      reflexivity.
  Qed.


  (*********************
   * Reduce properties *
   *********************)

  (* Flatten Reduce *)

  
  (* Java equivalent: MROptimizer.is_flatten_collect *)
  Definition is_flatten_collect red :=
    match red with
    | RedId => false
    | RedCollect reduce => is_flatten_function reduce
    | RedOp op => false
    | RedSingleton => false
    end.

  (* Id Reduce *)

  (* Java equivalent: MROptimizer.is_id_reduce *)  
  Definition is_id_reduce red :=
    match red with
    | RedId => true
    | RedCollect reduce => false
    | RedOp op => false
    | RedSingleton => false
    end.

  Lemma id_reduce_correct red coll:
    is_id_reduce red = true ->
    mr_reduce_eval h red coll = Some (Ddistr coll).
  Proof.
    destruct red; simpl; try congruence.
  Qed.

  (* Collect Reduce *)

  (* Java equivalent: MROptimizer.is_id_collect *)  
  Definition is_id_collect red :=
    match red with
    | RedId => false
    | RedCollect reduce => is_id_function reduce
    | RedOp op => false
    | RedSingleton => false
    end.

  Lemma id_collect_correct red coll:
    is_id_collect red = true ->
    mr_reduce_eval h red coll = Some (Dlocal (dcoll coll)).
  Proof.
    intros Hred.
    destruct red; simpl in *; try congruence;
    try solve [destruct r; simpl; congruence].
    destruct p; simpl in *.
    destruct n; simpl in *; try congruence;
    unfold equiv_decb in *;
    repeat dest_eqdec; simpl in *; try congruence.
    destruct u; simpl in *; try congruence.
    destruct n; simpl in *; try congruence.
    repeat dest_eqdec; simpl in *; try congruence.
 Qed.

  (* singleton *)
  (* Java equivalent: MROptimizer.is_singleton_reduce *)
  Definition is_singleton_reduce red :=
    match red with
    | RedId => false
    | RedCollect _ => false
    | RedOp _ => false
    | RedSingleton => true
    end.

  Lemma singleton_reduce_correct red d:
    is_singleton_reduce red = true ->
    mr_reduce_eval h red (d::nil) = Some (Dlocal d).
  Proof.
    intros Hred.
    destruct red; simpl in *; try congruence;
    try solve [destruct r; simpl; congruence].
 Qed.


  (* uncoll reduce *)
  Definition is_uncoll_collect red :=
    match red with
    | RedId => false
    | RedCollect reduce => is_uncoll_function_arg reduce
    | RedOp op => false
    | RedSingleton => false
    end.

  Definition suppress_uncoll_in_collect_reduce red :=
    match red with
    | RedId => None
    | RedCollect f =>
      if is_uncoll_function_arg f then
        let (x, n) := f in
        match n with
        | NNRCLet a _ n' => Some (RedCollect (a, n'))
        | _ => None
        end
      else
        None
    | RedOp op => None
    | RedSingleton => None
    end.

  Lemma suppress_uncoll_in_collect_reduce_correct reduce coll:
    forall reduce',
      reduce_well_formed reduce ->
      is_uncoll_collect reduce = true ->
      suppress_uncoll_in_collect_reduce reduce = Some reduce' ->
      mr_reduce_eval h reduce (dcoll coll :: nil) =
      mr_reduce_eval h reduce' coll.
  Proof.
    intros reduce' Hwf Hred Hred'.
    destruct reduce; simpl in *; try congruence;
    try solve [destruct r; simpl; congruence].
    destruct p; simpl in *; try congruence.
    destruct n; simpl in *; try congruence.
    destruct n1; simpl in *; try congruence.
    destruct n1_1; simpl in *; try congruence.
    destruct u; simpl in *; try congruence.
    destruct n1_2; simpl in *; try congruence;
    destruct n1_1; simpl in *; try congruence.
    destruct n1_3; simpl in *; try congruence.
    destruct d; simpl in *; try congruence.
    rewrite Hred in *.
    inversion Hred'.
    simpl.
    repeat rewrite Bool.andb_true_iff in Hred.
    destruct Hred.
    destruct H.
    unfold equiv_decb in *.
    repeat dest_eqdec; try congruence.
    simpl.
    clear e0 e H H1 H2 Hred'.
    assert (nnrc_core_eval h empty_cenv ((v, dcoll coll) :: (v, dcoll (dcoll coll :: nil)) :: nil) n2 =
            nnrc_core_eval h empty_cenv ((v, dcoll coll) :: nil) n2) as Heq;
      [ | rewrite <- Heq; reflexivity ].
    apply nnrc_core_eval_equiv_free_in_env.
    intros x Hx.
    unfold lookup.
    repeat dest_eqdec; try congruence.
  Qed.


  (******************
   * M/R Properties *
   ******************)

  (* Id M/R *)

  (* Java equivalent: MROptimizer.is_id_dist_mr *)
  Definition is_id_dist_mr mr :=
    match mr.(mr_reduce) with
    | RedId => is_id_dist_map mr.(mr_map)
    | RedCollect reduce => false
    | RedOp op => false
    | RedSingleton => false
    end.

  Lemma is_id_dist_mr_correct (mr:mr) :
    is_id_dist_mr mr = true ->
    forall loc_d,
      map_well_localized mr.(mr_map) loc_d ->
      match loc_d with
      | Ddistr coll =>
        mr_eval h mr loc_d = Some (Ddistr coll)
      | Dlocal d =>
        mr_eval h mr loc_d = Some (Ddistr (d::nil))
      end.
  Proof.
    intros H_is_id_mr loc_d H_well_localized.
    unfold is_id_dist_mr in H_is_id_mr.
    destruct mr; simpl in *.
    destruct mr_reduce; simpl in *; try congruence;
    try solve [ destruct r; simpl in *; congruence ].
    unfold mr_eval; simpl.
    destruct loc_d; simpl.
    - Case "loc_d is scalar"%string.
      destruct mr_map;
        simpl in *;
        try contradiction; try congruence.
    - Case "loc_d is distributed"%string.
      rewrite (id_dist_map_correct _ _ H_is_id_mr).
      simpl.
      reflexivity.
  Qed.

  (* Java equivalent: MROptimizer.is_id_scalar_mr *)
  Definition is_id_scalar_mr mr :=
    match mr.(mr_reduce) with
    | RedId => false
    | RedCollect reduce => false
    | RedOp op => false
    | RedSingleton => is_id_scalar_map mr.(mr_map)
    end.

  Lemma is_id_scalar_mr_correct (mr:mr) :
    is_id_scalar_mr mr = true ->
    forall loc_d,
      map_well_localized mr.(mr_map) loc_d ->
      match loc_d with
      | Ddistr coll => False
      | Dlocal d =>
        mr_eval h mr loc_d = Some (Dlocal d)
      end.
  Proof.
    intros H_is_id_mr loc_d H_well_localized.
    unfold is_id_scalar_mr in H_is_id_mr.
    destruct mr; simpl in *.
    destruct mr_reduce; simpl in *; try congruence;
    try solve [ destruct r; simpl in *; congruence ].
    unfold mr_eval; simpl.
    destruct loc_d; simpl.
    - Case "loc_d is scalar"%string.
      rewrite (id_scalar_map_correct _ _ H_is_id_mr).
      simpl.
      reflexivity.
    - Case "loc_d is distributed"%string.
      destruct mr_map;
        simpl in *;
        try contradiction; try congruence.
  Qed.

  (* Kind-of flatten M/R *)

  Definition is_kindofflatten_mr mr :=
      is_id_dist_map mr.(mr_map) && is_flatten_collect mr.(mr_reduce).

  Lemma is_kindofflatten_mr_correct (mr:mr) (loc_d: ddata) :
    is_kindofflatten_mr mr = true ->
    map_well_localized mr.(mr_map) loc_d ->
    match loc_d with
    | Ddistr coll =>
      mr_eval h mr loc_d = lift (fun l => Dlocal (dcoll l)) (oflatten coll)
    | Dlocal d =>
      mr_eval h mr loc_d = lift (fun l => Dlocal (dcoll l)) (oflatten (d::nil))
    end.
  Proof.
    intros Hmr Hwell_localized.
    unfold is_kindofflatten_mr in Hmr.
    rewrite Bool.andb_true_iff in Hmr.
    destruct Hmr.
    unfold is_flatten_collect in H0.
    destruct mr; simpl in *.
    destruct mr_reduce; simpl in *; try congruence;
    try solve [ destruct r; simpl in *; congruence ].
    unfold mr_eval; simpl.
    destruct loc_d.
    - Case "loc_d is scalar"%string.
      destruct mr_map;
        simpl in *;
        try contradiction; try congruence.
    - Case "loc_d is distributed"%string.
      rewrite (id_dist_map_correct _ _ H).
      destruct p; try congruence; simpl in *.
      destruct n; try congruence; simpl in *.
      + destruct u; try congruence; simpl in *.
        destruct n; try congruence; simpl in *.
        unfold equiv_decb in *.
        repeat dest_eqdec; try congruence.
        simpl.
        destruct (oflatten l); reflexivity.
      + destruct n1; try congruence; simpl in *.
        destruct u; try congruence; simpl in *.
        destruct n1; try congruence; simpl in *.
        destruct n2; try congruence; simpl in *.
        rewrite Bool.andb_true_iff in H0.
        destruct H0.
        unfold equiv_decb in *.
        repeat dest_eqdec; try congruence.
        simpl.
        destruct (oflatten l); reflexivity.
  Qed.

  (* Collect M/R *)

  Definition is_collect_mr mr :=
    is_id_dist_map mr.(mr_map) && is_id_collect mr.(mr_reduce).

  Lemma mr_collect_collects (mr:mr) (loc_d:ddata) :
    is_collect_mr mr = true ->
    map_well_localized mr.(mr_map) loc_d ->
    match loc_d with
    | Ddistr coll =>
      mr_eval h mr loc_d = Some (Dlocal (dcoll coll))
    | Dlocal d =>
      mr_eval h mr loc_d = Some (Dlocal (dcoll (d::nil)))
    end.
  Proof.
    intros Hmr Hwell_localized.
    unfold is_collect_mr in Hmr.
    rewrite Bool.andb_true_iff in Hmr.
    destruct Hmr.
    destruct mr; simpl in *.
    destruct mr_reduce; simpl in *; try congruence;
    try solve [ destruct r; simpl in *; congruence ].
    unfold mr_eval; simpl.
    destruct loc_d.
    (* - Case "loc_d is scalar"%string. *)
    (*   rewrite Hmap; simpl. *)
    (*   destruct p; simpl in *. *)
    (*   destruct n; simpl in *; try congruence. *)
    (*   * unfold equiv_decb in *. *)
    (*     repeat dest_eqdec; try congruence. *)
    (*     reflexivity. *)
    (*   * destruct u; simpl in *; try congruence. *)
    (*     destruct n; simpl in *; try congruence. *)
    (*     unfold equiv_decb in *. *)
    (*     repeat dest_eqdec; try congruence. *)
    (*     reflexivity. *)
    - Case "loc_d is scalar"%string.
      destruct mr_map;
        simpl in *;
        try contradiction; try congruence.
    - Case "loc_d is distributed"%string.
      rewrite (id_dist_map_correct _ _ H).
      destruct p; simpl in *; try congruence.
      destruct n; simpl in *; try congruence.
      * unfold equiv_decb in *.
        repeat dest_eqdec; try congruence.
        reflexivity.
      * destruct u; simpl in *; try congruence.
        destruct n; simpl in *; try congruence.
        unfold equiv_decb in *.
        repeat dest_eqdec; try congruence.
        reflexivity.
  Qed.

  (* Dispatch M/R *)

  Definition is_dispatch_mr mr :=
    match mr.(mr_reduce) with
    | RedId =>
      is_dispatch_map mr.(mr_map)
    | RedCollect reduce => false
    | RedOp _ => false
    | RedSingleton => false
    end.

  Lemma mr_dispatch_correct (mr:mr) (coll:list data) :
    is_dispatch_mr mr = true ->
    mr_eval h mr (Dlocal (dcoll coll)) = Some (Ddistr coll).
  Proof.
    intros.
    unfold is_dispatch_mr in H.
    destruct mr; simpl in *.
    destruct mr_reduce; simpl in *; try congruence.
    unfold is_dispatch_map in H.
    unfold mr_eval; simpl.
    rewrite dispatch_map_correct; [|assumption].
    unfold mr_reduce_eval; simpl.
    destruct (oflatten coll); reflexivity.
  Qed.

  (***************
   * M/R rewrite *
   ***************)

  (* Java equivalent: MROptimizer.map_collect_flatten_to_map_flatten_collect *)
  Definition map_collect_flatten_to_map_flatten_collect mr :=
    match mr.(mr_map) with
    | MapDist f =>
      if is_flatten_collect mr.(mr_reduce) then
        let mr' :=
            mkMR
              mr.(mr_input)
              mr.(mr_output)
              (MapDistFlatten f)
              (RedCollect id_function)
        in
        Some (mr'::nil)
      else
        None
    | _ => None
    end.

  Lemma map_collect_flatten_to_map_flatten_collect_correct mr:
    forall mr_chain,
      map_collect_flatten_to_map_flatten_collect mr = Some mr_chain ->
      forall env,
      mr_chain_eval h env (mr::nil) = mr_chain_eval h env mr_chain.
  Proof.
    intros mr_chain Hmr_chain env.
    unfold map_collect_flatten_to_map_flatten_collect in Hmr_chain.
    destruct mr; simpl in *.
    destruct mr_map; simpl in *; try congruence.
    destruct mr_chain;
    case_eq (is_flatten_collect mr_reduce);
      intros Heq; rewrite Heq in *;
      try congruence.
    destruct mr_reduce; simpl in *; try congruence;
    try solve [ destruct r; congruence ].
    inversion Hmr_chain.
    unfold mr_chain_eval; simpl.
    destruct (lookup equiv_dec env mr_input); simpl; try congruence.
    destruct p0; simpl in *; try congruence.
    destruct n; simpl in *; try congruence.
    - destruct u; simpl in *; try congruence.
      destruct n; simpl in *; try congruence.
      destruct d; try reflexivity.
      unfold mr_eval; simpl.
      unfold mr_reduce_eval; simpl.
      unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
      destruct
        (lift_map
           (fun d0 : data =>
              let (doc, body) := p in nnrc_core_eval h empty_cenv ((doc, d0) :: nil) body) l);
        simpl; try reflexivity.
      destruct (oflatten l0);
        simpl; try reflexivity.
    - destruct n1; simpl in *; try congruence.
      destruct u; simpl in *; try congruence.
      destruct n1; simpl in *; try congruence.
      destruct n2; simpl in *; try congruence.
      unfold mr_eval; simpl.
      destruct d; try reflexivity.
      rewrite Bool.andb_true_iff in Heq.
      destruct Heq.
      destruct
        (lift_map
           (fun d : data =>
              let (doc, body) := p in nnrc_core_eval h empty_cenv ((doc, d) :: nil) body) l);
        simpl; try reflexivity.
      destruct (@equiv_dec string (@eq string) (@eq_equivalence string) string_eqdec v1 v);
      [ | unfold equiv_decb in *;
          repeat dest_eqdec; try congruence ].
      destruct (@equiv_dec string (@eq string) (@eq_equivalence string) string_eqdec v2 v0);
      [ | unfold equiv_decb in *;
          repeat dest_eqdec; try congruence ].
      simpl.
      destruct (oflatten l0);
        simpl; try reflexivity.
  Qed.

  (**************
   * M/R Merges *
   **************)

  (* Some (temporary) notion of equivalence for M/R (pairs) chains *)
    
  Definition merge_correct (mf:mr -> mr -> option mr) (m1 m2: mr) :=
    forall (m3:mr),
      m1.(mr_output) <> m1.(mr_input) ->
      m2.(mr_output) <> m2.(mr_input) ->
      m2.(mr_output) <> m1.(mr_input) ->
      mf m1 m2 = Some m3 ->
      forall (loc_d: ddata),
        map_well_localized m1.(mr_map) loc_d ->
        get_mr_chain_result
          (mr_chain_eval h ((m1.(mr_input),loc_d)::nil) (m1::m2::nil)) =
        get_mr_chain_result
          (mr_chain_eval h ((m1.(mr_input),loc_d)::nil) (m3::nil)).

  Definition merge_correct_weak (mf:mr -> mr -> option mr) :=
    forall (m1 m2 m3:mr),
      m1.(mr_output) <> m1.(mr_input) ->
      m2.(mr_output) <> m2.(mr_input) ->
      m2.(mr_output) <> m1.(mr_input) ->
      mf m1 m2 = Some m3 ->
      forall (loc_d: ddata),
        forall (result: data),
          map_well_localized m1.(mr_map) loc_d ->
          get_mr_chain_result
            (mr_chain_eval h ((m1.(mr_input),loc_d)::nil) (m1::m2::nil)) = Some result ->
          get_mr_chain_result
            (mr_chain_eval h ((m1.(mr_input),loc_d)::nil) (m3::nil)) = Some result.

  (* Collect+Dispatch=Id *)

  (* Java equivalent: MROptimizer.merge_collect_dispatch *)
  Definition merge_collect_dispatch mr1 mr2 :=
    if (equiv_decb mr1.(mr_output) mr2.(mr_input))
         && is_id_collect mr1.(mr_reduce)
         && is_dispatch_map mr2.(mr_map) then
      let mr :=
          mkMR
            mr1.(mr_input)
            mr2.(mr_output)
            mr1.(mr_map)
            mr2.(mr_reduce)
      in
      Some mr
    else
      None.

  Lemma merge_collect_dispatch_correct mr1 mr2:
    merge_correct merge_collect_dispatch mr1 mr2.
  Proof.
    unfold merge_correct.
    intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge loc_d Hwell_localized.
    unfold merge_collect_dispatch in Hmerge.
    case_eq ((mr_output mr1 ==b mr_input mr2) &&
             is_id_collect (mr_reduce mr1) && is_dispatch_map (mr_map mr2)); intros Heq;
    rewrite Heq in *; simpl in *; [|congruence].
    inversion Hmerge; clear Hmerge; subst.
    rewrite Bool.andb_true_iff in Heq.
    rewrite Bool.andb_true_iff in Heq.
    destruct Heq.
    destruct H.
    unfold mr_chain_eval; simpl.
    unfold olift.
    unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
    unfold mr_eval; simpl.
    case_eq ((mr_map_eval h (mr_map mr1) loc_d)); simpl; try congruence.
    intros coll Hmap1.
    rewrite (id_collect_correct _ _ H1).
    simpl.
    repeat dest_eqdec; try congruence; simpl.
    case_eq (equiv_dec (mr_input mr2) (mr_output mr1)); try congruence.
    intros.
    rewrite (dispatch_map_correct _ _ H0).
    simpl.
    destruct (mr_reduce_eval h (mr_reduce mr2) coll); try reflexivity.
    rewrite e1 in *.
    unfold merge_env.
    destruct d;
    simpl;
    unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl;
    reflexivity.
  Qed.



  (* Id+M=M *)

  (* Java equivalent: MROptimizer.merge_mr_id_dist_l *)
  Definition merge_mr_id_dist_l mr1 mr2 :=
    if equiv_decb mr1.(mr_output) mr2.(mr_input) && is_id_dist_mr mr1 then
      let mr :=
          mkMR
            mr1.(mr_input)
            mr2.(mr_output)
            mr2.(mr_map)
            mr2.(mr_reduce)
      in
      Some mr
    else
      None.

  Lemma merge_mr_id_dist_l_correct mr1 mr2:
    merge_correct merge_mr_id_dist_l mr1 mr2.
  Proof.
    unfold merge_correct.
    intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge_mr loc_d Hwell_localized.
    unfold merge_mr_id_dist_l in Hmerge_mr.
    case_eq (equiv_decb (mr_output mr1) (mr_input mr2) && is_id_dist_mr mr1); intros Heq;
    rewrite Heq in *; simpl in *; [|congruence].
    rewrite Bool.andb_true_iff in Heq.
    destruct Heq as (Hmr1_mr2, Hmr1_is_id).
    inversion Hmerge_mr; clear Hmerge_mr H0.
    unfold mr_chain_eval; simpl.
    destruct (equiv_dec (mr_input mr1) (mr_input mr1)); try congruence.
    generalize (is_id_dist_mr_correct mr1 Hmr1_is_id loc_d Hwell_localized).
    intros Hmr1.
    unfold is_id_dist_mr in Hmr1_is_id.
    destruct mr1.
    destruct mr_reduce; simpl in *; try congruence;
    try solve [ destruct r; simpl in *; congruence ].
    destruct loc_d.
    - Case "loc_d is scalar"%string.
      destruct mr_map;
        simpl in *;
        try contradiction; try congruence.
    - Case "loc_d is distributed"%string.
      rewrite Hmr1.
      unfold merge_env; simpl.
      unfold equiv_decb in *;
        repeat dest_eqdec; try congruence; simpl.
      repeat dest_eqdec; try congruence; simpl.
      unfold mr_eval; simpl.
      generalize (olift (mr_reduce_eval h (mr_reduce mr2))
                        (mr_map_eval h (NNRCMR.mr_map mr2) (Ddistr l))).
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity.
  Qed.

  (* Java equivalent: MROptimizer.merge_mr_id_scalar_l *)
  Definition merge_mr_id_scalar_l mr1 mr2 :=
    if equiv_decb mr1.(mr_output) mr2.(mr_input) && is_id_scalar_mr mr1 then
      let mr :=
          mkMR
            mr1.(mr_input)
            mr2.(mr_output)
            mr2.(mr_map)
            mr2.(mr_reduce)
      in
      Some mr
    else
      None.

  Lemma merge_mr_id_scalar_l_correct mr1 mr2:
    merge_correct merge_mr_id_scalar_l mr1 mr2.
  Proof.
    unfold merge_correct.
    intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge_mr loc_d Hwell_localized.
    unfold merge_mr_id_scalar_l in Hmerge_mr.
    case_eq (equiv_decb (mr_output mr1) (mr_input mr2) && is_id_scalar_mr mr1); intros Heq;
    rewrite Heq in *; simpl in *; [|congruence].
    rewrite Bool.andb_true_iff in Heq.
    destruct Heq as (Hmr1_mr2, Hmr1_is_id).
    inversion Hmerge_mr; clear Hmerge_mr H0.
    unfold mr_chain_eval; simpl.
    destruct (equiv_dec (mr_input mr1) (mr_input mr1)); try congruence.
    generalize (is_id_scalar_mr_correct mr1 Hmr1_is_id loc_d Hwell_localized).
    intros Hmr1.
    unfold is_id_scalar_mr in Hmr1_is_id.
    destruct mr1.
    destruct mr_reduce; simpl in *; try congruence;
    try solve [ destruct r; simpl in *; congruence ].
    destruct loc_d.
    - Case "loc_d is scalar"%string.
      rewrite Hmr1.
      unfold merge_env; simpl.
      unfold equiv_decb in *;
        repeat dest_eqdec; try congruence; simpl.
      repeat dest_eqdec; try congruence; simpl.
      unfold mr_eval; simpl.
      generalize (olift (mr_reduce_eval h (mr_reduce mr2))
                        (mr_map_eval h (NNRCMR.mr_map mr2) (Dlocal d))).
      destruct o; try reflexivity; simpl.
      destruct d0; try reflexivity.
    - Case "loc_d is distributed"%string.
      destruct mr_map;
        simpl in *;
        try contradiction; try congruence.
  Qed.


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX TODO XXXXXXXXXXXXXXXXXXXXXX *)

  (* (* KindOfId+M=M *) *)

  (* Definition merge_mr_kindofid mr1 mr2 := *)
  (*   if equiv_decb mr1.(mr_output) mr2.(mr_input) && is_kindofid_mr mr1 then *)
  (*     let mr := *)
  (*         mkMR *)
  (*             mr1.(mr_input) *)
  (*             mr2.(mr_output) *)
  (*             mr2.(mr_flat_map) *)
  (*             mr2.(mr_reduce) *)
  (*     in *)
  (*     Some mr *)
  (*   else *)
  (*     None. *)

  (* Lemma merge_mr_kindofid_correct : *)
  (*   merge_correct_singleton merge_mr_kindofid. *)
  (* Proof. *)
  (*   unfold merge_correct_singleton. intros m1 m2 m3. *)
  (*   intros Hdist1 Hdist2. intros. *)
  (*   unfold merge_mr_kindofid in H0. *)
  (*   unfold equiv_decb in *. *)
  (*   dest_eqdec; simpl in *. *)
  (*   - case_eq (is_kindofid_mr m1); intros; *)
  (*     rewrite H1 in H0; try congruence. *)
  (*     unfold mr_chain_eval. *)
  (*     simpl. *)
  (*     dest_eqdec; [ | congruence ]. *)
  (*     a.dmit. *)
  (*   - discriminate.  *)
  (* Qed. *)

  (* map-id + id-red = map-red *)

  (* Java equivalent: MROptimizer.merge_id_reduce_id_dist_map *)  
  Definition merge_id_reduce_id_dist_map mr1 mr2 :=
    if equiv_decb mr1.(mr_output) mr2.(mr_input)
       && is_id_reduce mr1.(mr_reduce)
       && is_id_dist_map mr2.(mr_map) then
      let mr :=
          mkMR
            mr1.(mr_input)
            mr2.(mr_output)
            mr1.(mr_map)
            mr2.(mr_reduce)
      in
      Some mr
    else
      None.

  Lemma merge_id_reduce_id_dist_map_correct mr1 mr2:
    merge_correct merge_id_reduce_id_dist_map mr1 mr2.
  Proof.
    unfold merge_correct.
    intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge_mr loc_d Hwell_localized.
    unfold merge_id_reduce_id_dist_map in Hmerge_mr.
    case_eq (equiv_decb (mr_output mr1) (mr_input mr2) &&
                        is_id_reduce (mr_reduce mr1) && is_id_dist_map (mr_map mr2)); intros Heq;
    rewrite Heq in *; simpl in *; [|congruence].
    repeat rewrite Bool.andb_true_iff in Heq.
    destruct Heq as (Htmp, Hmr2_map_is_id).
    destruct Htmp as (Hmr1_mr2, Hmr1_red_is_id).
    inversion Hmerge_mr; clear Hmerge_mr H0.
    unfold mr_chain_eval; simpl.
    destruct (equiv_dec (mr_input mr1) (mr_input mr1)); simpl; try congruence.
    unfold mr_eval; simpl.
    destruct ((mr_map_eval h (mr_map mr1) loc_d)); simpl; try congruence.
    rewrite (id_reduce_correct _ _ Hmr1_red_is_id).
    simpl.
    unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
    repeat dest_eqdec; try congruence; simpl.
    rewrite (id_dist_map_correct _ _ Hmr2_map_is_id).
    simpl.
    destruct (mr_reduce_eval h (mr_reduce mr2) l); simpl; try congruence.
    unfold merge_env; simpl.
    repeat dest_eqdec; try congruence; simpl.
    destruct d; simpl; try congruence.
  Qed.

  (* map-singleton + id-red = map-red *)

  (* Java equivalent: MROptimizer.merge_singleton_reduce_id_scalar_map *)  
  Definition merge_singleton_reduce_id_scalar_map mr1 mr2 :=
    if equiv_decb mr1.(mr_output) mr2.(mr_input)
       && is_singleton_reduce mr1.(mr_reduce)
       && is_id_scalar_map mr2.(mr_map) then
      let mr :=
          mkMR
            mr1.(mr_input)
            mr2.(mr_output)
            mr1.(mr_map)
            mr2.(mr_reduce)
      in
      Some mr
    else
      None.

  Lemma merge_singleton_reduce_id_scalar_map_correct mr1 mr2:
    (forall loc_d, exists d, mr_map_eval h mr1.(mr_map) loc_d = Some (d::nil)) ->
    merge_correct merge_singleton_reduce_id_scalar_map mr1 mr2.
  Proof.
    intros Hmap1.
    unfold merge_correct.
    intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge_mr loc_d Hwell_localized.
    unfold merge_singleton_reduce_id_scalar_map in Hmerge_mr.
    case_eq (equiv_decb (mr_output mr1) (mr_input mr2) &&
                        is_singleton_reduce (mr_reduce mr1) &&
                        is_id_scalar_map (mr_map mr2)); intros Heq;
    rewrite Heq in *; simpl in *; [|congruence].
    repeat rewrite Bool.andb_true_iff in Heq.
    destruct Heq as (Htmp, Hmr2_map_is_id).
    destruct Htmp as (Hm1_m2, Hmr1_red_is_single).
    inversion Hmerge_mr; clear Hmerge_mr H0.
    unfold mr_chain_eval; simpl.
    destruct (equiv_dec (mr_input mr1) (mr_input mr1)); simpl; try congruence.
    unfold mr_eval; simpl.
    specialize (Hmap1 loc_d).
    destruct Hmap1.
    rewrite H.
    simpl.
    rewrite (singleton_reduce_correct _ _ Hmr1_red_is_single).
    simpl.
    unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
    repeat dest_eqdec; try congruence; simpl.
    rewrite (id_scalar_map_correct _ _ Hmr2_map_is_id).
    simpl.
    destruct (mr_reduce_eval h (mr_reduce mr2) (x :: nil)); simpl; try congruence.
    unfold merge_env; simpl.
    repeat dest_eqdec; try congruence; simpl.
    destruct d; simpl; try congruence.
  Qed.

  (* MapDist(m)-RedId + flatten-red = MapDistFlatten(m)-red *)

  (* Java equivalent: MROptimizer.merge_reduce_id_flatten_map *)
  Definition merge_reduce_id_flatten_map (mr1 mr2:mr) :=
    match mr1.(mr_map) with
    | MapDist map1 =>
      if equiv_decb mr1.(mr_output) mr2.(mr_input)
          && is_id_reduce mr1.(mr_reduce)
          && is_flatten_dist_map mr2.(mr_map) then
       let mr :=
           mkMR
             mr1.(mr_input)
             mr2.(mr_output)
             (MapDistFlatten map1)
             mr2.(mr_reduce)
       in
       Some mr
      else
        None
    | _ => None
    end.

  Lemma merge_reduce_id_flatten_map_correct mr1 mr2:
    merge_correct merge_reduce_id_flatten_map mr1 mr2.
  Proof.
    unfold merge_correct.
    intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge_mr loc_d Hwell_localized.
    unfold merge_reduce_id_flatten_map in Hmerge_mr.
    unfold mr_chain_eval; simpl.
    destruct (equiv_dec (mr_input mr1) (mr_input mr1)); simpl; try congruence.
    unfold mr_eval; simpl.
    destruct (mr_map mr1); try congruence.
    case_eq (equiv_decb (mr_output mr1) (mr_input mr2) &&
                        is_id_reduce (mr_reduce mr1) &&
                        is_flatten_dist_map (mr_map mr2)); intros Heq;
    rewrite Heq in *; simpl in *; [|congruence].
    repeat rewrite Bool.andb_true_iff in Heq.
    destruct Heq as (Htmp, Hmr2_map_is_flatten).
    destruct Htmp as (Hmr1_mr2, Hmr1_red_is_id).
    inversion Hmerge_mr; clear Hmerge_mr H0.
    simpl.
    destruct loc_d; simpl in *; try contradiction.
    dest_eqdec; try congruence; simpl.
    destruct (lift_map
                 (fun d : data =>
                  let (doc, body) := p in nnrc_core_eval h empty_cenv ((doc, d) :: nil) body)
                 l);
      simpl in *; try congruence.
    rewrite (id_reduce_correct _ _ Hmr1_red_is_id).
    simpl.
    unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
    repeat dest_eqdec; try congruence; simpl.
    rewrite (flatten_dist_map_correct _ _ Hmr2_map_is_flatten).
    simpl.
    destruct (olift (mr_reduce_eval h (mr_reduce mr2)) (oflatten l0));
      simpl; try congruence.
    unfold merge_env; simpl.
    repeat dest_eqdec; try congruence; simpl.
    destruct d; simpl; try congruence.
  Qed.


  (* scalar-singleton + scalar-red = scalar-scalar-red *)

  (* Java equivalent: MROptimizer.merge_scalar_singleton_scalar *)
  Definition merge_scalar_singleton_scalar (mr1 mr2: mr) :=
    if equiv_decb mr1.(mr_output) mr2.(mr_input)
       && is_singleton_reduce mr1.(mr_reduce) then
      match mr1.(mr_map), mr2.(mr_map) with
      | MapScalar (x1, NNRCUnop OpBag n1), MapScalar (x2, n2) =>
        let map :=
            MapScalar (x1, NNRCLet x2 n1 n2)
        in
        let mr :=
            mkMR
              mr1.(mr_input)
              mr2.(mr_output)
              map
              mr2.(mr_reduce)
        in
        Some mr
      | _, _ => None
      end
    else
      None.

  Lemma merge_scalar_singleton_scalar_correct mr1 mr2:
    mr_well_formed mr2 ->
    merge_correct merge_scalar_singleton_scalar mr1 mr2.
  Proof.
    intros Hmr2_wf.
    unfold mr_well_formed in Hmr2_wf.
    destruct Hmr2_wf as [ Hmr2_map_wf Hmr2_red_wf ].
    clear Hmr2_red_wf.
    unfold merge_correct.
    intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge_mr loc_d Hwell_localized.
    unfold merge_scalar_singleton_scalar in Hmerge_mr.
    unfold mr_chain_eval; simpl.
    destruct (equiv_dec (mr_input mr1) (mr_input mr1)); simpl; try congruence.
    unfold mr_eval; simpl.
    case_eq (equiv_decb (mr_output mr1) (mr_input mr2) &&
                        is_singleton_reduce (mr_reduce mr1)); intros Heq;
    rewrite Heq in *; simpl in *; [|congruence].
    repeat rewrite Bool.andb_true_iff in Heq.
    destruct Heq as (Hmr1_mr2, Hmr1_red_is_singleton).
    inversion Hmerge_mr; clear Hmerge_mr.
    destruct (mr_map mr1); try congruence.
    destruct p; try congruence.
    destruct n; try congruence.
    destruct u; try congruence.
    destruct (mr_map mr2); try congruence.
    destruct p; try congruence.
    inversion H0; clear H0.
    simpl in *.
    destruct loc_d; simpl in *; try contradiction.
    dest_eqdec; try congruence; simpl.
    destruct (nnrc_core_eval h empty_cenv ((v, d) :: nil) n); simpl; try congruence.
    rewrite (singleton_reduce_correct _ _ Hmr1_red_is_singleton).
    simpl.
    repeat dest_eqdec; try congruence; simpl.
    unfold equiv_decb in *;
      repeat dest_eqdec; try congruence; simpl.
    assert (nnrc_core_eval h empty_cenv ((v0, d0) :: nil) n0 =
            nnrc_core_eval h empty_cenv ((v0, d0) :: (v, d) :: nil) n0) as Heq;
      [ | rewrite Heq; clear Heq ].
    - apply nnrc_core_eval_equiv_free_in_env.
      intros x Hx.
      assert (x = v0) as Heq;
        [ | rewrite Heq; clear Heq;
            simpl;
            repeat dest_eqdec; try congruence ].
      unfold function_with_no_free_vars in *.
      simpl in *.
      apply Hmr2_map_wf.
      assumption.
    - destruct (nnrc_core_eval h empty_cenv ((v0, d0) :: (v, d) :: nil) n0); simpl; try congruence.
      destruct (olift (mr_reduce_eval h (mr_reduce mr2))); simpl; try congruence.
      unfold merge_env; simpl.
      repeat dest_eqdec; try congruence; simpl.
      destruct d2; simpl; try congruence.
  Qed.

  (* *)

  (* Definition merge_collect_coll_uncoll mr1 mr2 := *)
  (*   if (equiv_decb mr1.(mr_output) mr2.(mr_input)) *)
  (*        && is_id_collect mr1.(mr_reduce) *)
  (*        && is_id_scalar_map mr2.(mr_map) *)
  (*        && is_uncoll_collect mr2.(mr_reduce) then *)
  (*     match suppress_uncoll_in_collect_reduce mr2.(mr_reduce) with *)
  (*     | Some reduce => *)
  (*       let mr := *)
  (*           mkMR *)
  (*             mr1.(mr_input) *)
  (*             mr2.(mr_output) *)
  (*             mr1.(mr_map) *)
  (*             reduce *)
  (*       in *)
  (*       Some mr *)
  (*     | None => None *)
  (*     end *)
  (*   else *)
  (*     None. *)

  (* Lemma merge_collect_coll_uncoll_correct mr1 mr2: *)
  (*   merge_correct merge_collect_coll_uncoll mr1 mr2. *)
  (* Proof. *)
  (*   unfold merge_correct. *)
  (*   intros mr3 Hcycle1 Hcycle2 Hcycle3 Hmerge_mr loc_d Hwell_localized. *)
  (*   unfold merge_collect_coll_uncoll in Hmerge_mr. *)
  (*   case_eq (equiv_decb (mr_output mr1) (mr_input mr2) && *)
  (*                       is_id_collect (mr_reduce mr1) && *)
  (*                       is_id_scalar_map (mr_map mr2) && *)
  (*                       is_uncoll_collect (mr_reduce mr2)); intros Heq; *)
  (*   rewrite Heq in *; simpl in *; [|congruence]. *)
  (*   rewrite Bool.andb_true_iff in Heq. *)
  (*   destruct Heq as (H, Hmr2_red). *)
  (*   rewrite Bool.andb_true_iff in H. *)
  (*   destruct H as (H, Hmr2_map). *)
  (*   rewrite Bool.andb_true_iff in H. *)
  (*   destruct H as (Hoi, Hmr1_red). *)
  (*   destruct (mr_reduce mr2); simpl in *; try congruence; *)
  (*   try solve [ destruct r; simpl in *; congruence ]. *)
  (*   rewrite Hmr2_red in *; simpl in *. *)
  (*   destruct p; simpl in *; try congruence. *)
  (*   destruct n; simpl in *; try congruence. *)
  (*   destruct n1; simpl in *; try congruence. *)
  (*   destruct n1_1; simpl in *; try congruence. *)
  (*   destruct u; simpl in *; try congruence. *)
  (*   destruct n1_2; simpl in *; try congruence; *)
  (*   destruct n1_1; simpl in *; try congruence. *)
  (*   destruct n1_3; simpl in *; try congruence. *)
  (*   destruct d; simpl in *; try congruence. *)
  (*   inversion Hmerge_mr. *)

  (*   unfold mr_chain_eval; simpl. *)
  (*   destruct (equiv_dec (mr_input mr1) (mr_input mr1)); try congruence. *)
  (*   unfold mr_eval; simpl. *)
  (*   destruct ((mr_map_eval h (mr_map mr1) loc_d)); simpl in *; try congruence. *)
  (*   clear e. *)
  (*   rewrite (id_collect_correct _ _ Hmr1_red). *)
  (*   simpl. *)
  (*   repeat rewrite Bool.andb_true_iff in Hmr2_red. *)
  (*   destruct Hmr2_red. *)
  (*   destruct H. *)
  (*   unfold equiv_decb in *; *)
  (*     repeat dest_eqdec; try congruence; simpl; *)
  (*     repeat dest_eqdec; try congruence; simpl. *)
  (*   rewrite (id_scalar_map_correct _ _ Hmr2_map). *)
  (*   simpl. *)
  (*   (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX TODO XXXXXXXXX *) *)
  (* Qed. *)


  (* (* *) *)
  
  (* Definition merge_id_reduce_flatten_map mr1 mr2 := *)
  (*   match mr1.(mr_reduce) with *)
  (*   | RedCollect reduce1 => *)
  (*     if (equiv_decb mr1.(mr_output) mr2.(mr_input)) *)
  (*          && is_kindofid_reduce reduce1 *)
  (*          && is_id_flat_map mr2.(mr_flat_map) then *)
  (*       let map := *)
  (*           match mr1.(mr_flat_map) with *)
  (*           | (x, NNRCUnop OpBag n) => (x, n) *)
  (*           | (x, n) => (x, NNRCUnop OpFlatten n) *)
  (*           end *)
  (*       in *)
  (*       let mr := *)
  (*           mkMR *)
  (*             mr1.(mr_input) *)
  (*             mr2.(mr_output) *)
  (*             map *)
  (*             mr2.(mr_reduce) *)
  (*       in *)
  (*       Some mr *)
  (*     else *)
  (*       if (equiv_decb mr1.(mr_output) mr2.(mr_input)) *)
  (*            && is_kindofid_reduce reduce1 *)
  (*            && is_id_flat_map mr1.(mr_flat_map) then *)
  (*         let mr := *)
  (*             mkMR *)
  (*               mr1.(mr_input) *)
  (*               mr2.(mr_output) *)
  (*               mr2.(mr_flat_map) *)
  (*               mr2.(mr_reduce) *)
  (*         in *)
  (*         Some mr *)
  (*       else *)
  (*         None *)
  (*   | RedId => None *)
  (*   | RedAggregate _ => None *)
  (*   end. *)

  (* (* *) *)
  
  (* Definition merge_no_reduce mr1 mr2 := *)
  (*   match mr1.(mr_reduce) with *)
  (*   | RedId => *)
  (*     if (equiv_decb mr1.(mr_output) mr2.(mr_input)) then *)
  (*       let map := *)
  (*           let (x1, n1) := mr1.(mr_flat_map) in *)
  (*           let (x2, n2) := mr2.(mr_flat_map) in *)
  (*           (x1, NNRCUnop OpFlatten (NNRCFor x2 n1 n2)) *)
  (*       in *)
  (*       let mr := *)
  (*           mkMR *)
  (*             mr1.(mr_input) *)
  (*             mr2.(mr_output) *)
  (*             map *)
  (*             mr2.(mr_reduce) *)
  (*       in *)
  (*       Some mr *)
  (*     else *)
  (*       None *)
  (*   | RedCollect _ => None *)
  (*   | RedAggregate _ => None *)
  (*   end. *)

  (********************
   * Last expression  *
   ********************)

  Definition merge_mr_last mr (last: ((list var * nnrc) * list (var * dlocalization)) ) :=
    let '((params, n), args) := last in
    match (params, args) with
    | (x::nil, (output, Vscalar)::nil) =>
      if equiv_decb output mr.(mr_output) && is_singleton_reduce mr.(mr_reduce) then
        match mr.(mr_map) with
        | MapScalar (x1, NNRCUnop OpBag n1) =>
          Some ((mr.(mr_input)::nil, NNRCLet x
                                            (NNRCLet x1 (NNRCVar mr.(mr_input)) n1)
                                            n),
                (mr.(mr_input), Vscalar)::nil)
        | _ => None
        end
      else
        None
    | (_, _) => None
    end.

  (* Java equivalent: MROptimizer.mergeLast *)
  Definition merge_last mrl :=
    let '(chain, output, last) :=
        List.fold_right
          (fun mr chain_output_last =>
             match chain_output_last with
             | (nil, None, last) =>
               match merge_mr_last mr last with
               | Some last' => (nil, None, last')
               | None => (mr::nil, Some (mr_output mr), last)
               end
             | (acc, output, last) => (mr::acc, output, last)
             end)
          (nil, None, mrl.(mr_last)) mrl.(mr_chain)
    in
    match output with
    | None => None
    | Some output => Some (mkMRChain mrl.(mr_inputs_loc) chain last)
    end.


  (****************************
   * Rewriting Infrastructure *
   ****************************)

  (* Java equivalent: MROptimizer.applyRewrite *)
  Definition mr_chain_apply_rewrite (rew: mr -> option (list mr)) l :=
    List.flat_map
      (fun mr =>
         match rew mr with
         | None => mr::nil
         | Some mr_chain => mr_chain
         end)
      l.

  (* Java equivalent: MROptimizer.applyRewrite *)
  Definition apply_rewrite (rew: mr -> option (list mr)) mrl :=
    mkMRChain
      mrl.(mr_inputs_loc)
      (mr_chain_apply_rewrite rew mrl.(mr_chain))
      mrl.(mr_last).

  (* Java equivalent: MROptimizer.applyMerge *)
  Definition mr_chain_apply_merge (merge: mr -> mr -> option mr) l :=
    let output_vars : list var := List.fold_left (fun acc mr => mr.(mr_output) :: acc) l nil in
    List.fold_right
      (fun mr1 acc =>
         if leb (mult output_vars mr1.(mr_output)) 1 then  (* we do merge mr that have several inputs *)
           let l_optimized :=
               List.fold_right
                 (fun mr2 acc =>
                    match merge mr1 mr2 with
                    | None => mr2 :: acc
                    | Some mr12 => mr12 :: acc
                    end)
                 nil acc
           in
           mr1 :: l_optimized
         else
           mr1 :: acc)
      nil l.

  (* Java equivalent: MROptimizer.applyMerge *)
  Definition apply_merge (merge: mr -> mr -> option mr) mrl :=
    mkMRChain
      mrl.(mr_inputs_loc)
      (mr_chain_apply_merge merge mrl.(mr_chain))
      mrl.(mr_last).

  (* Java equivalent: MROptimizer.mr_chain_cleanup *)
  Fixpoint mr_chain_cleanup l (to_keep: list var) :=
    let (to_keep', res) :=
        List.fold_right
          (fun r (acc: list var * list mr) =>
             let (to_keep, res) := acc in
             if in_dec equiv_dec r.(mr_output) to_keep then
               (r.(mr_input)::to_keep, r::res)
             else
               (to_keep, res))
          (to_keep, nil) l
    in
    res.

  (* Java equivalent: MROptimizer.mr_cleanup *)
  Definition mr_cleanup mrl to_keep :=
    mkMRChain
      mrl.(mr_inputs_loc)
      (mr_chain_cleanup mrl.(mr_chain) to_keep)
      mrl.(mr_last).

  (*****************
   * M/R Optimizer *
   *****************)
 
  (* Java equivalent: MROptimizer.mr_optimize_step *)
  Definition mr_optimize_step (l: nnrcmr): nnrcmr :=
    let to_keep := List.map fst (snd l.(mr_last)) in
    let l := apply_rewrite map_collect_flatten_to_map_flatten_collect l in
    let l := apply_merge merge_id_reduce_id_dist_map l in
    let l := mr_cleanup l to_keep in
    let l := apply_merge merge_singleton_reduce_id_scalar_map l in
    let l := mr_cleanup l to_keep in
    let l := apply_merge merge_reduce_id_flatten_map l in
    let l := mr_cleanup l to_keep in
    (* let l := apply_merge merge_collect_coll_uncoll l in *)
    (* let l := mr_cleanup l to_keep in *)
    (* let l := apply_merge merge_id_reduce_flatten_map l in *)
    (* let l := mr_cleanup l to_keep in *)
    let l := apply_merge merge_collect_dispatch l in
    let l := mr_cleanup l to_keep in
    let l := apply_merge merge_mr_id_dist_l l in
    let l := mr_cleanup l to_keep in
    let l := apply_merge merge_mr_id_scalar_l l in
    let l := mr_cleanup l to_keep in
    (* let l := apply_merge merge_no_reduce l in *)
    (* let l := mr_cleanup l to_keep in *)
    let l := apply_merge merge_scalar_singleton_scalar l in
    let l := mr_cleanup l to_keep in
    let l :=
        match merge_last l with
        | None => l
        | Some l => l
        end
    in
    l.

  (* Java equivalent: MROptimizer.mr_optimize_loop *)
  Fixpoint mr_optimize_loop n (l: nnrcmr) :=
    match n with
    | 0 => l
    | S n =>
      let l := mr_optimize_step l in
      mr_optimize_loop n l
    end.

  (* Java equivalent: MROptimizer.mr_optimize *)
  Definition mr_optimize (l: nnrcmr) :=
    mr_optimize_loop 10 l.

  (* Java equivalent: MROptimizer.fresh_mr_var *)
  Definition fresh_mr_var (prefix: string) (vars: list var) :=
    let x := fresh_var prefix vars in
    (x, x::vars).


  (* Java equivalent: MROptimizer.get_nnrcmr_vars *)
  Definition get_mr_chain_vars mr_chain :=
    List.fold_left
      (fun acc mr => mr.(mr_input) :: mr.(mr_output) :: acc)
      mr_chain nil.

  (* Java equivalent: MROptimizer.get_nnrcmr_vars *)
  Definition get_nnrcmr_vars mrl :=
    get_mr_chain_vars mrl.(mr_chain).

End NNRCMRRewrite.

