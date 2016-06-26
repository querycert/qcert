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

Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import List.
Require Import EquivDec.

Require Import Utils BasicRuntime.
Require Import LData.
Require Import NNRCRuntime NNRCMRRuntime ForeignToReduceOps.
Require Import NNRCRuntime .

Local Open Scope list_scope.

Section NNRCtoNNRCMR.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {ftoredop:foreign_to_reduce_op}.

  (* Java equivalent: NnrcToNrcmr.fresh_mr_var *)
  Definition fresh_mr_var (prefix: string) (loc: localization) (vars_loc: list (var * localization)) :=
    let x := fresh_var prefix (domain vars_loc) in
    (x, (x, loc)::vars_loc).

  (****************
   * Environment  *
   ****************)

  (* This translation suppose that the environment contains at a unit
     that is used to trigger the comparisons of NNRC expressions
     without free variables.
   *)

  (** [load_env unit_var vars env] takes the
      environment [env] used to evaluate an NNRC expression and return
      the environment to use to execute the translation of this
      expression as a map-reduce chain. [vars] is the list of
      variables that have to be stored in the map-reduce with
      their localization kind.

      This function also add to the map-reduce environment and entry
      [init] that contains the unit value.
   *)
  Definition load_init_env' (initunit: var) (vars_loc: list (var * localization)) (env: bindings) : option nrcmr_env :=
    let mr_env :=
        List.fold_left
          (fun acc (x_loc: var * localization) =>
             let (x, loc) := x_loc in
             match lookup equiv_dec env x with
             | Some d =>
               match loc with
               | Vscalar => lift (fun env' => (x, Dscalar d) :: env') acc
               | Vdistributed =>
                 match d with
                 | dcoll coll => lift (fun env' => (x, Ddistributed coll) :: env') acc
                 | _ => None
                 end
               end
             | None => None
             end)
          vars_loc
          (Some nil)
    in
    match mr_env with
    | Some env => Some ((initunit, Dscalar dunit) :: env)
    | None => None
    end.

  Definition load_init_env (initunit: var) (vars_loc: list (var * localization)) (env: bindings) : option nrcmr_env :=
    let one (x_loc: var * localization) :=
        let (x, loc) := x_loc in
        match lookup equiv_dec env x with
        | Some d =>
          match loc with
          | Vscalar => Some (x, Dscalar d)
          | Vdistrubuted =>
            match d with
            | dcoll coll => Some (x, Ddistributed coll)
            | _ => None
            end
          end
        | None => None
        end
    in
    let mr_env := rmap one vars_loc in
    match mr_env with
    | Some env => Some ((initunit, Dscalar dunit) :: env)
    | None => None
    end.

  Definition load_init_env_success initunit vars_loc nrc_env mr_env :=
    load_init_env initunit vars_loc nrc_env = Some mr_env /\
    (forall x,
       lookup equiv_dec vars_loc x = Some Vscalar ->
       lift Dscalar (lookup equiv_dec nrc_env x) = lookup equiv_dec mr_env x) /\
    (forall x,
       lookup equiv_dec vars_loc x = Some Vdistributed ->
       exists coll,
         lookup equiv_dec nrc_env x = Some (dcoll coll) /\
         lookup equiv_dec mr_env x = Some (Ddistributed coll)).

  Lemma load_env_lookup_initunit initunit vars_loc nrc_env mr_env:
    load_init_env_success initunit vars_loc nrc_env mr_env ->
    lookup equiv_dec mr_env initunit = Some (Dscalar dunit).
  Proof.
    intros Hmr_env.
    unfold load_init_env_success in Hmr_env.
    destruct Hmr_env.
    destruct H0.
    unfold load_init_env in H.
    destruct (rmap
          (fun x_loc : var * localization =>
           let (x, loc) := x_loc in
           match lookup equiv_dec nrc_env x with
           | Some d =>
               match loc with
               | Vscalar => Some (x, Dscalar d)
               | Vdistributed =>
                   match d with
                   | dunit => None
                   | dnat _ => None
                   | dbool _ => None
                   | dstring _ => None
                   | dcoll coll => Some (x, Ddistributed coll)
                   | drec _ => None
                   | dleft _ => None
                   | dright _ => None
                   | dbrand _ _ => None
                   | dforeign _ => None
                   end
               end
           | None => None
           end) vars_loc); try congruence.
    inversion H.
    simpl.
    dest_eqdec; try congruence.
  Qed.

  (*******************************************
   * Put a NNRC expression into a Map-Reduce *
   *******************************************)

  (* In the following functions, the initial NNRC expression is put in
     a map-reduce element unchanged. Additional map-reduce elements
     can be created to load free variables of the expression.

     The free variables of the NNRC expression are supposed to be
     in the environment.

     The result of the evaluation is stored in the environment into as
     a scalar.
  *)

  (* --------------------------- *
   * Case with no free variables *
   * --------------------------- *)

  (* Java equivalent: NnrcToNrcmr.mr_chain_of_nnrc_with_no_free_var *)
  Definition mr_chain_of_nnrc_with_no_free_var (n: nrc) (initunit: var) (output: var) :=
    let coll_n :=
        let var := "x"%string in
        (var, NRCUnop AColl n)
    in
    let mr :=
        mkMR
          initunit
          output
          (MapScalar coll_n)
          RedSingleton
    in
    (mr::nil).

  Definition nnrcmr_of_nnrc_with_no_free_var (n: nrc) (initunit: var) (output: var) :=
    mkMRChain
      (mr_chain_of_nnrc_with_no_free_var n initunit output)
      ((output::nil, (NRCVar output)), (output, Vscalar)::nil).

  Lemma nnrcmr_of_nnrc_with_no_free_var_wf (n: nrc) (initunit: var) (output: var):
    nrc_free_vars n = nil ->
    nrcmr_well_formed (nnrcmr_of_nnrc_with_no_free_var n initunit output).
  Proof.
    intros Hfv.
    unfold nrcmr_well_formed.
    intros mr.
    unfold nnrcmr_of_nnrc_with_no_free_var.
    simpl.
    intros Hmr.
    destruct Hmr; try contradiction.
    unfold mr_well_formed.
    split; try split; try (rewrite <- H; simpl); auto.
    unfold function_with_no_free_vars.
    simpl.
    intros x Hx.
    rewrite Hfv in Hx.
    contradiction.
  Qed.

  Lemma nnrcmr_of_nnrc_with_no_free_var_correct h mr_env n:
    forall initunit output,
    forall (Hfv: nrc_free_vars n = nil),
    forall (Hinitunit: lookup equiv_dec mr_env initunit = Some (Dscalar dunit)),
    forall (Houtput: lookup equiv_dec mr_env output = None),
      nrc_eval h nil n =
      nrcmr_eval h mr_env (nnrcmr_of_nnrc_with_no_free_var n initunit output).
  Proof.
    intros.
    unfold nnrcmr_of_nnrc_with_no_free_var.
    unfold nrcmr_eval; simpl.
    unfold mr_chain_eval; simpl.
    rewrite Hinitunit.
    unfold mr_eval; simpl.
    assert (nrc_eval h
                   (@cons (prod var data)
                      (@pair var data
                         (String
                            (Ascii.Ascii false false false true true true
                               true false) EmptyString) dunit)
                      (@nil (prod var data))) n =
            nrc_eval h (@nil (prod string data)) n) as Heq;
    [ | rewrite Heq; clear Heq ].
    - rewrite (nrc_eval_equiv_free_in_env n (("x"%string, dunit) :: nil) nil);
        [ reflexivity | ].
      intros x Hx.
      simpl.
      rewrite Hfv in *.
      contradiction.
    - destruct (nrc_eval h nil n); simpl; try reflexivity.
      rewrite Houtput; simpl.
      unfold mr_last_eval; simpl.
      case (equiv_dec output output);
        try congruence.
      simpl.
      unfold build_nrc_env.
      unfold nrc_env_build.
      unfold zip, effective_params_from_bindings; simpl.
      case (equiv_dec output output);
        try congruence.
      intros.
      simpl.
      destruct (@equiv_dec string (@eq string) (@eq_equivalence string)
         string_eqdec output output); congruence.
  Qed.


  (* ---------------------------- *
   * Case with one free variables *
   * ---------------------------- *)

  (* Java equivalent: NnrcToNrcmr.mr_chain_of_nnrc_with_one_free_var *)
  Definition mr_chain_of_nnrc_with_one_free_var (n: nrc) (x_loc: var * localization) (output:var) :=
    match x_loc with
    | (x, Vscalar) =>
      let mr :=
          mkMR
            x
            output
            (MapScalar (x, NRCUnop AColl n))
            RedSingleton
      in
      (mr::nil)
    | (x, Vdistributed) =>
      let values := x in
      let mr :=
          mkMR
            x
            output
            (MapDist id_function)
            (RedCollect (values, n))
      in
      (mr::nil)
    end.

  Definition nnrcmr_of_nnrc_with_one_free_var (n: nrc) (x_loc: var * localization) (output:var) :=
    mkMRChain
      (mr_chain_of_nnrc_with_one_free_var n x_loc output)
      ((output::nil, (NRCVar output)), (output, Vscalar)::nil).


  Lemma nnrcmr_of_nnrc_with_one_free_var_wf (n: nrc) (x_loc: var * localization) (output:var):
    function_with_no_free_vars (fst x_loc, n) ->
    nrcmr_well_formed (nnrcmr_of_nnrc_with_one_free_var n x_loc output).
  Proof.
    intros Hfv.
    unfold nrcmr_well_formed.
    intros mr.
    unfold nnrcmr_of_nnrc_with_one_free_var; simpl.
    destruct x_loc.
    destruct l; simpl;
      intros Hmr;
      destruct Hmr; try contradiction;
      subst;
      unfold mr_well_formed; simpl in *.
    - split; [ | trivial ].
      unfold function_with_no_free_vars in *; simpl in *; intros.
      intuition.
    - split.
      * apply id_function_no_free_vars.
      * unfold function_with_no_free_vars in *; simpl in *; intros.
        intuition.
  Qed.

  Lemma nnrcmr_of_nnrc_with_one_free_var_correct h nrc_env mr_env n x_loc:
    forall output initunit,
    forall (Hnrc_env: exists d, lookup equiv_dec nrc_env (fst x_loc) = Some d),
    forall (Hmr_env: load_init_env_success initunit (x_loc::nil) nrc_env mr_env),
    forall (Hfv: function_with_no_free_vars (fst x_loc, n)),
    forall (Houtput: lookup equiv_dec mr_env output = None),
      nrc_eval h nrc_env n =
      nrcmr_eval h mr_env (nnrcmr_of_nnrc_with_one_free_var n x_loc output).
  Proof.
    intros.
    unfold load_init_env_success in Hmr_env.
    destruct Hmr_env.
    destruct H0.
    unfold nnrcmr_of_nnrc_with_one_free_var.
    destruct x_loc; simpl.
    destruct l.
    - specialize (H0 v); clear H1.
      simpl in *.
      dest_eqdec; try congruence.
      assert (Some Vscalar = Some Vscalar) as Htrivial; [ reflexivity | ].
      specialize (H0 Htrivial); clear Htrivial e.
      unfold nrcmr_eval; simpl.
      unfold mr_chain_eval; simpl.
      assert (@lookup var localized_data
                      (@equiv_dec var (@eq var) (@eq_equivalence var) string_eqdec)
                      mr_env v =
              (@lift data localized_data Dscalar
                     (@lookup string data
                              (@equiv_dec string (@eq string) (@eq_equivalence string)
                                          string_eqdec) nrc_env v))) as Heq;
        [ rewrite H0; reflexivity | rewrite Heq; clear Heq ].
      destruct Hnrc_env.
      unfold lift.
      assert (@lookup string data
                      (@equiv_dec string (@eq string) (@eq_equivalence string)
                                  string_eqdec) nrc_env v =
              @Some data x) as Heq;
        [ auto | rewrite Heq; clear Heq ].
      unfold mr_eval; simpl.
      assert (nrc_eval h ((v, x) :: nil) n =
              nrc_eval h nrc_env n) as Heq;
        [ | rewrite Heq; clear Heq ].
      * apply nrc_eval_equiv_free_in_env; intros.
        simpl.
        dest_eqdec; try congruence.
        specialize (Hfv x0).
        simpl in *.
        specialize (Hfv H2).
        congruence.
      * destruct (nrc_eval h nrc_env n);
          simpl; try congruence.
        rewrite Houtput; simpl.
        unfold mr_last_eval; simpl.
        case (equiv_dec output output);
          try congruence.
        simpl.
        case (equiv_dec output output);
          try congruence.
      unfold build_nrc_env, nrc_env_build, zip, effective_params_from_bindings; simpl.
      intro; simpl; intros; simpl.
      case (equiv_dec output output);
        try congruence; intros.
      simpl.
      case (equiv_dec output output);
        try congruence; intros.
    - specialize (H1 v); clear H0.
      simpl in *.
      dest_eqdec; try congruence.
      assert (Some Vdistributed = Some Vdistributed) as Htrivial; [ reflexivity | ].
      specialize (H1 Htrivial); clear Htrivial e.
      unfold nrcmr_eval; simpl.
      unfold mr_chain_eval; simpl.
      destruct H1.
      destruct H0.
      assert (@lookup var localized_data
                      (@equiv_dec var (@eq var) (@eq_equivalence var) string_eqdec)
                      mr_env v =
              @Some localized_data (Ddistributed x)) as Heq;
        [ assumption | rewrite Heq; clear Heq].
      unfold mr_eval; simpl.
      rewrite rmap_id.
      simpl.
      assert (nrc_eval h ((v, dcoll x) :: nil) n =
              nrc_eval h nrc_env n) as Heq.
      * apply nrc_eval_equiv_free_in_env; intros.
        simpl.
        specialize (Hfv x0).
        simpl in *.
        specialize (Hfv H2).
        dest_eqdec; try congruence.
        rewrite <- H0.
        reflexivity.
      * rewrite Heq.
        destruct (nrc_eval h nrc_env n);
          simpl; try congruence.
        rewrite Houtput; simpl.
        unfold mr_last_eval; simpl.
        case (equiv_dec output output);
          try congruence.
        simpl.
        case (equiv_dec output output);
          try congruence.
        intros.
      case (equiv_dec output output);
          try congruence; intros.
      simpl.
      unfold build_nrc_env, nrc_env_build, zip, effective_params_from_bindings; simpl.
      case (equiv_dec output output);
        try congruence; intros.
      simpl.
      case (equiv_dec output output);
        congruence.
  Qed.

  (* --------------------------------- *
   * Case with multiple free variables *
   * --------------------------------- *)

  (* Java equivalent: NnrcToNrcmr.brand_of_var *)
  Definition brand_of_var (x: var) := String.append "__Env."%string (x).

  (**
    Packing the value of a free variable [fv] in a closure environment
    named [closure_env_name] is done by a map-reduce job (without reduce)
    that looks like:
        (fun d => Brand "fv" d)
   *)
  (* Java equivalent: NnrcToNrcmr.pack_closure_env *)
  Definition pack_closure_env (free_vars_loc: list (var * localization)) (closure_env_name: var) : list mr :=
    List.map
      (fun (fv_loc: var * localization) =>
         let (fv, loc) := fv_loc in
         let mr_reduce_brand :=
             RedId
         in
         match loc with
         | Vscalar =>
           let mr_map_brand :=
               let d:var := "x"%string in
               (d, NRCUnop AColl
                           (NRCUnop (ABrand (singleton (brand_of_var fv))) (NRCVar d)))
           in
           mkMR
             fv
             closure_env_name
             (MapScalar mr_map_brand)
             mr_reduce_brand
         | Vdistributed =>
           let mr_map_brand :=
               let d:var := "x"%string in
               (d, NRCUnop (ABrand (singleton (brand_of_var fv))) (NRCVar d))
           in
           mkMR
             fv
             closure_env_name
             (MapDist mr_map_brand)
             mr_reduce_brand
         end)
      free_vars_loc.

  (**
    Unpacking a distributed free variable [fv] coming from [closure_env_name]
    with the continuation [k] correspond to the following NNRC code:
        let fv =
          flatten
            { match ("fv") d with
              | Some d => { Unbrand d }
              | None => {}
              end | d in closure_env_name }
         in k

    Unpacking a scalar free variable [fv] coming from [closure_env_name]
    with the continuation [k] correspond to the following NNRC code:
        let fv =
          match singleton
            { match ("fv") d with
              | Some d => { Unbrand d }
              | None => {}
              end | d in closure_env_name }
          with
          | Some fv => fv
          | None => assert false
        in
        k
   *)
  (* Java equivalent: NnrcToNrcmr.unpack_closure_env *)
  Definition unpack_closure_env (closure_env_name: var) (free_vars_loc: list (var * localization)) (k: nrc) : nrc :=
    List.fold_right
      (fun fv_loc k =>
         match fv_loc with
         | (fv, Vdistributed) =>
           let d : var := fresh_var "unpackdistributed$" (closure_env_name :: nil) in
           NRCLet fv
                  (NRCUnop AFlatten
                           (NRCFor d (NRCVar closure_env_name)
                                   (NRCEither (NRCUnop (ACast (singleton (brand_of_var fv))) (NRCVar d))
                                              d (NRCUnop AColl (NRCUnop AUnbrand (NRCVar d)))
                                              d (NRCConst (dcoll nil)))))
                  k
         | (fv, Vscalar) =>
           let d : var := fresh_var "unpackscalar$" (closure_env_name :: nil) in
           NRCLet fv
                  (NRCEither (NRCUnop ASingleton
                                      (NRCUnop AFlatten
                                               (NRCFor d (NRCVar closure_env_name)
                                                       (NRCEither (NRCUnop (ACast (singleton (brand_of_var fv))) (NRCVar d))
                                                                  d (NRCUnop AColl (NRCUnop AUnbrand (NRCVar d)))
                                                                  d (NRCConst (dcoll nil))))))
                             fv (NRCVar fv)
                             fv (NRCConst dunit)) (* must not be executed *)
                  k
         end)
      k free_vars_loc.

  (**
    Convert an NNRC expression [n] into a Map-Reduce fetching the
    values of the free variables from the environment. The list
    [vars_loc] give the localization of each free variable of [n].
    This list must contain all the variables that are in the
    map-reduce environment (it may contain variables that are not
    free in [n]).
   *)
  (* Java equivalent: NnrcToNrcmr.mr_chain_of_nnrc_with_free_vars *)
  Definition mr_chain_of_nnrc_with_free_vars (n: nrc) (vars_loc: list (var * localization)) (output: var): list mr :=
    let free_vars := bdistinct (nrc_free_vars n) in
    match
      List.fold_right
        (fun x oacc =>
           olift
             (fun loc => lift (fun acc => (x, loc)::acc) oacc)
             (lookup equiv_dec vars_loc x))
        (Some nil) free_vars
    with
    | Some free_vars_loc =>
      let (closure_env_name, vars_loc) := fresh_mr_var "closure$" Vdistributed vars_loc in
      let pack_closure_env := pack_closure_env free_vars_loc closure_env_name in
      let final_reduce :=
          (closure_env_name, unpack_closure_env closure_env_name free_vars_loc n)
      in
      let final_mr :=
          mkMR
            closure_env_name
            output
            (MapDist id_function)
            (RedCollect final_reduce)
      in
      pack_closure_env ++ (final_mr::nil)
    | None => nil
    end.

  Definition nnrcmr_of_nnrc_with_free_vars (n: nrc) (vars_loc: list (var * localization)) (output: var): nrcmr :=
    mkMRChain
      (mr_chain_of_nnrc_with_free_vars n vars_loc output)
      ((output::nil, (NRCVar output)), (output, Vscalar)::nil).

  (* Well formation *)

  Lemma pack_closure_env_wf (free_vars_loc: list (var * localization)) (closure_env_name: var):
    mr_chain_well_formed (pack_closure_env free_vars_loc closure_env_name).
  Proof.
    induction free_vars_loc.
    - Case "free_vars_loc = nil"%string.
      simpl.
      unfold mr_chain_well_formed.
      contradiction.
    - Case "free_vars_loc <> nil"%string.
      unfold nrcmr_well_formed.
      simpl.
      intros mr Hmr.
      destruct a.
      destruct Hmr.
      subst.
      + unfold mr_well_formed.
        destruct l.
        * SCase "Scalar"%string.
          repeat split.
          simpl.
          unfold function_with_no_free_vars.
          simpl.
          intros x Hx.
          destruct Hx; [ congruence | contradiction ].
        * SCase "Distributed"%string.
          repeat split.
          simpl.
          unfold function_with_no_free_vars.
          simpl.
          intros x Hx.
          destruct Hx; [ congruence | contradiction ].
      + apply IHfree_vars_loc.
        assumption.
  Qed.

  Lemma unpack_closure_env_free_vars (closure_env_name: var) (free_vars_loc: list (var * localization)) (k: nrc) :
    forall x,
      let free_vars := List.map fst free_vars_loc in
      In x (nrc_free_vars (unpack_closure_env closure_env_name free_vars_loc k)) ->
      In x (closure_env_name :: (bminus free_vars (bdistinct (nrc_free_vars k)))).
  Proof.
    Opaque fresh_var.
    intros x.
    induction free_vars.
    - Case "free_vars = nil"%string.
      simpl.
      right.
      apply bdistinct_same_elemts.
      admit. (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
      (* assumption. *)
    - Case "free_vars <> nil"%string.
      intros Hx.
      simpl in Hx.
      admit. (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
      (* destruct Hx; subst; simpl; [intuition | ]. *)
      (* destruct (string_eqdec *)
      (*             (fresh_var "unpack$" (closure_env_name :: nil)) *)
      (*             (fresh_var "unpack$" (closure_env_name :: nil))); [ | congruence]. *)
      (* rewrite in_app_iff in H. *)
      (* destruct H; apply remove_inv in H; destruct H. *)
      (* + rewrite in_app_iff in H. *)
      (*   simpl in H. *)
      (*   destruct H; [ | intuition ]. *)
      (*   apply remove_inv in H. *)
      (*   destruct H. *)
      (*   dest_eqdec; simpl in H; intuition. *)
      (* + specialize (IHfree_vars H). *)
      (*   simpl in IHfree_vars. *)
      (*   intuition. *)
      (*   right. *)
      (*   rewrite <- mult_pos_equiv_in in H1 |- *. *)
      (*   rewrite bminus_mult in H1 |- *. *)
      (*   rewrite mult_on_remove; trivial. *)
  Admitted.

  Lemma nnrcmr_of_nnrc_with_free_vars_wf (n: nrc) (vars_loc: list (var * localization)) (output: var):
    (forall x, In x (nrc_free_vars n) -> In x (List.map fst vars_loc)) ->
    nrcmr_well_formed (nnrcmr_of_nnrc_with_free_vars n vars_loc output).
  Proof.
    Opaque fresh_var.
    unfold nrcmr_well_formed.
    intros Hvars_loc mr.
    unfold nnrcmr_of_nnrc_with_free_vars.
    intros Hmr.
    admit. (* XXXXXXXXXX TODO XXXXXXXXXX *)
    (* destruct (List.fold_right *)
    (*           (fun (x : var) (oacc : option (list (var * localization))) => *)
    (*            olift *)
    (*              (fun loc : localization => *)
    (*               lift *)
    (*                 (fun acc : list (var * localization) => (x, loc) :: acc) *)
    (*                 oacc) (lookup equiv_dec vars_loc x)) *)
    (*           (Some nil) (bdistinct (nrc_free_vars n))); *)
    (*   [ | apply in_nil in Hmr; *)
    (*       contradiction ]. *)
    (* simpl in Hmr. *)
    (* apply in_app_or in Hmr. *)
    (* inversion Hmr; clear Hmr. *)
    (* - Case "pack_closure_env"%string. *)
    (*   admit. (* XXXXXXXXX TODO XXXXXXXXXX *) *)
    (*   (* generalize (pack_closure_env_wf inputdb (bdistinct free_vars_of_n) (really_fresh_in output (output :: avoid) n) mr). *) *)
    (*   (* auto. *) *)
    (* - Case "final_mr"%string. *)
    (*   simpl in H. *)
    (*   inversion H; try contradiction; clear H. *)
    (*   rewrite <- H0; clear H0. *)
    (*   unfold mr_well_formed. *)
    (*   simpl. *)
    (*   repeat split. *)
    (*   + apply coll_function_no_free_vars. *)
    (*   + intros f Hf. *)
    (*     simpl in *. *)
    (*     apply unpack_closure_env_free_vars in Hf; *)
    (*       try solve [ apply bdistinct_same_elemts ]. *)
    (*     rewrite (Hvars_loc f) in Hf. *)

    (*     rewrite Hfree_vars_of_n in Hf. *)
    (*     assert (bminus (bdistinct (nrc_free_vars n)) (bdistinct (nrc_free_vars n)) = nil) as Hbminus; *)
    (*       try solve [ apply bminus_self ]. *)
    (*     rewrite Hbminus in Hf; clear Hbminus. *)
    (*     apply in_inv in Hf. *)
    (*     destruct Hf; try contradiction. *)
    (*     rewrite <- H. *)
    (*     reflexivity. *)
  Admitted.

  (* Semantics correctness *)

  (*
  Lemma nnrcmr_of_nnrc_with_free_vars_correct_help
        h env n free_vars_of_n init output avoid:
    free_vars_of_n <> nil ->
    In init avoid ->
    free_vars_of_n = bdistinct (nrc_free_vars n) ->
    incl (domain env) avoid ->
    incl free_vars_of_n (domain env) ->
    lookup equiv_dec env output = None ->
    nrc_eval h env n =
    get_result (nrcmr_eval h (load_init_env init env) (nnrcmr_of_nnrc_with_free_vars n free_vars_of_n output avoid)).
  Proof.
    revert n init output avoid.
    induction free_vars_of_n; simpl
    ; intros n init output avoid freevars_nempty Hinit_avoid Hfree_vars_of_n Havoid Hfv Houtput
    ; unfold nnrcmr_of_nnrc_with_free_vars.
    - congruence.
    - destruct free_vars_of_n.
      unfold nrcmr_eval. simpl.
      assert (ainenv:In a (domain env))
        by (specialize (Hfv a); simpl in Hfv; intuition).
      rewrite <- env_domain_domain in ainenv.
      apply lookup_in_domain in ainenv.
      destruct ainenv as [ad adin].
      rewrite (load_env_lookup _ _ _ _ adin).
      simpl.
      unfold mr_eval. simpl.
    - simpl. unfold get_result.
      unfold nrcmr_eval. simpl.
      assert (eqq:env_lookup (load_env init env) (really_fresh_in (output :: avoid) n) = None).
      admit.
      rewrite eqq.

  Qed.
      Admitted.
 *)

  Lemma nnrcmr_of_nnrc_with_free_vars_correct h nrc_env mr_env n initunit vars_loc output:
    load_init_env_success initunit vars_loc nrc_env mr_env ->
    (forall x, In x (domain nrc_env) -> In x (domain vars_loc)) ->
    (forall x, In x (nrc_free_vars n) -> exists d, lookup equiv_dec mr_env x = Some d) ->
    lookup equiv_dec mr_env output = None ->
    nrc_eval h nrc_env n =
    nrcmr_eval h mr_env (nnrcmr_of_nnrc_with_free_vars n vars_loc output).
  Proof.
    (* intros Hfree_vars_of_n Havoid Hfv Houtput. *)
    (* unfold nnrcmr_of_nnrc_with_free_vars. *)
    (* unfold nrcmr_eval. *)
    (* rewrite fold_left_app. *)
    (* simpl. *)
    admit. (* XXXXXXXXXXXXXXX *)
  Admitted.


  (* ------------ *
   * General case *
   * ------------ *)

  (* Java equivalent: NnrcToNrcmr.get_nrcmr_vars *)
  Definition get_nrcmr_vars nrm :=
    let vars_loc :=
        List.fold_left
          (fun acc mr =>
             let vinput := mr_input_localized mr in
             let voutput := mr_output_localized mr in
             vinput :: voutput :: acc)
          nrm nil
    in
    vars_loc.

  (**
    Convert any NNRC expression [n] into a Map-Reduce fetching the
    values of the free variables from the environment.

    The variable [initunit] represent a variable in the environment
    that contains unit.

    The variable [output] indicates the place in the environment where
    the result of the evaluation must be stored. The result is a scalar.

    The list [vars_loc] is used to represent the variables that are
    bind in the environment (that may not appear free in [n]).

    The function returns the generated map-reduce and the updated
    version of the [vars_loc] list with the variables introduced by
    the translation.
  *)
  (* Java equivalent: NnrcToNrcmr.mr_chain_of_nnrc *)
  Definition mr_chain_of_nnrc (n: nrc) (initunit: var) (vars_loc: list (var * localization)) (output: var): list mr * list (var * localization) :=
    let mr_chain :=
        match bdistinct (nrc_free_vars n) with
        | nil =>
          mr_chain_of_nnrc_with_no_free_var n initunit output
        | x :: nil =>
          match lookup equiv_dec vars_loc x with
          | Some loc => mr_chain_of_nnrc_with_one_free_var n (x, loc) output
          | None => nil
          end
        | free_vars =>
          mr_chain_of_nnrc_with_free_vars n vars_loc output
        end
    in
    let nrcmr_vars := get_nrcmr_vars mr_chain in
    (mr_chain, nrcmr_vars ++ vars_loc).

  Definition nnrcmr_of_nnrc (n: nrc) (initunit: var) (vars_loc: list (var * localization)) (output: var): nrcmr * list (var * localization) :=
    let (mr_chain, vars_loc) := mr_chain_of_nnrc n initunit vars_loc output in
    (mkMRChain
       mr_chain
       ((output::nil, (NRCVar output)), (output, Vscalar)::nil),
     vars_loc).

  Lemma nnrcmr_of_nnrc_wf (n: nrc) (initunit: var) (vars_loc: list (var * localization)) (output: var):
    nrcmr_well_formed (fst (nnrcmr_of_nnrc n initunit vars_loc output)).
  Proof.
    unfold nnrcmr_of_nnrc.
    case_eq (bdistinct (nrc_free_vars n)).
    admit. (* XXXX TODO XXXX *)
  Admitted.

(* *)

  (* Java equivalent: NnrcToNrcmr.mr_chain_distributed_of_nnrc *)
  Definition mr_chain_distributed_of_nnrc (n: nrc) (initunit: var) (vars_loc: list (var * localization)) (output: var): list mr * list (var * localization) :=
    let (tmp, vars_loc) := fresh_mr_var "scalarcoll$"%string Vdistributed vars_loc in
    let (mr_chain, vars_loc) := mr_chain_of_nnrc n initunit vars_loc tmp in
    (mr_chain ++ ((mr_scalar_to_distributed tmp output)::nil), vars_loc).


  (* Java equivalent: NnrcToNrcmr.mk_loop *)
  Definition mk_loop (x: var) (n1: nrc) (n2: nrc) (mr_list1: list mr) (initunit: var) (vars_loc: list (var * localization)) : nrc * list mr * list (var * localization) :=
    let (n1_distributed_result_var, vars_loc) := fresh_mr_var "distcoll$"%string Vdistributed vars_loc in
    let (n_result_var, vars_loc) := fresh_mr_var "loop_result$"%string Vscalar vars_loc in
    let (mr_n1, vars_loc) := mr_chain_distributed_of_nnrc n1 initunit vars_loc n1_distributed_result_var in
    let mr_n2 :=
        mkMR
          n1_distributed_result_var
          n_result_var
          (MapDist (x, n2))
          (RedCollect id_function)
    in
    let mr_list : list mr :=
        mr_list1 ++ mr_n1 ++ (mr_n2 :: nil)
    in
    (NRCVar n_result_var, mr_list, vars_loc).

  (* Java equivalent: NnrcToNrcmr.try_mk_loop *)
  Definition try_mk_loop (x: var) (n1: nrc) (n2: nrc) (mr_list1: list mr) (initunit: var) (vars_loc: list (var * localization)) : option (nrc * list mr * list (var * localization)) :=
    match bdistinct (nrc_free_vars n2) with
    | nil =>
      Some (mk_loop x n1 n2 mr_list1 initunit vars_loc)
    | x' :: nil =>
      if equiv_dec x x' then
        Some (mk_loop x n1 n2 mr_list1 initunit vars_loc)
      else
        None
    | _ => None
    end.

  (***********************************************************
   * Translate a  NNRC expression into a chain of Map-Reduce *
   ***********************************************************)

  (**
    Auxiliary function for the translation from an NNRC expression
    into a chain of map-reduce. It take as argument:
      - [n] the expresion to translate
      - [init] a variable of the environment that contains a non-empty
        collection to trigger the computations of expressions without
        free variables.
      - [avoid] a list of names to avoid to generate fresh names.
    It returns:
      - a NNRC expression equivalent to the input [n] but in which
        some map-reduces have been extracted
      - the map-reduce elements extracted from [n] in the order
        with respect to the scheduling
      - the updated avoid list.
   *)
              
  (* Java equivalent: NnrcToNrcmr.nnrc_to_nnrcmr_chain_ns_aux *)
  Fixpoint nnrc_to_nnrcmr_chain_ns_aux (n: nrc) (initunit: var) (vars_loc: list (var * localization)): nrc * list mr * list (var * localization) :=
    match n with
    | NRCFor x n1 n2 =>
      let '(n1', mr_list1, avoid) := nnrc_to_nnrcmr_chain_ns_aux n1 initunit vars_loc in
      match try_mk_loop x n1' n2 mr_list1 initunit vars_loc with
      | Some (n', mr_list, vars_loc) => (n', mr_list, vars_loc)
      | None =>
        (NRCFor x n1' n2, mr_list1, vars_loc)
      end
    | NRCVar x =>
      (n, nil, vars_loc)
    | NRCConst d =>
      (n, nil, vars_loc)
    | NRCUnop op n1 =>
      let '(n1', mr_list1, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n1 initunit vars_loc in
      match foreign_to_reduce_op_of_unary_op op with
      | Some red_op =>
        let (n1_distributed_result_var, vars_loc) := fresh_mr_var "distcoll$"%string Vdistributed vars_loc in
        let (mr_n1, vars_loc) := mr_chain_distributed_of_nnrc n1' initunit vars_loc n1_distributed_result_var in
        let (result_var, vars_loc) := fresh_mr_var "res$"%string Vscalar vars_loc in
        let mr :=
            mkMR
              n1_distributed_result_var
              result_var
              (MapDist id_function)
              (RedOp red_op)
        in
        (NRCVar result_var, mr_list1 ++ mr_n1 ++ (mr :: nil), vars_loc)
      | None =>
        match op with
        | AFlatten =>
          let (n1_distributed_result_var, vars_loc) := fresh_mr_var "distcoll$"%string Vdistributed vars_loc in
          let (mr_n1, vars_loc) := mr_chain_distributed_of_nnrc n1' initunit vars_loc n1_distributed_result_var in
          let (flatten_result_var, vars_loc) := fresh_mr_var "flat$"%string Vdistributed vars_loc in
          let mr_flatten :=
              mkMR
                n1_distributed_result_var
                flatten_result_var
                (MapDistFlatten id_function)
                RedId
          in
          (NRCVar flatten_result_var, mr_list1 ++ mr_n1 ++ (mr_flatten :: nil), vars_loc)
        | _ => (NRCUnop op n1', mr_list1, vars_loc)
        end
      end
    | NRCBinop op n1 n2 =>
      let '(n1', mr_list1, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n1 initunit vars_loc in
      let '(n2', mr_list2, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n2 initunit vars_loc in
      (NRCBinop op n1' n2', mr_list1 ++ mr_list2, vars_loc)
    | NRCLet x n1 n2 =>
      let '(n1', mr_list1, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n1 initunit vars_loc in
      let (mr_n1, vars_loc) := mr_chain_of_nnrc n1' initunit vars_loc x in
      let '(n2', mr_list2, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n2 initunit vars_loc in
      (n2', mr_list1 ++ mr_n1 ++ mr_list2, vars_loc)
    | NRCIf n0 n1 n2 =>
      let '(n0', mr_list, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n0 initunit vars_loc in
      let '(n1', mr_list1, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n1 initunit vars_loc in
      let '(n2', mr_list2, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n2 initunit vars_loc in
      (NRCIf n0' n1' n2', nil, vars_loc)
    | NRCEither n0 x n1 y n2 =>
      (n, nil, vars_loc) (* XXX TODO? *)
    end.

  Lemma nnrc_to_nnrcmr_chain_aux_causally_consistent (n: nrc) (initunit: var) (vars_loc: list (var * localization)) :
    shadow_free n = true ->
    let '(_, mr_chain, _) := nnrc_to_nnrcmr_chain_ns_aux n initunit vars_loc in
    mr_chain_causally_consistent mr_chain = true.
  Proof.
    nrc_cases (induction n) Case; simpl;
    try solve [ unfold nrcmr_causally_consistent; reflexivity ].
    - Case "NRCBinop"%string.
      intros Hshadow_free.
      case_eq (nnrc_to_nnrcmr_chain_ns_aux n1 initunit vars_loc).
      intros tmp vars_loc1.
      destruct tmp as (n1', mr_list1).
      intros Hn1.
      case_eq (nnrc_to_nnrcmr_chain_ns_aux n2 initunit vars_loc1).
      intros tmp vars_loc2.
      destruct tmp as (n2', mr_list2).
      intros Hn2.
      unfold nrcmr_causally_consistent.
      admit. (* XXXXXX TODO XXXXXXX *)
    - Case "NRCUnop"%string.
      admit. (* XXXXXX TODO XXXXXXX *)
    - Case "NRCLet"%string.
      admit. (* XXXXXX TODO XXXXXXX *)
    - Case "NRCFor"%string.
      admit. (* XXXXXX TODO XXXXXXX *)
    - Case "NRCIf"%string.
      admit. (* XXXXXX TODO XXXXXXX *)
  Admitted.

  (* Java equivalent: NnrcToNrcmr.nnrc_to_mr_chain_ns *)
  Definition nnrc_to_mr_chain_ns (n: nrc) (initunit: var) (vars_loc: list (var * localization)) (output: var) : list mr :=
    let '(n', mr_list, vars_loc) := nnrc_to_nnrcmr_chain_ns_aux n initunit vars_loc in
    let (final_mr, _) := mr_chain_of_nnrc n' initunit vars_loc output in
    mr_list ++ final_mr.

  (* Java equivalent: NnrcToNrcmr.nnrc_to_nnrcmr_chain_ns *)
  Definition nnrc_to_nnrcmr_chain_ns (n: nrc) (initunit: var) (vars_loc: list (var * localization)) : nrcmr :=
    let output := fresh_var "output" (domain vars_loc) in
    mkMRChain
      (nnrc_to_mr_chain_ns n initunit vars_loc output)
      ((output::nil, (NRCVar output)), (output, Vscalar)::nil).

  (* Java equivalent: NnrcToNrcmr.nnrc_to_nnrcmr_chain *)
  Definition nnrc_to_nnrcmr_chain (n: nrc) (initunit: var) (vars_loc: list (var * localization)) : nrcmr :=
    let n_ns := unshadow_simpl (initunit::nil) n in
    let vars_loc := vars_loc ++ List.map (fun x => (x, Vscalar)) (nrc_bound_vars n_ns) in
    nnrc_to_nnrcmr_chain_ns n_ns initunit vars_loc.

  (* Theorem nnrc_to_nnrcmr_chain_correct h env n initdb initunit output: *)
  (*   (forall x d, *)
  (*      In x (nrc_free_vars n) -> *)
  (*      lookup equiv_dec env x = Some (dcoll (d::nil))) -> *)
  (*   forall d, *)
  (*     lookup equiv_dec env output = Some (dcoll (d::nil)) -> *)
  (*     lookup equiv_dec env output = None -> *)
  (*     nrc_eval h env n = *)
  (*     get_result (nrcmr_eval h env (nnrc_to_nnrcmr_chain n initdb initunit output (output::(domain env)))). *)
  (* Proof. *)
  (*   intros Hfree_vars_of_n Havoid Hfv Houtput. *)
  (*   unfold nnrcmr_of_nnrc_with_free_vars. *)
  (*   unfold nrcmr_eval. *)
  (*   admit. (* XXXXXXXXXXXXXXX *) *)
  (* Qed. *)


  Definition nnrc_to_nnrcmr_no_chain (n: nrc) (vars_loc: list (var * localization)) : nrcmr :=
    mkMRChain
      nil
      ((List.map fst vars_loc, n), vars_loc).

  Lemma load_init_env_build_nrc_env_id env initunit mr_env vars_loc :
    load_init_env initunit vars_loc env = Some mr_env ->
    build_nrc_env mr_env (map fst vars_loc) vars_loc = Some ((initunit, dunit) :: env).
  Proof.
    intros.
    revert env mr_env H.
    induction vars_loc; simpl in *; intros.
  Admitted.

  Theorem nnrc_to_nnrcmr_no_chain_correct h env initunit mr_env (n:nrc) (vars_loc: list (var * localization)) :
      load_init_env initunit vars_loc env = Some mr_env ->
      nrc_eval h env n = nrcmr_eval h mr_env (nnrc_to_nnrcmr_no_chain n vars_loc).
  Proof.
    intros.
    unfold nnrc_to_nnrcmr_no_chain; simpl.
    unfold nrcmr_eval; simpl.
    unfold mr_last_eval; simpl.
    rewrite (load_init_env_build_nrc_env_id env initunit mr_env vars_loc).
    simpl.
    admit.
    assumption.
  Admitted.
  
End NNRCtoNNRCMR.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
