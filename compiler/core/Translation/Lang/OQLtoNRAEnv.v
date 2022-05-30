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
Require Import Arith Lia.
Require Import EquivDec.
Require Import Permutation.
Require Import Morphisms.
Require Import Utils.
Require Import DataRuntime.
Require Import OQL.
Require Import NRAEnvRuntime.

Section OQLtoNRAEnv.
  Context {fruntime:foreign_runtime}.

  Section query_var.
    Context (deflist:list string).

  (*****************************
   * OQL to NRAEnv translation *
   *****************************)

  Definition lookup_table (table_name:string) : nraenv
    := if in_dec string_eqdec table_name deflist
       then NRAEnvUnop (OpDot table_name) NRAEnvEnv
       else NRAEnvGetConstant table_name.

  Fixpoint oql_to_nraenv_expr (e:oql_expr) : nraenv :=
    match e with
    | OConst d => NRAEnvConst d
    | OVar v => NRAEnvUnop (OpDot v) NRAEnvID
    | OTable t => lookup_table t
    | OBinop b e1 e2 => NRAEnvBinop b (oql_to_nraenv_expr e1) (oql_to_nraenv_expr e2)
    | OUnop u e1 => NRAEnvUnop u (oql_to_nraenv_expr e1)
    | OSFW select_clause from_clause where_clause order_clause =>
      let nraenv_of_from (opacc:nraenv) (from_in_expr : oql_in_expr) :=
          match from_in_expr with
          | OIn in_v from_expr =>
            NRAEnvMapProduct (NRAEnvMap (NRAEnvUnop (OpRec in_v) NRAEnvID) (oql_to_nraenv_expr from_expr)) opacc
          | OInCast in_v br from_expr =>
            NRAEnvMapProduct
              (NRAEnvMap (NRAEnvUnop (OpRec in_v) NRAEnvID)
                         (NRAEnvUnop OpFlatten
                                     (NRAEnvMap
                                        (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID)
                                                      (NRAEnvConst (dcoll nil)))
                                        (NRAEnvMap (NRAEnvUnop (OpCast br) NRAEnvID)
                                                   (oql_to_nraenv_expr from_expr))
              )))
              opacc
          end
      in
      let nraenv_of_from_clause :=
          fold_left nraenv_of_from from_clause (NRAEnvUnop OpBag NRAEnvID)
      in
      let nraenv_of_where_clause :=
          match where_clause with
          | OTrue => nraenv_of_from_clause
          | OWhere where_expr =>
            NRAEnvSelect (oql_to_nraenv_expr where_expr) nraenv_of_from_clause
          end
      in
      let nraenv_of_order_clause :=
          match order_clause with
          | ONoOrder => nraenv_of_where_clause
          | OOrderBy order_e sc =>
            let nraenv_order_e := oql_to_nraenv_expr order_e in
            (* Get the sorted value *)
            NRAEnvMap (NRAEnvUnop (OpDot "val") NRAEnvID)
                      (* Sort by sorting criteria *)
                      (NRAEnvUnop (OpOrderBy (("crit"%string, sc)::nil))
                                  (* Create pairs of input value + sorting criteria *)
                                  (NRAEnvMap
                                     (NRAEnvBinop OpRecConcat
                                                  (NRAEnvUnop (OpRec "val") NRAEnvID)
                                                  (NRAEnvUnop (OpRec "crit") nraenv_order_e))
                                     nraenv_of_where_clause))
          end
      in
      match select_clause with
      | OSelect select_expr =>
        NRAEnvMap (oql_to_nraenv_expr select_expr) nraenv_of_order_clause
      | OSelectDistinct select_expr =>
        NRAEnvUnop OpDistinct (NRAEnvMap (oql_to_nraenv_expr select_expr) nraenv_of_order_clause)
      end
    end.

  End query_var.

  Fixpoint oql_to_nraenv_query_program
               (defllist:list string) (oq:oql_query_program) : nraenv
    := match oq with
       | ODefineQuery s e rest =>
         NRAEnvAppEnv 
              (oql_to_nraenv_query_program (s::defllist) rest)
              (NRAEnvBinop OpRecConcat
                      NRAEnvEnv
                      (NRAEnvUnop (OpRec s)
                                  (oql_to_nraenv_expr defllist e)))
       | OUndefineQuery s rest =>
         NRAEnvAppEnv
           (oql_to_nraenv_query_program (remove_all s defllist) rest)
           (NRAEnvUnop (OpRecRemove s) NRAEnvEnv)
       | OQuery q => 
         oql_to_nraenv_expr defllist q
       end.

  Definition oql_to_nraenv (q:oql) : nraenv
    := NRAEnvAppEnv 
         (NRAEnvApp (oql_to_nraenv_query_program nil q)
                    (NRAEnvConst (drec nil)))
         (NRAEnvConst (drec nil)).


  (***************************
   * Translation correctness *
   ***************************)
  
  (* Some useful lemmas *)

  Lemma lift_map_rec_concat_map_is_map_rec_concat_map a s l1 :
    lift_map
      (fun x : data =>
         match x with
         | dunit => None
         | dnat _ => None
         | dfloat _ => None
         | dbool _ => None
         | dstring _ => None
         | dcoll _ => None
         | drec r1 => Some (drec (rec_concat_sort a r1))
         | dleft _ => None
         | dright _ => None
         | dbrand _ _ => None
         | dforeign _ => None
         end) (map (fun d : data => drec ((s, d) :: nil)) l1) =
    Some (map (fun x : list (string * data) => drec (rec_concat_sort a x))
              (map (fun x : data => (s, x) :: nil) l1)).
  Proof.
    induction l1; [reflexivity| ]; simpl.
    rewrite IHl1; simpl.
    reflexivity.
  Qed.
                                                        
  Lemma flatten_either_is_lift_map_either h bn l0:
    (olift oflatten
           (olift
              (lift_map
                 (fun x : data =>
                    match x with
                    | dunit => None
                    | dnat _ => None
                    | dfloat _ => None
                    | dbool _ => None
                    | dstring _ => None
                    | dcoll _ => None
                    | drec _ => None
                    | dleft dl => Some (dcoll (dl :: nil))
                    | dright _ => Some (dcoll nil)
                    | dbrand _ _ => None
                    | dforeign _ => None
                    end))
              (lift_map
                 (fun x : data =>
                    match x with
                    | dunit => None
                    | dnat _ => None
                    | dfloat _ => None
                    | dbool _ => None
                    | dstring _ => None
                    | dcoll _ => None
                    | drec _ => None
                    | dleft _ => None
                    | dright _ => None
                    | dbrand b' _ =>
                      if sub_brands_dec h b' bn
                      then Some (dsome x)
                      else Some dnone
                    | dforeign _ => None
                    end) l0))) =
    lift_flat_map
      (fun x : data =>
         match x with
         | dunit => None
         | dnat _ => None
         | dfloat _ => None
         | dbool _ => None
         | dstring _ => None
         | dcoll _ => None
         | drec _ => None
         | dleft _ => None
         | dright _ => None
         | dbrand b' _ =>
           if sub_brands_dec h b' bn
           then Some (x :: nil)
           else Some nil
         | dforeign _ => None
         end) l0.
  Proof.
    induction l0; [reflexivity| ]; simpl.
    destruct a; try reflexivity.
    destruct (sub_brands_dec h b bn); simpl;
    rewrite <- IHl0;
      destruct ((lift_map
             (fun x : data =>
              match x with
              | dunit => None
              | dnat _ => None
              | dfloat _ => None
              | dbool _ => None
              | dstring _ => None
              | dcoll _ => None
              | drec _ => None
              | dleft _ => None
              | dright _ => None
              | dbrand b' _ =>
                  if sub_brands_dec h b' bn
                  then Some (dsome x)
                  else Some dnone
              | dforeign _ => None
              end) l0)); simpl; try reflexivity;
      destruct (lift_map
          (fun x : data =>
           match x with
           | dunit => None
           | dnat _ => None
           | dfloat _ => None
           | dbool _ => None
           | dstring _ => None
           | dcoll _ => None
           | drec _ => None
           | dleft dl => Some (dcoll (dl :: nil))
           | dright _ => Some (dcoll nil)
           | dbrand _ _ => None
           | dforeign _ => None
           end) l); reflexivity.
  Qed.

  Lemma map_map_drec_works s a l1 l2:
    dcoll
      (map (fun x : list (string * data) => drec (rec_concat_sort a x))
           (map (fun x : data => (s, x) :: nil) l1) ++ 
           map drec l2) =
    (dcoll
       (map drec
            (map (fun x : list (string * data) => rec_concat_sort a x)
                 (map (fun x : data => (s, x) :: nil) l1) ++ l2))).
  Proof.
    rewrite map_map.
    rewrite map_map.
    rewrite map_app.
    rewrite map_map.
    reflexivity.
  Qed.

  Lemma push_lift_coll_in_lift_map l f :
    olift (fun x0 : list oql_env => lift dcoll (lift_map f x0)) l =
    lift dcoll (olift (fun x0 : list oql_env => (lift_map f x0)) l).
  Proof.
    destruct l; reflexivity.
  Qed.

  Lemma olift_rondcoll_over_dcoll l f :
    (olift (fun d : data => rondcoll f d) (lift dcoll l)) =
    (lift (fun x : list data => dcoll (f x)) l).
  Proof.
    destruct l; reflexivity.
  Qed.

  Lemma map_env_with_drec (s:string) (l:list data) :
    (map (fun d : data => drec ((s, d) :: nil)) l) =
    (map drec (map (fun x : data => (s, x) :: nil) l)).
  Proof.
    induction l; try reflexivity; simpl in *.
    rewrite IHl; reflexivity.
  Qed.

  Lemma pull_drec_from_map_concat (s:string) env l :
    Some (map drec
              (env_map_concat_single env (map (fun x : data => (s, x) :: nil) l))) =
    omap_concat (drec env) (map drec (map (fun x : data => (s, x) :: nil) l)).
  Proof.
    induction l; try reflexivity; simpl in *.
    unfold omap_concat in *; simpl in *.
    unfold env_map_concat_single in *; simpl in *.
    rewrite <- IHl; simpl.
    reflexivity.
  Qed.

  Lemma oql_nra_dual_map_concat (s:string) env l:
    Some
      (dcoll
         (map drec
              (env_map_concat_single env
                                     (map (fun x : data => (s, x) :: nil) l)))) =
    lift dcoll
         match
           omap_concat (drec env)
                       (map (fun d : data => drec ((s, d) :: nil)) l)
         with
         | Some x' => Some (x' ++ nil)
         | None => None
         end.
  Proof.
    rewrite map_env_with_drec.
    idtac.
    rewrite <- pull_drec_from_map_concat; simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma lift_map_orecconcat_lift_map_drec s a l0 :
    lift_map (fun x : data => orecconcat (drec a) x)
         (map (fun d : data => drec ((s, d) :: nil)) l0) =
    Some (map (fun d : data => drec (rec_concat_sort a ((s,d)::nil))) l0).
  Proof.
    induction l0; try reflexivity; simpl in *.
    rewrite IHl0; reflexivity.
  Qed.

  Lemma map_drec_app s a l0 l1:
    map (fun d : data => drec (rec_concat_sort a ((s, d) :: nil))) l0 ++
        map drec l1 =
    map drec
        (map (fun x : list (string * data) => rec_concat_sort a x)
             (map (fun x : data => (s, x) :: nil) l0) ++ l1).
  Proof.
    rewrite map_app.
    repeat rewrite map_map.
    trivial.
  Qed.


  (*****************************
   * Select clause correctness *
   *****************************)

  Section correct.
    Context (h:brand_relation_t).
    Context (constant_env:list (string*data)).

    Lemma nraenv_of_select_expr_correct defls
          (o:oql_expr) xenv (env0 : option (list oql_env)) :
      (forall xenv (env : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) o env =
          (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ (drec env) ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv) ->
      olift (fun x0 : list oql_env => lift dcoll (lift_map (oql_expr_interp h (rec_concat_sort constant_env defls) o) x0)) env0 =
    olift
      (fun d : data =>
         lift_oncoll
           (fun c1 : list data =>
              lift dcoll
                   (lift_map
                      (nraenv_eval h constant_env (oql_to_nraenv_expr (domain defls) o) (drec (rec_concat_sort xenv defls)))
                      c1)) d) (lift (fun x => dcoll (map drec x)) env0).
    Proof.
      intros.
      destruct env0; [|reflexivity]; simpl.
      induction l; simpl; try reflexivity.
      rewrite (H xenv).
      destruct (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ (drec a) ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv; simpl;
        [|reflexivity].
      destruct (lift_map (oql_expr_interp h (rec_concat_sort constant_env defls) o) l);
        destruct (lift_map (nraenv_eval h constant_env (oql_to_nraenv_expr (domain defls) o) (drec (rec_concat_sort xenv defls)))
                       (map drec l)); simpl in *; congruence.
    Qed.

    (***************************
     * From clause correctness *
     ***************************)

    (* first off, prove the one-step used in the fold correctly adds one
     variable and does cartesian product (i.e., MapProduct) *)
    Lemma one_from_fold_step_is_map_concat defls s o op xenv envs envs0:
      (h ⊢ op @ₓ envs ⊣ constant_env ; (drec (rec_concat_sort xenv defls)))%nraenv =
      lift (fun x : list (list (string * data)) => dcoll (map drec x)) envs0 ->
      (forall xenv0 (env : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) o env =
          (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ drec env ⊣ constant_env; (drec (rec_concat_sort xenv0 defls)))%nraenv) ->
      ((h ⊢ (NRAEnvMapProduct (NRAEnvMap (NRAEnvUnop (OpRec s) NRAEnvID) (oql_to_nraenv_expr (domain defls) o)) op) @ₓ envs ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv =
       lift (fun x : list (list (string * data)) => dcoll (map drec x))
            (match envs0 with
             | Some envl' =>
               env_map_concat s (oql_expr_interp h (rec_concat_sort constant_env defls) o) envl'
             | None => None
             end)).
    Proof.
      intros; simpl.
      unfold nraenv_eval in *; simpl.
      rewrite H; simpl; clear H.
      destruct envs0; [|reflexivity]; simpl.
      induction l; try reflexivity; simpl.
      unfold env_map_concat in *; simpl.
      unfold omap_product in *; simpl.
      unfold oncoll_map_concat in *; simpl.
      unfold oenv_map_concat_single in *; simpl.
      rewrite (H0 xenv).
      destruct (cNRAEnv.nraenv_core_eval h constant_env
                                         (nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) o))
                                         (drec (rec_concat_sort xenv defls))
                                         (drec a))%nraenv;
        try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      autorewrite with alg; simpl.
      unfold omap_concat in *.
      rewrite lift_map_orecconcat_lift_map_drec.
      destruct ((lift_flat_map
                   (fun a0 : oql_env =>
                      match oql_expr_interp h (rec_concat_sort constant_env defls) o a0 with
                      | Some (dcoll y) =>
                        Some
                          (env_map_concat_single a0
                                                 (map (fun x : data => (s, x) :: nil) y))
                      | Some _ => None
                      | None => None
                      end) l));
        destruct (lift_flat_map
                    (fun a0 : data =>
                       match
                         olift
                           (fun d : data =>
                              lift_oncoll
                                (fun c1 : list data =>
                                   lift dcoll
                                        (lift_map
                                           (fun x : data => Some (drec ((s, x) :: nil)))
                                           c1)) d)
                           (cNRAEnv.nraenv_core_eval h constant_env
                                                     (nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) o)) (drec (rec_concat_sort xenv defls)) a0)%nraenv
                       with
                       | Some (dcoll y) => lift_map (fun x : data => orecconcat a0 x) y
                       | Some _ => None
                       | None => None
                       end) (map drec l)); simpl in *; try congruence; simpl in *.
      inversion IHl. subst; simpl.
      unfold env_map_concat_single; simpl.
      rewrite map_drec_app.
      reflexivity.
    Qed.

    (* re-first off, prove the one-step used in the fold for from-cast
       correctly adds one variable and does cartesian product (i.e.,
       MapProduct) as well *)

    Lemma one_from_cast_fold_step_is_map_concat_cast defls s bn o op xenv envs envs0:
      (h ⊢ op @ₓ envs ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv =
      lift (fun x : list (list (string * data)) => dcoll (map drec x)) envs0 ->
      (forall xenv0 (env : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) o env =
          (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ drec env ⊣ constant_env; (drec (rec_concat_sort xenv0 defls)))%nraenv) ->
      ((h ⊢ (NRAEnvMapProduct
               (NRAEnvMap
                  (NRAEnvUnop (OpRec s) NRAEnvID)
                  (NRAEnvUnop OpFlatten(
                                NRAEnvMap (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID)
                                                        (NRAEnvConst (dcoll nil)))
                                          (NRAEnvMap (NRAEnvUnop (OpCast bn) NRAEnvID)
                                                     (oql_to_nraenv_expr (domain defls) o))))) op) @ₓ envs
          ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv
       =
       lift (fun x : list (list (string * data)) => dcoll (map drec x))
            match envs0 with
            | Some envl' =>
              env_map_concat_cast h s bn (oql_expr_interp h (rec_concat_sort constant_env defls) o) envl'
            | None => None
            end).
    Proof.
      intros; simpl.
      unfold nraenv_eval in *; simpl.
      rewrite H; simpl; clear H.
      destruct envs0; [|reflexivity]; simpl.
      induction l; try reflexivity; simpl.
      unfold env_map_concat_cast in *; simpl.
      unfold omap_product in *; simpl.
      unfold oncoll_map_concat in *; simpl.
      unfold oenv_map_concat_single_with_cast in *; simpl.
      rewrite (H0 xenv).
      destruct (cNRAEnv.nraenv_core_eval h constant_env
                                         (nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) o)) (drec (rec_concat_sort xenv defls))
                                         (drec a))%nraenv;
        try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      unfold filter_cast in *; simpl in *.
      autorewrite with alg; simpl.
      rewrite flatten_either_is_lift_map_either; simpl.
      destruct (lift_flat_map
                  (fun x : data =>
                     match x with
                     | dbrand b' _ =>
                       if sub_brands_dec h b' bn
                       then Some (x :: nil)
                       else Some nil
                     | _ => None
                     end) l0); simpl; try reflexivity.
      autorewrite with alg; simpl.
      unfold env_map_concat_single in *.
      unfold omap_concat in *.
      autorewrite with alg; simpl.
      rewrite lift_map_rec_concat_map_is_map_rec_concat_map; simpl.
      match type of IHl with
      | lift _ ?x = lift _ ?y  => destruct y; destruct x; simpl in *
      end; simpl in *; try discriminate.
      - invcs IHl.
        rewrite map_map_drec_works.
        reflexivity.
      - congruence.
    Qed.

    (* Second, show that 'x in expr' translation is correct *)
  
    Lemma nraenv_of_from_in_correct defls env o s xenv :
      (forall xenv0 (env0 : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) o env0 =
          (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ drec env0 ⊣ constant_env; (drec (rec_concat_sort xenv0 defls)))%nraenv) ->
      (lift (fun x : list (list (string * data)) => dcoll (map drec x))
            (env_map_concat s (oql_expr_interp h (rec_concat_sort constant_env defls) o) (env :: nil))) =
      (nraenv_eval h constant_env (NRAEnvMapProduct (NRAEnvMap (NRAEnvUnop (OpRec s) NRAEnvID) (oql_to_nraenv_expr (domain defls) o)) (NRAEnvUnop OpBag NRAEnvID)) (drec (rec_concat_sort xenv defls)) (drec env)).
    Proof.
      intros; simpl.
      unfold nraenv_eval; simpl.
      unfold omap_product; simpl.
      unfold env_map_concat; simpl.
      unfold oncoll_map_concat; simpl.
      unfold oenv_map_concat_single; simpl.
      rewrite (H xenv); clear H.
      unfold nraenv_eval; simpl.
      destruct (cNRAEnv.nraenv_core_eval h constant_env
                                         (nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) o)) (drec (rec_concat_sort xenv defls))
                                         (drec env))%nraenv;
        try reflexivity; simpl.
      destruct d; simpl; try reflexivity.
      autorewrite with alg; simpl.
      rewrite app_nil_r.
      apply oql_nra_dual_map_concat.
    Qed.

    (* Finally, the main fold_left for a whole from clause is correct *)
  
    Lemma nraenv_of_from_clause_correct defls op envs envs0 el xenv :
      Forall
        (fun ab : oql_in_expr =>
           forall xenv (env : oql_env),
             oql_expr_interp h (rec_concat_sort constant_env defls) (oin_expr ab) env =
             (h ⊢ oql_to_nraenv_expr (domain defls) (oin_expr ab) @ₓ drec env ⊣ constant_env;
                (drec (rec_concat_sort xenv defls)))%nraenv) el ->
      (h ⊢ op @ₓ envs ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv =
      (lift (fun x : list (list (string * data)) => dcoll (map drec x)) envs0) ->
      (lift (fun x : list (list (string * data)) => dcoll (map drec x))
            (fold_left
               (fun (envl : option (list oql_env))
                    (from_in_expr : oql_in_expr) =>
                  match from_in_expr with
                  | OIn in_v from_expr =>
                    match envl with
                    | None => None
                    | Some envl' =>
                      env_map_concat in_v (oql_expr_interp h (rec_concat_sort constant_env defls) from_expr) envl'
                    end
                  | OInCast in_v brand_name from_expr =>
                    match envl with
                    | None => None
                    | Some envl' =>
                      env_map_concat_cast h in_v brand_name (oql_expr_interp h (rec_concat_sort constant_env defls) from_expr) envl'
                    end
                  end
               ) el envs0)) =
      (h
         ⊢ fold_left
         (fun (opacc : nraenv) (from_in_expr : oql_in_expr) =>
            match from_in_expr with
            | OIn in_v from_expr =>
              NRAEnvMapProduct
                (NRAEnvMap (NRAEnvUnop (OpRec in_v) NRAEnvID) (oql_to_nraenv_expr (domain defls) from_expr))
                opacc
            | OInCast in_v brands from_expr =>
              NRAEnvMapProduct
                (NRAEnvMap
                   (NRAEnvUnop (OpRec in_v) NRAEnvID)
                   (NRAEnvUnop OpFlatten
                               (NRAEnvMap (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID)
                                                        (NRAEnvConst (dcoll nil)))
                                          (NRAEnvMap (NRAEnvUnop (OpCast brands)
                                                                 NRAEnvID)
                                                     (oql_to_nraenv_expr (domain defls) from_expr)))))
                opacc
            end
         )
         el op @ₓ envs ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv.
    Proof.
      intros.
      revert op xenv envs0 envs H0.
      induction el; simpl in *; intros; try (rewrite H0; reflexivity).
      destruct a; simpl in *.
      (* OIn case *)
      - inversion H; subst; simpl in *.
        specialize (IHel H4); clear H H4.
        specialize (IHel (NRAEnvMapProduct
                            (NRAEnvMap (NRAEnvUnop (OpRec s) NRAEnvID)
                                       (oql_to_nraenv_expr (domain defls) o)) op)%nraenv).
        assert ((h ⊢ (NRAEnvMapProduct
                        (NRAEnvMap (NRAEnvUnop (OpRec s) NRAEnvID)
                                   (oql_to_nraenv_expr (domain defls) o)) op)%nraenv
                   @ₓ envs ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv =
                lift (fun x : list (list (string * data)) => dcoll (map drec x))
                     (match envs0 with
                      | Some envl' =>
                        env_map_concat s (oql_expr_interp h (rec_concat_sort constant_env defls) o) envl'
                      | None => None
                      end))
          by (apply one_from_fold_step_is_map_concat; assumption).
        apply (IHel xenv (match envs0 with
                          | Some envl' =>
                            env_map_concat s (oql_expr_interp h (rec_concat_sort constant_env defls) o) envl'
                          | None => None
                          end) envs H).
      (* OInCast case *)
      - inversion H; subst; simpl in *.
        specialize (IHel H4); clear H H4.
        specialize
          (IHel (NRAEnvMapProduct
                   (NRAEnvMap
                      (NRAEnvUnop (OpRec s) NRAEnvID)
                      (NRAEnvUnop OpFlatten
                                  (NRAEnvMap
                                     (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID)
                                                   (NRAEnvConst (dcoll nil)))
                                     (NRAEnvMap (NRAEnvUnop (OpCast l) NRAEnvID)
                                                (oql_to_nraenv_expr (domain defls) o))))) (op))%nraenv).
        assert ((h ⊢ (NRAEnvMapProduct
                        (NRAEnvMap
                           (NRAEnvUnop (OpRec s) NRAEnvID)
                           (NRAEnvUnop OpFlatten
                                       (NRAEnvMap
                                          (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID)
                                                        (NRAEnvConst (dcoll nil)))
                                          (NRAEnvMap (NRAEnvUnop (OpCast l) NRAEnvID)
                                                     (oql_to_nraenv_expr (domain defls) o))))) (op)) @ₓ envs
                   ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv
                =
                lift (fun x : list (list (string * data)) => dcoll (map drec x))
                     match envs0 with
                     | Some envl' =>
                       env_map_concat_cast h s l (oql_expr_interp h (rec_concat_sort constant_env defls) o) envl'
                     | None => None
                     end)
          by (apply one_from_cast_fold_step_is_map_concat_cast; assumption).
        apply (IHel xenv (match envs0 with
                          | Some envl' =>
                            env_map_concat_cast h s l (oql_expr_interp h (rec_concat_sort constant_env defls) o) envl'
                          | None => None
                          end) envs H).
    Qed.

    (****************************
     * Where clause correctness *
     ****************************)
  
    Lemma nraenv_of_where_clause_correct defls
          (o:oql_expr) xenv (ol : option (list oql_env)):
      (forall xenv (env : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) o env =
          (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ drec env ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv) ->
      lift (fun x : list (list (string * data)) => dcoll (map drec x))
           (olift
              (lift_filter
                 (fun x' : oql_env =>
                    match oql_expr_interp h (rec_concat_sort constant_env defls) o x' with
                    | Some (dbool b) => Some b
                    | Some _ => None
                    | None => None
                    end)) ol) =
      olift
        (fun d : data =>
           lift_oncoll
             (fun c1 : list data =>
                lift dcoll
                     (lift_filter
                        (fun x' : data =>
                           match
                             (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ x' ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv
                           with
                           | Some (dbool b) => Some b
                           | Some _ => None
                           | None => None
                           end) c1)) d)
        (lift (fun x : list (list (string * data)) => dcoll (map drec x)) ol).
    Proof.
      intros.
      destruct ol; [|reflexivity]; simpl.
      induction l; [reflexivity|idtac]; simpl.
      rewrite (H xenv a); simpl in *.
      destruct (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ drec a ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      destruct (lift_filter
                  (fun x' : data =>
                     match
                       (h ⊢ oql_to_nraenv_expr (domain defls) o @ₓ x' ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv
                     with
                     | Some (dbool b0) => Some b0
                     | Some _ => None
                     | None => None
                     end) (map drec l));
        destruct ((lift_filter
                     (fun x' : oql_env =>
                        match oql_expr_interp h (rec_concat_sort constant_env defls) o x' with
                        | Some (dbool b) => Some b
                        | Some _ => None
                        | None => None
                        end) l)); simpl in *; try congruence.
      inversion IHl; subst.
      destruct b; reflexivity.
    Qed.

    (****************************
     * Order clause correctness *
     ****************************)

    Lemma test1 defls xenv e l :
      (forall (xenv : list (string * data)) (env : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) e env =
          (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
             drec env ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core) ->
      match
        lift_map
          (fun d : list (string * data) =>
           match
             match
               (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
             with
             | Some x' => Some (drec (("crit"%string, x') :: nil))
             | None => None
             end
           with
           | Some (drec r2) =>
               Some
                 (drec
                    (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
           | _ => None
           end) l
      with
      | Some a' => Some (dcoll a')
      | None => None
      end
      = None -> (@lift_map (@oql_env fruntime) (@sortable_data (@oql_env fruntime))
            (fun d : @oql_env fruntime =>
             match
               @fget_criterias (@oql_env fruntime) d
                 (@cons (forall _ : @oql_env fruntime, option sdata)
                    (fun env0 : @oql_env fruntime =>
                     match
                       @oql_expr_interp fruntime h
                         (@rec_concat_sort string ODT_string
                            (@data (@foreign_runtime_data fruntime)) constant_env defls) e env0
                       return (option sdata)
                     with
                     | Some x' => @sdata_of_data (@foreign_runtime_data fruntime) x'
                     | None => @None sdata
                     end) (@nil (forall _ : @oql_env fruntime, option sdata)))
               return (option (prod (list sdata) (@oql_env fruntime)))
             with
             | Some a' =>
                 @Some (prod (list sdata) (@oql_env fruntime))
                   (@pair (list sdata) (@oql_env fruntime) a' d)
             | None => @None (prod (list sdata) (@oql_env fruntime))
             end) l = None).
    Proof.
      intro Hall.
      intros.
      induction l; simpl in *.
      - congruence.
      - case_eq ((h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                    drec a ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core); intros; rewrite H0 in H; simpl in *; try congruence.
        + rename d into ddd.
          unfold lift in H.
          unfold fget_criterias in *; simpl in *.
          rewrite (Hall xenv a).
          rewrite H0; simpl.
          case_eq (lift_map
          (fun d : list (string * data) =>
           match
             match
               (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
             with
             | Some x' => Some (drec (("crit"%string, x') :: nil))
             | None => None
             end
           with
           | Some (drec r2) =>
               Some
                 (drec
                    (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
           | _ => None
           end) l); intros;
            rewrite H1 in *; try congruence.
          specialize (IHl eq_refl).
          destruct (match
                       match
                         @sdata_of_data (@foreign_runtime_data fruntime) ddd return (option (list sdata))
                       with
                       | Some x' => @Some (list sdata) (@cons sdata x' (@nil sdata))
                       | None => @None (list sdata)
                       end return (option (prod (list sdata) (@oql_env fruntime)))
                     with
                     | Some a' =>
                       @Some (prod (list sdata) (@oql_env fruntime))
                             (@pair (list sdata) (@oql_env fruntime) a' a)
                     | None => @None (prod (list sdata) (@oql_env fruntime))
                     end); try reflexivity.
          rewrite IHl.
          reflexivity.
        + unfold fget_criterias; simpl.
          rewrite (Hall xenv a).
          rewrite H0; reflexivity.
    Qed.

    Lemma test2 f l0 l :
      match
        lift_map
          (fun d : list (string * data) =>
             match
               match
                 f (drec d)
               with
               | Some x' => Some (drec (("crit"%string, x') :: nil))
               | None => None
               end
             with
             | Some (drec r2) =>
               Some
                 (drec
                    (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
             | _ => None
             end) l
      with
      | Some a' => Some (dcoll a')
      | None => None
      end = Some (dcoll l0) ->
      exists l1,
        lift_map (fun d : data => match d with
                                  | drec r => Some r
                                  | _ => None
                                  end) l0 = Some l1.
    Proof.
      intros.
      revert l0 H.
      induction l; intros.
      - simpl in *. inversion H; subst. exists nil; reflexivity.
      - simpl in *.
        destruct (f (drec a)); simpl in *; try congruence.
        rename d into ddd.
        unfold lift in *.
        case_eq (lift_map
            (fun d : list (string * data) =>
             match
               match f (drec d) with
               | Some x' => Some (drec (("crit"%string, x') :: nil))
               | None => None
               end
             with
             | Some (drec r2) =>
                 Some
                   (drec
                      (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
             | _ => None
             end) l); intros; rewrite H0 in H; simpl in *; try congruence.
        inversion H; subst; clear H.
        simpl.
        rewrite H0 in IHl.
        elim (IHl l1 eq_refl); intros.
        rewrite H; simpl.
        eauto.
    Qed.
    
    Lemma test3 (l0:list data) (x : list (list (string * data))):
      lift_map (fun d : data => match d with
                                | drec r => Some r
                                | _ => None
                                end) l0 = Some x ->
      exists l1,
        map drec l1 = l0.
    Proof.
      intros.
      revert x H.
      induction l0; intros.
      - exists nil; reflexivity.
      - destruct a; simpl in H; try congruence.
        unfold lift in H.
        case_eq (lift_map (fun d : data => match d with
                                      | drec r => Some r
                                      | _ => None
                                           end) l0); intros; rewrite H0 in *; try congruence.
        elim (IHl0 l1 eq_refl); intros; clear IHl0.
        inversion H; subst.
        rewrite <- lift_map_map_merge in H0.
        rewrite lift_map_map in H0.
        inversion H0.
        subst.
        exists (l::x0); reflexivity.
    Qed.

    Lemma test4 defls xenv e x0 l :
      match
        lift_map
          (fun d : list (string * data) =>
             match
               match
                 (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                    drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
               with
               | Some x' => Some (drec (("crit"%string, x') :: nil))
               | None => None
               end
             with
             | Some (drec r2) =>
               Some
                 (drec
                    (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
             | _ => None
             end) l
      with
      | Some a' => Some (dcoll a')
      | None => None
      end = Some (dcoll (map drec x0)) -> 
        lift_map
          (fun d : list (string * data) =>
             match
               match
                 (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                    drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
               with
               | Some x' => Some (("crit"%string, x') :: nil)
               | None => None
               end
             with
             | Some r2 =>
               Some
                 (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2))
             | _ => None
             end) l
        = Some x0.
    Proof.
      intros.
      case_eq (lift_map
          (fun d : list (string * data) =>
           match
             match
               (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
             with
             | Some x' => Some (drec (("crit"%string, x') :: nil))
             | None => None
             end
           with
           | Some (drec r2) =>
               Some
                 (drec
                    (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
           | _ => None
           end) l); intros; rewrite H0 in H; try congruence.
      inversion H; subst; clear H.
      revert x0 H0.
      induction l; intros; simpl in *.
      - inversion H0; subst.
        destruct x0; simpl; simpl in H1; try congruence.
      - destruct ((h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                     drec a ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core); try congruence; simpl in *.
        unfold lift in *.
        case_eq (lift_map
           (fun d : list (string * data) =>
            match
              match
                (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                 drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
              with
              | Some x' => Some (drec (("crit"%string, x') :: nil))
              | None => None
              end
            with
            | Some (drec r2) =>
                Some
                  (drec
                     (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
            | _ => None
            end) l); intros; simpl in *; rewrite H in H0; try congruence.
        inversion H0; clear H0.
        destruct x0; simpl in H2; try congruence.
        inversion H2; clear H2; subst.
        rewrite (IHl x0 H); reflexivity.
    Qed.

    Lemma test5 defls xenv e lll :
      (forall (xenv : list (string * data)) (env : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) e env =
          (h ⊢ oql_to_nraenv_expr (domain defls) e @ₓ drec env ⊣ constant_env;
          (drec (rec_concat_sort xenv defls)))%nraenv) ->
      @lift_map (@oql_env fruntime) (@sortable_data (@oql_env fruntime))
            (fun d : @oql_env fruntime =>
             match
               match
                 match
                   @oql_expr_interp fruntime h
                     (@rec_concat_sort string ODT_string (@data (@foreign_runtime_data fruntime))
                        constant_env defls) e d return (option sdata)
                 with
                 | Some x' => @sdata_of_data (@foreign_runtime_data fruntime) x'
                 | None => @None sdata
                 end return (option (list sdata))
               with
               | Some x' => @Some (list sdata) (@cons sdata x' (@nil sdata))
               | None => @None (list sdata)
               end return (option (prod (list sdata) (@oql_env fruntime)))
             with
             | Some a' =>
                 @Some (prod (list sdata) (@oql_env fruntime))
                   (@pair (list sdata) (@oql_env fruntime) a' d)
             | None => @None (prod (list sdata) (@oql_env fruntime))
             end) lll =
      lift_map
        (fun d : oql_env =>
           match
             match
               match (h ⊢ oql_to_nraenv_expr (domain defls) e @ₓ drec d ⊣ constant_env;
                     (drec (rec_concat_sort xenv defls)))%nraenv with
               | Some x' => sdata_of_data x'
               | None => None
               end
             with
             | Some x' => Some (x' :: nil)
             | None => None
             end
           with
           | Some a' => Some (a', d)
           | None => None
           end) lll.
    Proof.
      intros.
      induction lll; simpl.
      - reflexivity.
      - rewrite (H xenv a).
        destruct ((h ⊢ oql_to_nraenv_expr (domain defls) e @ₓ drec a ⊣ constant_env;
                   (drec (rec_concat_sort xenv defls)))%nraenv); try reflexivity.
        destruct (sdata_of_data d); try reflexivity.
        unfold lift; simpl.
        rewrite IHlll.
        reflexivity.
    Qed.
    
    Lemma test7 s d a l :
      lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val") l = None ->
      lift_map (fun d0 : list sdata * list (string * data) => edot (snd d0) "val")
               (insertion_sort_insert dict_field_le_dec
                                      (s :: nil, ("crit"%string, d) :: ("val"%string, drec a) :: nil) 
                                      l) = None.
    Proof.
      intros.
      revert l H.
      induction l; intros; simpl in *.
      - congruence.
      - destruct a0; simpl in *.
        destruct (LexicographicDataOrder.le_dec (s :: nil) l0);
        destruct (LexicographicDataOrder.le_dec l0 (s :: nil)); simpl in *;
        case_eq (edot l1 "val"); intros; rewrite H0 in *; try congruence; try reflexivity.
        rewrite H; reflexivity.
        rewrite H; reflexivity.
        rewrite IHl. reflexivity.
        unfold lift in H.
        destruct (lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val") l); try congruence.
    Qed.

    Lemma test8 s a d l l0 :
      lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val") (dict_sort l) =
      Some (map drec (map snd (dict_sort l0))) ->
      lift_map (fun d0 : list sdata * list (string * data) => edot (snd d0) "val")
               (insertion_sort_insert dict_field_le_dec
                                      (s :: nil, ("crit"%string, d) :: ("val"%string, drec a) :: nil) 
                                      (dict_sort l)) =
      Some (map drec (map snd (insertion_sort_insert dict_field_le_dec
                                                     (s :: nil, a) (dict_sort l0)))).
    Proof.
      rewrite map_map.
      rewrite map_map.
      intros.
      revert a l0 H.
      induction l; simpl in *; intros.
      - inversion H; simpl in *; clear H; subst.
        assert (map (fun x : list sdata * list (string * data) => drec (snd x)) (dict_sort l0) = nil) by auto; clear H1.
        assert (dict_sort l0 = nil).
        apply (map_eq_nil _ _ H); clear H.
        assert (l0 = nil).
        unfold dict_sort in H0.
        apply (insertion_sort_nil dict_field_le_dec _ H0).
        subst; reflexivity.
      - destruct a; simpl in *.
        rename l2 into a1.
        destruct l0; simpl in *.
        + case_eq (dict_sort l); intros; rewrite H0 in H; simpl in H.
          destruct (edot a1 "val"); try congruence.
          destruct p; simpl in *; try congruence.
          destruct (LexicographicDataOrder.le_dec l1 l2); simpl in H; try congruence.
          unfold lift in H.
          destruct (edot a1 "val"); try congruence.
          destruct (edot l3 "val"); try congruence.
          destruct (lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val") l0); try congruence.
          destruct (LexicographicDataOrder.le_dec l2 l1); simpl in H; try congruence.
          unfold lift in H.
          destruct (edot l3 "val"); try congruence.
          destruct (@lift_map
            (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
            (@data (@foreign_runtime_data fruntime))
            (fun
               d : prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
             =>
             @edot (@data (@foreign_runtime_data fruntime))
               (@snd (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))) d)
               (String (Ascii.Ascii false true true false true true true false)
                  (String (Ascii.Ascii true false false false false true true false)
                     (String (Ascii.Ascii false false true true false true true false) EmptyString))))
            (@insertion_sort_insert
               (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
               (@dict_field_le (list (prod string (@data (@foreign_runtime_data fruntime)))))
               (@dict_field_le_dec (list (prod string (@data (@foreign_runtime_data fruntime)))))
               (@pair (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
                  l1 a1) l0)); try congruence.
          destruct (edot l3 "val"); try congruence; unfold lift in H.
          destruct (lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val") l0); try congruence.
        + specialize (IHl a0 l0).
          assert (lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val") (dict_sort l) =
        Some
          (map (fun x : list sdata * list (string * data) => drec (snd x)) (dict_sort l0))).
          admit.
          specialize (IHl H0); clear H0.
          

      admit.
    Admitted.

    Lemma test6 f lll x0 :
      lift_map
        (fun d : list (string * data) =>
           match
             match f d with
             | Some x' => Some (("crit"%string, x') :: nil)
             | None => None
             end
           with
           | Some r2 =>
             Some (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2))
           | None => None
           end) lll = Some x0
      ->
      match
        match
          match
            lift_map
              (fun d : oql_env =>
                 match
                   match
                     match f d with
                     | Some x' => sdata_of_data x'
                     | None => None
                     end
                   with
                   | Some x' => Some (x' :: nil)
                   | None => None
                   end
                 with
                 | Some a' => Some (a', d)
                 | None => None
                 end) lll
          with
          | Some a' => Some (dict_sort a')
          | None => None
          end
        with
        | Some a' => Some (coll_of_sortable_coll a')
        | None => None
        end
      with
      | Some a' => Some (dcoll (map drec a'))
      | None => None
      end =
      match
        match
          match
            match
              lift_map
                (fun d : list (string * data) =>
                   match
                     match
                       match edot d "crit" with
                       | Some d0 => sdata_of_data d0
                       | None => None
                       end
                     with
                     | Some x' => Some (x' :: nil)
                     | None => None
                     end
                   with
                   | Some a' => Some (a', d)
                   | None => None
                   end) x0
            with
            | Some a' => Some (dict_sort a')
            | None => None
            end
          with
          | Some a' => Some (coll_of_sortable_coll a')
          | None => None
          end
        with
        | Some a' => Some (dcoll (map drec a'))
        | None => None
        end
      with
      | Some x' =>
        lift_oncoll
          (fun c1 : list data =>
             match
               lift_map (fun din : data => match din with
                                           | drec r => edot r "val"
                                           | _ => None
                                           end) c1
             with
             | Some a' => Some (dcoll a')
             | None => None
             end) x'
      | None => None
      end.
    Proof.
      intros.
      revert x0 H.
      induction lll; intros; simpl.
      - destruct x0; simpl in *; congruence.
      - simpl in H.
        destruct (f a); simpl in *; try congruence.
        unfold lift in *.
        case_eq (lift_map
          (fun d : list (string * data) =>
           match
             match f d with
             | Some x' => Some (("crit"%string, x') :: nil)
             | None => None
             end
           with
           | Some r2 =>
               Some (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2))
           | None => None
           end) lll); intros;
          rewrite H0 in H; simpl in H; try congruence.
        inversion H; clear H.
        destruct x0; try congruence.
        inversion H2; subst; clear H2.
        case_eq (sdata_of_data d); simpl; intros;
          rewrite H; simpl; try reflexivity.
        specialize (IHlll x0 H0); clear H0;
          unfold lift in *.
        case_eq (lift_map
                  (fun d : oql_env =>
                   match
                     match match f d with
                           | Some x' => sdata_of_data x'
                           | None => None
                           end with
                     | Some x' => Some (x' :: nil)
                     | None => None
                     end
                   with
                   | Some a' => Some (a', d)
                   | None => None
                   end) lll);
                  case_eq (lift_map
                    (fun d : list (string * data) =>
                     match
                       match
                         match edot d "crit" with
                         | Some d0 => sdata_of_data d0
                         | None => None
                         end
                       with
                       | Some x' => Some (x' :: nil)
                       | None => None
                       end
                     with
                     | Some a' => Some (a', d)
                     | None => None
                     end) x0); intros; rewrite H0 in *; rewrite H1 in *;
                    simpl in *; try congruence.
        + unfold coll_of_sortable_coll in *.
          repeat (rewrite <- lift_map_map_merge).
          repeat (rewrite <- lift_map_map_merge in IHlll).
          clear H H0 H1.
          case_eq (lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val")
                            (dict_sort l)); intros; rewrite H in IHlll; try congruence.
          inversion IHlll; subst; clear IHlll.
          apply (test8 s a d) in H.
          assert ((@lift_map
           (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
           (@data (@foreign_runtime_data fruntime))
           (fun
              d0 : prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
            =>
            @edot (@data (@foreign_runtime_data fruntime))
              (@snd (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))) d0)
              (String (Ascii.Ascii false true true false true true true false)
                 (String (Ascii.Ascii true false false false false true true false)
                    (String (Ascii.Ascii false false true true false true true false) EmptyString))))
           (@insertion_sort_insert
              (@sortable_data (list (prod string (@data (@foreign_runtime_data fruntime)))))
              (@dict_field_le (list (prod string (@data (@foreign_runtime_data fruntime)))))
              (@dict_field_le_dec (list (prod string (@data (@foreign_runtime_data fruntime)))))
              (@pair (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
                 (@cons sdata s (@nil sdata))
                 (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                    (@pair string (@data (@foreign_runtime_data fruntime))
                       (String (Ascii.Ascii true true false false false true true false)
                          (String (Ascii.Ascii false true false false true true true false)
                             (String (Ascii.Ascii true false false true false true true false)
                                (String (Ascii.Ascii false false true false true true true false)
                                   EmptyString)))) d)
                    (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                       (@pair string (@data (@foreign_runtime_data fruntime))
                          (String (Ascii.Ascii false true true false true true true false)
                             (String (Ascii.Ascii true false false false false true true false)
                                (String (Ascii.Ascii false false true true false true true false)
                                   EmptyString))) (@drec (@foreign_runtime_data fruntime) a))
                       (@nil (prod string (@data (@foreign_runtime_data fruntime)))))))
              (@dict_sort (list (prod string (@data (@foreign_runtime_data fruntime)))) l))) = @lift_map (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
        (@data (@foreign_runtime_data fruntime))
        (fun d0 : prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
         =>
         @edot (@data (@foreign_runtime_data fruntime))
           (@snd (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))) d0)
           (String (Ascii.Ascii false true true false true true true false)
              (String (Ascii.Ascii true false false false false true true false)
                 (String (Ascii.Ascii false false true true false true true false) EmptyString))))
        (@insertion_sort_insert
           (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
           (@dict_field_le (list (prod string (@data (@foreign_runtime_data fruntime)))))
           (@dict_field_le_dec (list (prod string (@data (@foreign_runtime_data fruntime)))))
           (@pair (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
              (@cons sdata s (@nil sdata))
              (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                 (@pair string (@data (@foreign_runtime_data fruntime))
                    (String (Ascii.Ascii true true false false false true true false)
                       (String (Ascii.Ascii false true false false true true true false)
                          (String (Ascii.Ascii true false false true false true true false)
                             (String (Ascii.Ascii false false true false true true true false)
                                EmptyString)))) d)
                 (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                    (@pair string (@data (@foreign_runtime_data fruntime))
                       (String (Ascii.Ascii false true true false true true true false)
                          (String (Ascii.Ascii true false false false false true true false)
                             (String (Ascii.Ascii false false true true false true true false)
                                EmptyString))) (@drec (@foreign_runtime_data fruntime) a))
                    (@nil (prod string (@data (@foreign_runtime_data fruntime)))))))
           (@dict_sort (list (prod string (@data (@foreign_runtime_data fruntime)))) l))) by reflexivity.
          rewrite H0 in H; clear H0.
          rewrite H; reflexivity.
        + unfold coll_of_sortable_coll in *.
          repeat (rewrite <- lift_map_map_merge).
          repeat (rewrite <- lift_map_map_merge in IHlll).
          case_eq (lift_map (fun d : list sdata * list (string * data) => edot (snd d) "val")
                            (dict_sort l));
            intros; rewrite H2 in IHlll; try congruence.
          assert (lift_map (fun d0 : list sdata * list (string * data) => edot (snd d0) "val")
                           (insertion_sort_insert dict_field_le_dec
                                                  (s :: nil, ("crit"%string, d) :: ("val"%string, drec a) :: nil) 
                                                  (dict_sort l)) = None) by
              (apply test7; assumption).
          assert (@lift_map (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
        (@data (@foreign_runtime_data fruntime))
        (fun d0 : prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
         =>
         @edot (@data (@foreign_runtime_data fruntime))
           (@snd (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))) d0)
           (String (Ascii.Ascii false true true false true true true false)
              (String (Ascii.Ascii true false false false false true true false)
                 (String (Ascii.Ascii false false true true false true true false) EmptyString))))
        (@insertion_sort_insert
           (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
           (@dict_field_le (list (prod string (@data (@foreign_runtime_data fruntime)))))
           (@dict_field_le_dec (list (prod string (@data (@foreign_runtime_data fruntime)))))
           (@pair (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
              (@cons sdata s (@nil sdata))
              (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                 (@pair string (@data (@foreign_runtime_data fruntime))
                    (String (Ascii.Ascii true true false false false true true false)
                       (String (Ascii.Ascii false true false false true true true false)
                          (String (Ascii.Ascii true false false true false true true false)
                             (String (Ascii.Ascii false false true false true true true false)
                                EmptyString)))) d)
                 (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                    (@pair string (@data (@foreign_runtime_data fruntime))
                       (String (Ascii.Ascii false true true false true true true false)
                          (String (Ascii.Ascii true false false false false true true false)
                             (String (Ascii.Ascii false false true true false true true false)
                                EmptyString))) (@drec (@foreign_runtime_data fruntime) a))
                    (@nil (prod string (@data (@foreign_runtime_data fruntime)))))))
           (@dict_sort (list (prod string (@data (@foreign_runtime_data fruntime)))) l))
         = (@lift_map
            (prod (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))))
            (@data (@foreign_runtime_data fruntime))
            (fun
               d0 : prod (list sdata)
                      (list (prod string (@data (@foreign_runtime_data fruntime)))) =>
             @edot (@data (@foreign_runtime_data fruntime))
               (@snd (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime)))) d0)
               (String (Ascii.Ascii false true true false true true true false)
                  (String (Ascii.Ascii true false false false false true true false)
                     (String (Ascii.Ascii false false true true false true true false) EmptyString))))
            (@insertion_sort_insert
               (@sortable_data (list (prod string (@data (@foreign_runtime_data fruntime)))))
               (@dict_field_le (list (prod string (@data (@foreign_runtime_data fruntime)))))
               (@dict_field_le_dec (list (prod string (@data (@foreign_runtime_data fruntime)))))
               (@pair (list sdata) (list (prod string (@data (@foreign_runtime_data fruntime))))
                  (@cons sdata s (@nil sdata))
                  (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                     (@pair string (@data (@foreign_runtime_data fruntime))
                        (String (Ascii.Ascii true true false false false true true false)
                           (String (Ascii.Ascii false true false false true true true false)
                              (String (Ascii.Ascii true false false true false true true false)
                                 (String (Ascii.Ascii false false true false true true true false)
                                    EmptyString)))) d)
                     (@cons (prod string (@data (@foreign_runtime_data fruntime)))
                        (@pair string (@data (@foreign_runtime_data fruntime))
                           (String (Ascii.Ascii false true true false true true true false)
                              (String (Ascii.Ascii true false false false false true true false)
                                 (String (Ascii.Ascii false false true true false true true false)
                                    EmptyString))) (@drec (@foreign_runtime_data fruntime) a))
                        (@nil (prod string (@data (@foreign_runtime_data fruntime)))))))
               (@dict_sort (list (prod string (@data (@foreign_runtime_data fruntime)))) l)))) by reflexivity.
          rewrite H4.
          rewrite H3; reflexivity.
    Qed.

    Lemma nraenv_of_order_clause_correct defls sc
          (e:oql_expr) xenv (ol: option (list oql_env)) :
      (forall xenv (env : oql_env),
          oql_expr_interp h (rec_concat_sort constant_env defls) e env =
          (h ⊢ oql_to_nraenv_expr (domain defls) e @ₓ drec env ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv) ->
      lift (fun x : list (list (string * data)) => dcoll (map drec x))
           (olift
              (fun l => table_sort
                          ((fun env0 : oql_env =>
                              olift sdata_of_data (oql_expr_interp h (rec_concat_sort constant_env defls) e env0))
                             :: nil) l) ol) =
      olift
       (fun d : data =>
        lift_oncoll
          (fun c1 : list data =>
           lift dcoll
             (lift_map (fun din : data => match din with
                                          | drec r => edot r "val"
                                          | _ => None
                                          end) c1)) d)
       (olift (fun d1 : data => data_sort (get_criteria ("crit"%string, sc) :: nil) d1)
          (olift
             (fun d : data =>
              lift_oncoll
                (fun c1 : list data =>
                 lift dcoll
                   (lift_map
                      (fun din : data =>
                       match
                         olift (fun d1 : data => Some (drec (("crit"%string, d1) :: nil)))
                           (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ
                            din ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
                       with
                       | Some (drec r2) =>
                           Some
                             (drec
                                (insertion_sort_insert rec_field_lt_dec 
                                   ("val"%string, din) (rec_sort r2)))
                       | _ => None
                       end) c1)) d)
             (lift (fun x : list (list (string * data)) => dcoll (map drec x)) ol))).
    Proof.
      intros.
      destruct ol; try reflexivity; simpl.
      unfold olift, lift.
      rewrite <- lift_map_map_merge.
      unfold data_sort.
      unfold table_of_data.
      unfold table_sort in *; simpl in *.
      unfold fsortable_coll_of_coll in *; simpl in *.
      unfold fsortable_data_of_data in *; simpl in *.
      case_eq (match
                    lift_map
                      (fun d : list (string * data) =>
                         match
                           match
                             (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                                drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
                           with
                           | Some x' => Some (drec (("crit"%string, x') :: nil))
                           | None => None
                           end
                         with
                         | Some (drec r2) =>
                           Some
                             (drec
                                (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
                         | _ => None
                         end) l
                  with
                  | Some a' => Some (dcoll a')
                  | None => None
                end); intros;[
      | unfold lift; rewrite (test1 defls xenv e l H H0); reflexivity].
      simpl.
      unfold data_of_table, lift.
      unfold sort_sortable_coll in *.
      unfold olift.
      Set Nested Proofs Allowed.
      rename d into ddd.
      destruct ddd; simpl;
        try (destruct (lift_map
                    (fun d : list (string * data) =>
                       match
                         match
                           (h ⊢ₑ nraenv_to_nraenv_core (oql_to_nraenv_expr (domain defls) e) @ₑ 
                              drec d ⊣ constant_env; (drec (rec_concat_sort xenv defls)))%nraenv_core
                         with
                         | Some x' => Some (drec (("crit"%string, x') :: nil))
                         | None => None
                         end
                       with
                       | Some (drec r2) =>
                         Some
                           (drec
                              (insertion_sort_insert rec_field_lt_dec ("val"%string, drec d) (rec_sort r2)))
                       | _ => None
                       end) l); congruence).
      elim (test2 _ l0 l H0); intros.
      rewrite H1; simpl.
      elim (test3 l0 x H1); intros.
      subst.
      rewrite <- lift_map_map_merge in H1.
      rewrite lift_map_map in H1.
      inversion H1; subst; simpl; clear H1.
      rewrite <- lift_map_map_merge; simpl.
      rename l into lll.
      apply (test4 defls xenv e x0 lll) in H0.
      unfold fget_criterias; simpl.
      rewrite (test5 defls xenv e lll H); clear H.
      apply test6; assumption.
    Qed.

    (* OQL expr to NRAEnv translation is correct *)

    (* delete env section *)
    Theorem oql_to_nraenv_expr_correct (e:oql_expr) :
      forall xenv, forall defls, forall env,
            oql_expr_interp h (rec_concat_sort constant_env defls) e env =
            (nraenv_eval h constant_env (oql_to_nraenv_expr (domain defls) e)
                         (drec (rec_concat_sort xenv defls)) (drec env))%nraenv.
    Proof.
      intros. revert xenv env.
      induction e; intros.
      (* OConst *)
      - reflexivity.
      (* OVar *)
      - reflexivity.
      (* OTable *)
      - simpl; unfold lookup_table; unfold nraenv_eval.
        match_destr; simpl.
        + unfold edot.
          unfold rec_concat_sort.
          repeat rewrite assoc_lookupr_drec_sort.
          rewrite (assoc_lookupr_app constant_env defls).
          rewrite (assoc_lookupr_app xenv defls).
          match_case; intros nin.
          apply assoc_lookupr_none_nin in nin.
          congruence.
        + unfold edot.
          unfold rec_concat_sort.
          rewrite assoc_lookupr_drec_sort.
          rewrite (assoc_lookupr_app constant_env defls).
          match_case; intros ? inn.
          apply assoc_lookupr_in in inn.
          apply in_dom in inn.
          congruence.
      (* OBinop *)
      - simpl; rewrite (IHe1 xenv env); rewrite (IHe2 xenv env).
        reflexivity.
      (* OUnop *)
      - simpl; rewrite (IHe xenv env).
        reflexivity.
      (* OSFW *)
      - destruct e1.
        + simpl in *.
          generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil)))
          ; [idtac|assumption|reflexivity].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          reflexivity.
        + simpl in *.
          generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          rewrite push_lift_coll_in_lift_map; simpl.
          rewrite olift_rondcoll_over_dcoll.
          reflexivity.
      - destruct e1.
        + simpl in *.
          generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
          generalize nraenv_of_where_clause_correct; intros Hwhere.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hwhere; [|assumption].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          reflexivity.
        + simpl in *.
          generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
          generalize nraenv_of_where_clause_correct; intros Hwhere.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hwhere; [|assumption].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          rewrite push_lift_coll_in_lift_map; simpl.
          rewrite olift_rondcoll_over_dcoll.
          reflexivity.
      - simpl. destruct e1.
        + generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
          generalize nraenv_of_order_clause_correct; intros Horder.
          rewrite <- Horder; [|assumption].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          reflexivity.
        + simpl in *.
          generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
          generalize nraenv_of_order_clause_correct; intros Horder.
          rewrite <- Horder; [|assumption].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          rewrite push_lift_coll_in_lift_map; simpl.
          rewrite olift_rondcoll_over_dcoll.
          reflexivity.
      - destruct e1.
        + simpl in *.
          generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
          generalize nraenv_of_where_clause_correct; intros Hwhere.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hwhere; [|assumption].
          generalize nraenv_of_order_clause_correct; intros Horder.
          rewrite <- Horder; [|assumption].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          reflexivity.
        + simpl in *.
          generalize (nraenv_of_from_clause_correct defls); intros Hfrom.
          unfold nraenv_eval in *; simpl.
          rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
          generalize nraenv_of_where_clause_correct; intros Hwhere.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hwhere; [|assumption].
          generalize nraenv_of_order_clause_correct; intros Horder.
          rewrite <- Horder; [|assumption].
          generalize nraenv_of_select_expr_correct; intros Hselect.
          unfold nraenv_eval in *; simpl.
          rewrite <- Hselect; [|assumption].
          rewrite push_lift_coll_in_lift_map; simpl.
          rewrite olift_rondcoll_over_dcoll.
          reflexivity.
    Qed.

    Global Instance lookup_table_proper :
      Proper (equivlist ==> eq ==> eq) lookup_table.
    Proof.
      red; intros l1 l2 eql s1 s2 eqs; subst s2.
      unfold lookup_table.
      match_destr; match_destr.
      - rewrite eql in i; congruence.
      - rewrite <- eql in i; congruence.
    Qed.

    Global Instance oql_to_nraenv_expr_proper :
      Proper (equivlist ==> eq ==> eq) oql_to_nraenv_expr.
    Proof.
      Ltac fold_left_local_solver 
        := match goal with
             [H:Forall _ ?el |- fold_left ?f1 ?e1 ?n1 = fold_left ?f2 ?e2 ?n2 ]
             => cut (forall n, fold_left f1 e1 n = fold_left f2 e2 n); [solve[auto] | ]
                ; intros n; revert H n
                ; let IHel := (fresh "IHel") in
                  (induction el as [| ? ? IHel]; intros FH n; simpl in *; trivial
                   ; invcs FH; rewrite IHel; trivial
                   ; match_destr; simpl in *; congruence)
           end.
      red; intros l1 l2 eql q1 q2 eqq; subst q2.
      induction q1; simpl in *; trivial.
      - rewrite eql; trivial.
      - rewrite IHq1_1, IHq1_2; trivial.
      - rewrite IHq1; trivial.
      - destruct e1; simpl in *; rewrite IHq1; clear IHq1.
        + do 1 f_equal; fold_left_local_solver.
        + do 2 f_equal; fold_left_local_solver.
      - destruct e1; simpl in *; rewrite IHq0, IHq1; clear IHq0 IHq1.
        + do 2 f_equal; fold_left_local_solver.
        + do 3 f_equal; fold_left_local_solver.
      - destruct e1; simpl in *; rewrite IHq0, IHq1; clear IHq0 IHq1.
        + do 4 f_equal; fold_left_local_solver.
        + do 5 f_equal; fold_left_local_solver.
      - destruct e1; simpl in *; rewrite IHq1_1, IHq1_2, IHq1_3; clear IHq1_1 IHq1_2 IHq1_3.
        + do 5 f_equal; fold_left_local_solver.
        + do 6 f_equal; fold_left_local_solver.
    Qed.
  
    Global Instance oql_to_nraenv_query_program_proper :
      Proper (equivlist ==> eq ==> eq) oql_to_nraenv_query_program.
    Proof.
      red; intros l1 l2 eql q1 q2 eqq; subst q2.
      revert l1 l2 eql.
      induction q1; intros l1 l2 eql; simpl.
      - f_equal.
        + apply IHq1.
          apply equivlist_cons; trivial.
        + do 2 f_equal. apply oql_to_nraenv_expr_proper; trivial.
      - f_equal.
        apply IHq1.
        apply equivlist_remove_all; trivial.
      - apply oql_to_nraenv_expr_proper; trivial.
    Qed.

    Lemma rec_concat_sort_domain_app_commutatuve_equiv {K} {odt:ODT} {B} l1 l2 :
      (equivlist (domain (rec_concat_sort l1 l2)) (domain l2 ++ @domain K B l1)).
    Proof.
      unfold rec_concat_sort.
      rewrite drec_sort_equiv_domain.
      rewrite domain_app.
      rewrite app_commutative_equivlist.
      simpl.
      reflexivity.
    Qed.

    Lemma oql_to_nraenv_query_program_correct (defllist:list string) (oq:oql_query_program) :
      forall (defls:oql_env) xenv,
        (forall x, In x ((domain defls)++(oql_query_program_defls oq)) -> ~In x (domain xenv)) ->
        oql_query_program_interp h constant_env defls oq =
        nraenv_eval h constant_env (oql_to_nraenv_query_program (domain defls) oq) (drec (rec_concat_sort xenv defls)) (drec nil).
    Proof.
      intros. revert defls xenv H.
      induction oq; simpl; intros.
      - rewrite (oql_to_nraenv_expr_correct _ xenv).
        unfold nraenv_eval; simpl.
        match goal with
          [|- olift _ ?x = _ ] => destruct x
        end; simpl; trivial.
        rewrite (IHoq _ xenv).
        + unfold nraenv_eval; simpl.
          assert (equivlist (domain (rec_concat_sort defls ((s, d) :: nil))) (s::domain defls))
            by (rewrite rec_concat_sort_domain_app_commutatuve_equiv; simpl; reflexivity).
          rewrite (oql_to_nraenv_query_program_proper _ _ H0 _ _ (eq_refl _ )).
          unfold rec_concat_sort.
          rewrite rec_sort_rec_sort_app1.
          rewrite app_ass.
          rewrite rec_sort_rec_sort_app2.
          trivial.
        + intros.
          apply H.
          rewrite in_app_iff in H0.
          unfold rec_concat_sort in H0.
          rewrite in_dom_rec_sort in H0.
          rewrite domain_app in H0.
          simpl in H0.
          rewrite in_app_iff in H0.
          rewrite in_app_iff; simpl in *.
          tauto.
      - unfold nraenv_eval; simpl.
        rewrite (IHoq _ xenv).
        + unfold nraenv_eval.
          f_equal.
          * rewrite domain_rremove; trivial.
          * unfold rec_concat_sort.
            rewrite rremove_rec_sort_commute.
            rewrite rremove_app.
            rewrite (nin_rremove xenv); trivial.
            apply H.
            rewrite in_app_iff; simpl.
            tauto.
        + intros.
          apply H.
          rewrite in_app_iff; simpl.
          rewrite domain_rremove in H0.
          rewrite in_app_iff in H0.
          rewrite remove_all_filter in H0.
          rewrite filter_In in H0.
          tauto.
      - apply oql_to_nraenv_expr_correct.
    Qed.
    
    Theorem oql_to_nraenv_correct (q:oql) :
      forall xenv xdata,
        oql_interp h constant_env q =
        nraenv_eval h constant_env (oql_to_nraenv q) xenv xdata.
    Proof.
      intros xenv.
      unfold oql_to_nraenv, oql_interp.
      rewrite (oql_to_nraenv_query_program_correct nil q nil nil); simpl; [| tauto].
      reflexivity.
    Qed.
  End correct.

  Section Top.
    Context (h:brand_relation_t).

    (* Top-level translation call *)
    Definition oql_to_nraenv_top (q:oql) : nraenv :=
      oql_to_nraenv q.

    Theorem oql_to_nraenv_top_correct (q:oql) (cenv:bindings) : 
        oql_eval_top h q cenv =
        nraenv_eval_top h (oql_to_nraenv_top q) cenv.
    Proof.
      apply oql_to_nraenv_correct.
    Qed.
  End Top.

End OQLtoNRAEnv.

