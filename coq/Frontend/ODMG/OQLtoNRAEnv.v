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

Section OQLtoNRAEnv.

  Require Import String.
  Require Import List.
  Require Import Arith Omega.
  Require Import EquivDec.

  Require Import Utils BasicSystem.

  Require Import OQL.
  Require Import NRAEnvRuntime.

  Context {fruntime:foreign_runtime}.

  Context (h:list(string*string)).
  Context (constant_env:list (string*data)).

  (*****************************
   * OQL to NRAEnv translation *
   *****************************)
  
  Fixpoint nraenv_of_oql (e:oql_expr) : nraenv :=
    match e with
    | OConst d => NRAEnvConst d
    | OVar v => NRAEnvUnop (ADot v) NRAEnvID
    | OTable t => NRAEnvGetConstant t
    | OBinop b e1 e2 => NRAEnvBinop b (nraenv_of_oql e1) (nraenv_of_oql e2)
    | OUnop u e1 => NRAEnvUnop u (nraenv_of_oql e1)
    | OSFW select_clause from_clause where_clause order_clause =>
      let nraenv_of_from (opacc:nraenv) (from_in_expr : oql_in_expr) :=
          match from_in_expr with
            | OIn in_v from_expr =>
              NRAEnvMapConcat (NRAEnvMap (NRAEnvUnop (ARec in_v) NRAEnvID) (nraenv_of_oql from_expr)) opacc
            | OInCast in_v brand_name from_expr =>
              NRAEnvMapConcat (NRAEnvMap (NRAEnvUnop (ARec in_v) NRAEnvID)
                                 (NRAEnvUnop AFlatten
                                         (NRAEnvMap
                                            (NRAEnvEither (NRAEnvUnop AColl NRAEnvID)
                                                      (NRAEnvConst (dcoll nil)))
                                            (NRAEnvMap (NRAEnvUnop (ACast (brand_name::nil)) NRAEnvID)
                                                   (nraenv_of_oql from_expr))
                                         )))
                          opacc
          end
      in
      let nraenv_of_from_clause :=
          fold_left nraenv_of_from from_clause (NRAEnvUnop AColl NRAEnvID)
      in
      let nraenv_of_where_clause :=
          match where_clause with
          | OTrue => nraenv_of_from_clause
          | OWhere where_expr =>
            NRAEnvSelect (nraenv_of_oql where_expr) nraenv_of_from_clause
          end
      in
      let nraenv_of_order_clause :=
          match order_clause with
          | ONoOrder => nraenv_of_where_clause
          | OOrderBy e sc => nraenv_of_where_clause
          end
      in
      match select_clause with
      | OSelect select_expr =>
        NRAEnvMap (nraenv_of_oql select_expr) nraenv_of_order_clause
      | OSelectDistinct select_expr =>
        NRAEnvUnop ADistinct (NRAEnvMap (nraenv_of_oql select_expr) nraenv_of_order_clause)
      end
    end.


  (***************************
   * Translation correctness *
   ***************************)
  
  (* Some useful lemmas *)

  Lemma rmap_rec_concat_map_is_map_rec_concat_map a s l1 :
    rmap
      (fun x : data =>
         match x with
         | dunit => None
         | dnat _ => None
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
                                                        
  Lemma flatten_either_is_rmap_either bn l0:
    (olift rflatten
           (olift
              (rmap
                 (fun x : data =>
                    match x with
                    | dunit => None
                    | dnat _ => None
                    | dbool _ => None
                    | dstring _ => None
                    | dcoll _ => None
                    | drec _ => None
                    | dleft dl => Some (dcoll (dl :: nil))
                    | dright _ => Some (dcoll nil)
                    | dbrand _ _ => None
                    | dforeign _ => None
                    end))
              (rmap
                 (fun x : data =>
                    match x with
                    | dunit => None
                    | dnat _ => None
                    | dbool _ => None
                    | dstring _ => None
                    | dcoll _ => None
                    | drec _ => None
                    | dleft _ => None
                    | dright _ => None
                    | dbrand b' _ =>
                      if sub_brands_dec h b' (bn :: nil)
                      then Some (dsome x)
                      else Some dnone
                    | dforeign _ => None
                    end) l0))) =
    oflat_map
      (fun x : data =>
         match x with
         | dunit => None
         | dnat _ => None
         | dbool _ => None
         | dstring _ => None
         | dcoll _ => None
         | drec _ => None
         | dleft _ => None
         | dright _ => None
         | dbrand b' _ =>
           if sub_brands_dec h b' (bn :: nil)
           then Some (x :: nil)
           else Some nil
         | dforeign _ => None
         end) l0.
  Proof.
    induction l0; [reflexivity| ]; simpl.
    destruct a; try reflexivity.
    destruct (sub_brands_dec h b (bn :: nil)); simpl;
    rewrite <- IHl0;
      destruct ((rmap
             (fun x : data =>
              match x with
              | dunit => None
              | dnat _ => None
              | dbool _ => None
              | dstring _ => None
              | dcoll _ => None
              | drec _ => None
              | dleft _ => None
              | dright _ => None
              | dbrand b' _ =>
                  if sub_brands_dec h b' (bn :: nil)
                  then Some (dsome x)
                  else Some dnone
              | dforeign _ => None
              end) l0)); simpl; try reflexivity;
      destruct (rmap
          (fun x : data =>
           match x with
           | dunit => None
           | dnat _ => None
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

  Lemma push_lift_coll_in_rmap l f :
    olift (fun x0 : list oql_env => lift dcoll (rmap f x0)) l =
    lift dcoll (olift (fun x0 : list oql_env => (rmap f x0)) l).
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

  Lemma rmap_orecconcat_rmap_drec s a l0 :
    rmap (fun x : data => orecconcat (drec a) x)
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
    induction l0; [reflexivity|idtac]; simpl.
    rewrite IHl0. reflexivity.
  Qed.


  (*****************************
   * Select clause correctness *
   *****************************)
  
  Lemma nraenv_of_select_expr_correct
        (o:oql_expr) (xenv:data) (env0 : option (list oql_env)) :
    (forall (xenv : data) (env : oql_env),
        oql_interp h constant_env o env =
        (h ⊢ nraenv_of_oql o @ₓ (drec env) ⊣ constant_env; xenv )%nraenv) ->
    olift (fun x0 : list oql_env => lift dcoll (rmap (oql_interp h constant_env o) x0)) env0 =
    olift
      (fun d : data =>
         lift_oncoll
           (fun c1 : list data =>
              lift dcoll
                   (rmap
                      (nraenv_eval h constant_env (nraenv_of_oql o) xenv)
                      c1)) d) (lift (fun x => dcoll (map drec x)) env0).
  Proof.
    intros.
    destruct env0; [|reflexivity]; simpl.
    induction l; simpl; try reflexivity.
    rewrite (H xenv).
    destruct (h ⊢ nraenv_of_oql o @ₓ (drec a) ⊣ constant_env; xenv)%nraenv; simpl;
    [|reflexivity].
    destruct (rmap (oql_interp h constant_env o) l);
      destruct (rmap (nraenv_eval h constant_env (nraenv_of_oql o) xenv)
                     (map drec l)); simpl in *; congruence.
  Qed.


  (***************************
   * From clause correctness *
   ***************************)

  (* first off, prove the one-step used in the fold correctly adds one
     variable and does cartesian product (i.e., MapConcat) *)

  Lemma one_from_fold_step_is_map_concat s o op xenv envs envs0:
    (h ⊢ op @ₓ envs ⊣ constant_env; xenv)%nraenv =
    lift (fun x : list (list (string * data)) => dcoll (map drec x)) envs0 ->
    (forall (xenv0 : data) (env : oql_env),
       oql_interp h constant_env o env =
       (h ⊢ nraenv_of_oql o @ₓ drec env ⊣ constant_env; xenv0)%nraenv) ->
    ((h ⊢ (NRAEnvMapConcat (NRAEnvMap (NRAEnvUnop (ARec s) NRAEnvID) (nraenv_of_oql o)) op) @ₓ envs ⊣ constant_env; xenv)%nraenv =
     lift (fun x : list (list (string * data)) => dcoll (map drec x))
          (match envs0 with
           | Some envl' =>
             env_map_concat s (oql_interp h constant_env o) envl'
           | None => None
           end)).
  Proof.
    intros; simpl.
    unfold nraenv_eval in *; simpl.
    rewrite H; simpl; clear H.
    destruct envs0; [|reflexivity]; simpl.
    induction l; try reflexivity; simpl.
    unfold env_map_concat in *; simpl.
    unfold rmap_concat in *; simpl.
    unfold oomap_concat in *; simpl.
    unfold oenv_map_concat_single in *; simpl.
    rewrite (H0 xenv).
    destruct (RAlgEnv.fun_of_algenv h constant_env
          (algenv_of_nraenv (nraenv_of_oql o)) xenv 
          (drec a))%nraenv;
      try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    autorewrite with alg; simpl.
    unfold omap_concat in *.
    rewrite rmap_orecconcat_rmap_drec.
    destruct ((oflat_map
             (fun a0 : oql_env =>
              match oql_interp h constant_env o a0 with
              | Some (dcoll y) =>
                  Some
                    (env_map_concat_single a0
                       (map (fun x : data => (s, x) :: nil) y))
              | Some _ => None
              | None => None
              end) l)); destruct (oflat_map
             (fun a0 : data =>
              match
                olift
                  (fun d : data =>
                   lift_oncoll
                     (fun c1 : list data =>
                      lift dcoll
                        (rmap
                           (fun x : data => Some (drec ((s, x) :: nil)))
                           c1)) d)
                  (RAlgEnv.fun_of_algenv h constant_env
                  (algenv_of_nraenv (nraenv_of_oql o)) xenv a0)%nraenv
              with
              | Some (dcoll y) => rmap (fun x : data => orecconcat a0 x) y
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
     MapConcat) as well *)

  Lemma one_from_cast_fold_step_is_map_concat_cast s bn o op xenv envs envs0:
    (h ⊢ op @ₓ envs ⊣ constant_env; xenv)%nraenv =
    lift (fun x : list (list (string * data)) => dcoll (map drec x)) envs0 ->
    (forall (xenv0 : data) (env : oql_env),
       oql_interp h constant_env o env =
       (h ⊢ nraenv_of_oql o @ₓ drec env ⊣ constant_env; xenv0)%nraenv) ->
    ((h ⊢ (NRAEnvMapConcat
             (NRAEnvMap
                (NRAEnvUnop (ARec s) NRAEnvID)
                (NRAEnvUnop AFlatten(
                              NRAEnvMap (NRAEnvEither (NRAEnvUnop AColl NRAEnvID)
                                                      (NRAEnvConst (dcoll nil)))
                                        (NRAEnvMap (NRAEnvUnop (ACast (bn :: nil)) NRAEnvID)
                                                   (nraenv_of_oql o))))) op) @ₓ envs
        ⊣ constant_env; xenv)%nraenv
     =
     lift (fun x : list (list (string * data)) => dcoll (map drec x))
          match envs0 with
          | Some envl' =>
            env_map_concat_cast h s bn (oql_interp h constant_env o) envl'
          | None => None
          end).
  Proof.
    intros; simpl.
    unfold nraenv_eval in *; simpl.
    rewrite H; simpl; clear H.
    destruct envs0; [|reflexivity]; simpl.
    induction l; try reflexivity; simpl.
    unfold env_map_concat_cast in *; simpl.
    unfold rmap_concat in *; simpl.
    unfold oomap_concat in *; simpl.
    unfold oenv_map_concat_single_with_cast in *; simpl.
    rewrite (H0 xenv).
    destruct (RAlgEnv.fun_of_algenv h constant_env
          (algenv_of_nraenv (nraenv_of_oql o)) xenv 
          (drec a))%nraenv;
      try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    unfold filter_cast in *; simpl in *.
    autorewrite with alg; simpl.
    rewrite flatten_either_is_rmap_either; simpl.
    assert (           @oflat_map (@data (@foreign_runtime_data fruntime))
             (@data (@foreign_runtime_data fruntime))
             (fun x : @data (@foreign_runtime_data fruntime) =>
              match
                x
                return
                  (option (list (@data (@foreign_runtime_data fruntime))))
              with
              | dunit =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | dnat _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | dbool _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | dstring _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | dcoll _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | drec _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | dleft _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | dright _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              | dbrand b' _ =>
                  match
                    sub_brands_dec h b' (@cons string bn (@nil string))
                    return
                      (option
                         (list (@data (@foreign_runtime_data fruntime))))
                  with
                  | left _ =>
                      @Some
                        (list (@data (@foreign_runtime_data fruntime)))
                        (@cons (@data (@foreign_runtime_data fruntime)) x
                           (@nil (@data (@foreign_runtime_data fruntime))))
                  | right _ =>
                      @Some
                        (list (@data (@foreign_runtime_data fruntime)))
                        (@nil (@data (@foreign_runtime_data fruntime)))
                  end
              | dforeign _ =>
                  @None (list (@data (@foreign_runtime_data fruntime)))
              end) l0 =                (@oflat_map (@data (@foreign_runtime_data fruntime))
                   (@data (@foreign_runtime_data fruntime))
                   (fun x : @data (@foreign_runtime_data fruntime) =>
                    match
                      x
                      return
                        (option
                           (list (@data (@foreign_runtime_data fruntime))))
                    with
                    | dunit =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | dnat _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | dbool _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | dstring _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | dcoll _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | drec _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | dleft _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | dright _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    | dbrand b' _ =>
                        match
                          sub_brands_dec h b'
                            (@cons brand bn (@nil brand))
                          return
                            (option
                               (list
                                  (@data (@foreign_runtime_data fruntime))))
                        with
                        | left _ =>
                            @Some
                              (list
                                 (@data (@foreign_runtime_data fruntime)))
                              (@cons
                                 (@data (@foreign_runtime_data fruntime))
                                 x
                                 (@nil
                                    (@data
                                       (@foreign_runtime_data fruntime))))
                        | right _ =>
                            @Some
                              (list
                                 (@data (@foreign_runtime_data fruntime)))
                              (@nil
                                 (@data (@foreign_runtime_data fruntime)))
                        end
                    | dforeign _ =>
                        @None
                          (list (@data (@foreign_runtime_data fruntime)))
                    end) l0)) by reflexivity.
    rewrite H; clear H.
    destruct (oflat_map
          (fun x : data =>
           match x with
           | dunit => None
           | dnat _ => None
           | dbool _ => None
           | dstring _ => None
           | dcoll _ => None
           | drec _ => None
           | dleft _ => None
           | dright _ => None
           | dbrand b' _ =>
               if sub_brands_dec h b' (bn :: nil)
               then Some (x :: nil)
               else Some nil
           | dforeign _ => None
           end) l0); simpl; try reflexivity.
    autorewrite with alg; simpl.
    unfold env_map_concat_single in *.
    unfold omap_concat in *.
    autorewrite with alg; simpl.
    rewrite rmap_rec_concat_map_is_map_rec_concat_map; simpl.
    destruct ((@oflat_map (@oql_env fruntime) (@oql_env fruntime)
                (fun a : @oql_env fruntime =>
                 match
                   @oql_interp fruntime h constant_env o a
                   return (option (list (@oql_env fruntime)))
                 with
                 | Some d =>
                     match
                       d return (option (list (@oql_env fruntime)))
                     with
                     | dunit => @None (list (@oql_env fruntime))
                     | dnat _ => @None (list (@oql_env fruntime))
                     | dbool _ => @None (list (@oql_env fruntime))
                     | dstring _ => @None (list (@oql_env fruntime))
                     | dcoll y =>
                         match
                           @oflat_map
                             (@data (@foreign_runtime_data fruntime))
                             (@data (@foreign_runtime_data fruntime))
                             (fun
                                x : @data (@foreign_runtime_data fruntime)
                              =>
                              match
                                x
                                return
                                  (option
                                     (list
                                        (@data
                                           (@foreign_runtime_data fruntime))))
                              with
                              | dunit =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | dnat _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | dbool _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | dstring _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | dcoll _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | drec _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | dleft _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | dright _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              | dbrand b' _ =>
                                  match
                                    sub_brands_dec h b'
                                      (@cons string bn (@nil string))
                                    return
                                      (option
                                         (list
                                            (@data
                                               (@foreign_runtime_data
                                                fruntime))))
                                  with
                                  | left _ =>
                                      @Some
                                        (list
                                           (@data
                                              (@foreign_runtime_data
                                                fruntime)))
                                        (@cons
                                           (@data
                                              (@foreign_runtime_data
                                                fruntime)) x
                                           (@nil
                                              (@data
                                                (@foreign_runtime_data
                                                fruntime))))
                                  | right _ =>
                                      @Some
                                        (list
                                           (@data
                                              (@foreign_runtime_data
                                                fruntime)))
                                        (@nil
                                           (@data
                                              (@foreign_runtime_data
                                                fruntime)))
                                  end
                              | dforeign _ =>
                                  @None
                                    (list
                                       (@data
                                          (@foreign_runtime_data fruntime)))
                              end) y
                           return (option (list (@oql_env fruntime)))
                         with
                         | Some y0 =>
                             @Some (list (@oql_env fruntime))
                               (@map
                                  (list
                                     (prod string
                                        (@data
                                           (@foreign_runtime_data fruntime))))
                                  (list
                                     (prod string
                                        (@data
                                           (@foreign_runtime_data fruntime))))
                                  (fun
                                     x : list
                                           (prod string
                                              (@data
                                                (@foreign_runtime_data
                                                fruntime))) =>
                                   @rec_concat_sort string ODT_string
                                     (@data
                                        (@foreign_runtime_data fruntime))
                                     a x)
                                  (@map
                                     (@data
                                        (@foreign_runtime_data fruntime))
                                     (list
                                        (prod string
                                           (@data
                                              (@foreign_runtime_data
                                                fruntime))))
                                     (fun
                                        x : @data
                                              (@foreign_runtime_data
                                                fruntime) =>
                                      @cons
                                        (prod string
                                           (@data
                                              (@foreign_runtime_data
                                                fruntime)))
                                        (@pair string
                                           (@data
                                              (@foreign_runtime_data
                                                fruntime)) s x)
                                        (@nil
                                           (prod string
                                              (@data
                                                (@foreign_runtime_data
                                                fruntime))))) y0))
                         | None => @None (list (@oql_env fruntime))
                         end
                     | drec _ => @None (list (@oql_env fruntime))
                     | dleft _ => @None (list (@oql_env fruntime))
                     | dright _ => @None (list (@oql_env fruntime))
                     | dbrand _ _ => @None (list (@oql_env fruntime))
                     | dforeign _ => @None (list (@oql_env fruntime))
                     end
                 | None => @None (list (@oql_env fruntime))
                 end) l)); simpl in *.
    - destruct (          (oflat_map
             (fun a : data =>
              match
                olift
                  (fun d : data =>
                   lift_oncoll
                     (fun c1 : list data =>
                      lift dcoll
                        (rmap
                           (fun x : data => Some (drec ((s, x) :: nil)))
                           c1)) d)
                  (olift
                     (fun d1 : data =>
                      lift_oncoll
                        (fun l : list data => lift dcoll (rflatten l)) d1)
                     (olift
                        (fun d : data =>
                         lift_oncoll
                           (fun c1 : list data =>
                            lift dcoll
                              (rmap
                                 (fun x : data =>
                                  match x with
                                  | dunit => None
                                  | dnat _ => None
                                  | dbool _ => None
                                  | dstring _ => None
                                  | dcoll _ => None
                                  | drec _ => None
                                  | dleft dl => Some (dcoll (dl :: nil))
                                  | dright _ => Some (dcoll nil)
                                  | dbrand _ _ => None
                                  | dforeign _ => None
                                  end) c1)) d)
                        (olift
                           (fun d : data =>
                            lift_oncoll
                              (fun c1 : list data =>
                               lift dcoll
                                 (rmap
                                    (fun x : data =>
                                     match x with
                                     | dunit => None
                                     | dnat _ => None
                                     | dbool _ => None
                                     | dstring _ => None
                                     | dcoll _ => None
                                     | drec _ => None
                                     | dleft _ => None
                                     | dright _ => None
                                     | dbrand b' _ =>
                                         if
                                          sub_brands_dec h b' (bn :: nil)
                                         then Some (dsome x)
                                         else Some dnone
                                     | dforeign _ => None
                                     end) c1)) d)
                           (RAlgEnv.fun_of_algenv h constant_env
                              (algenv_of_nraenv (nraenv_of_oql o)) xenv a)%nraenv)))
              with
              | Some dunit => None
              | Some (dnat _) => None
              | Some (dbool _) => None
              | Some (dstring _) => None
              | Some (dcoll y) => rmap (fun x : data => orecconcat a x) y
              | Some (drec _) => None
              | Some (dleft _) => None
              | Some (dright _) => None
              | Some (dbrand _ _) => None
              | Some (dforeign _) => None
              | None => None
              end) (map drec l))); simpl in *; try congruence.
      inversion IHl; clear IHl.
      subst; simpl.
      rewrite map_map_drec_works.
      reflexivity.
    - destruct
        ((oflat_map
            (fun a : data =>
               match
                 olift
                   (fun d : data =>
                      lift_oncoll
                        (fun c1 : list data =>
                           lift dcoll
                                (rmap
                                   (fun x : data => Some (drec ((s, x) :: nil)))
                                   c1)) d)
                   (olift
                      (fun d1 : data =>
                         lift_oncoll
                           (fun l : list data => lift dcoll (rflatten l)) d1)
                      (olift
                         (fun d : data =>
                            lift_oncoll
                              (fun c1 : list data =>
                                 lift dcoll
                                      (rmap
                                         (fun x : data =>
                                            match x with
                                            | dunit => None
                                            | dnat _ => None
                                            | dbool _ => None
                                            | dstring _ => None
                                            | dcoll _ => None
                                            | drec _ => None
                                            | dleft dl => Some (dcoll (dl :: nil))
                                            | dright _ => Some (dcoll nil)
                                            | dbrand _ _ => None
                                            | dforeign _ => None
                                            end) c1)) d)
                         (olift
                            (fun d : data =>
                               lift_oncoll
                                 (fun c1 : list data =>
                                    lift dcoll
                                         (rmap
                                            (fun x : data =>
                                               match x with
                                               | dunit => None
                                               | dnat _ => None
                                               | dbool _ => None
                                               | dstring _ => None
                                               | dcoll _ => None
                                               | drec _ => None
                                               | dleft _ => None
                                               | dright _ => None
                                               | dbrand b' _ =>
                                                 if
                                                   sub_brands_dec h b' (bn :: nil)
                                                 then Some (dsome x)
                                                 else Some dnone
                                               | dforeign _ => None
                                               end) c1)) d)
                            (RAlgEnv.fun_of_algenv h constant_env
                              (algenv_of_nraenv (nraenv_of_oql o)) xenv a))))
               with
               | Some dunit => None
               | Some (dnat _) => None
               | Some (dbool _) => None
               | Some (dstring _) => None
               | Some (dcoll y) => rmap (fun x : data => orecconcat a x) y
               | Some (drec _) => None
               | Some (dleft _) => None
               | Some (dright _) => None
               | Some (dbrand _ _) => None
               | Some (dforeign _) => None
               | None => None
               end) (map drec l))); simpl in *; [congruence|reflexivity].
  Qed.

  (* Second, show that 'x in expr' translation is correct *)
  
  Lemma nraenv_of_from_in_correct env o s xenv :
    (forall (xenv0 : data) (env0 : oql_env),
        oql_interp h constant_env o env0 =
        (h ⊢ nraenv_of_oql o @ₓ drec env0 ⊣ constant_env; xenv0)%nraenv) ->
    (lift (fun x : list (list (string * data)) => dcoll (map drec x))
          (env_map_concat s (oql_interp h constant_env o) (env :: nil))) =
    (nraenv_eval h constant_env (NRAEnvMapConcat (NRAEnvMap (NRAEnvUnop (ARec s) NRAEnvID) (nraenv_of_oql o)) (NRAEnvUnop AColl NRAEnvID)) xenv (drec env)).
  Proof.
    intros; simpl.
    unfold nraenv_eval; simpl.
    unfold rmap_concat; simpl.
    unfold env_map_concat; simpl.
    unfold oomap_concat; simpl.
    unfold oenv_map_concat_single; simpl.
    rewrite (H xenv); clear H.
    unfold nraenv_eval; simpl.
    destruct (RAlgEnv.fun_of_algenv h constant_env
          (algenv_of_nraenv (nraenv_of_oql o)) xenv 
          (drec env))%nraenv;
      try reflexivity; simpl.
    destruct d; simpl; try reflexivity.
    autorewrite with alg; simpl.
    rewrite app_nil_r.
    apply oql_nra_dual_map_concat.
  Qed.

  (* Finally, the main fold_left for a whole from clause is correct *)
  
  Lemma nraenv_of_from_clause_correct op envs envs0 el xenv :
    Forall
      (fun ab : oql_in_expr =>
         forall (xenv : data) (env : oql_env),
           oql_interp h constant_env (oin_expr ab) env =
           (h ⊢ nraenv_of_oql (oin_expr ab) @ₓ drec env ⊣ constant_env;
             xenv)%nraenv) el ->
    (h ⊢ op @ₓ envs ⊣ constant_env; xenv)%nraenv =
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
              env_map_concat in_v (oql_interp h constant_env from_expr) envl'
            end
          | OInCast in_v brand_name from_expr =>
            match envl with
            | None => None
            | Some envl' =>
              env_map_concat_cast h in_v brand_name (oql_interp h constant_env from_expr) envl'
            end
          end
             ) el envs0)) =
    (h
       ⊢ fold_left
       (fun (opacc : nraenv) (from_in_expr : oql_in_expr) =>
          match from_in_expr with
          | OIn in_v from_expr =>
            NRAEnvMapConcat
              (NRAEnvMap (NRAEnvUnop (ARec in_v) NRAEnvID) (nraenv_of_oql from_expr))
              opacc
          | OInCast in_v brand_name from_expr =>
            NRAEnvMapConcat
              (NRAEnvMap
                 (NRAEnvUnop (ARec in_v) NRAEnvID)
                 (NRAEnvUnop AFlatten
                             (NRAEnvMap (NRAEnvEither (NRAEnvUnop AColl NRAEnvID)
                                                      (NRAEnvConst (dcoll nil)))
                                        (NRAEnvMap (NRAEnvUnop (ACast (brand_name::nil))
                                                               NRAEnvID)
                                                   (nraenv_of_oql from_expr)))))
              opacc
          end
       )
       el op @ₓ envs ⊣ constant_env; xenv)%nraenv.
  Proof.
    intros.
    revert op xenv envs0 envs H0.
    induction el; simpl in *; intros; try (rewrite H0; reflexivity).
    destruct a; simpl in *.
    (* OIn case *)
    - inversion H; subst; simpl in *.
      specialize (IHel H4); clear H H4.
      specialize (IHel (NRAEnvMapConcat
                          (NRAEnvMap (NRAEnvUnop (ARec s) NRAEnvID)
                                     (nraenv_of_oql o)) op)%nraenv).
      assert ((h ⊢ (NRAEnvMapConcat
                      (NRAEnvMap (NRAEnvUnop (ARec s) NRAEnvID)
                                 (nraenv_of_oql o)) op)%nraenv
                 @ₓ envs ⊣ constant_env; xenv)%nraenv =
              lift (fun x : list (list (string * data)) => dcoll (map drec x))
                   (match envs0 with
                    | Some envl' =>
                      env_map_concat s (oql_interp h constant_env o) envl'
                    | None => None
                    end))
        by (apply one_from_fold_step_is_map_concat; assumption).
      apply (IHel xenv (match envs0 with
                        | Some envl' =>
                          env_map_concat s (oql_interp h constant_env o) envl'
                        | None => None
                        end) envs H).
    (* OInCast case *)
    - inversion H; subst; simpl in *.
      specialize (IHel H4); clear H H4.
      specialize
        (IHel (NRAEnvMapConcat
                 (NRAEnvMap
                    (NRAEnvUnop (ARec s) NRAEnvID)
                    (NRAEnvUnop AFlatten
                                (NRAEnvMap
                                   (NRAEnvEither (NRAEnvUnop AColl NRAEnvID)
                                                 (NRAEnvConst (dcoll nil)))
                                   (NRAEnvMap (NRAEnvUnop (ACast (s0 :: nil)) NRAEnvID)
                                              (nraenv_of_oql o))))) (op))%nraenv).
      assert ((h ⊢ (NRAEnvMapConcat
                 (NRAEnvMap
                    (NRAEnvUnop (ARec s) NRAEnvID)
                    (NRAEnvUnop AFlatten
                                (NRAEnvMap
                                   (NRAEnvEither (NRAEnvUnop AColl NRAEnvID)
                                                 (NRAEnvConst (dcoll nil)))
                                   (NRAEnvMap (NRAEnvUnop (ACast (s0 :: nil)) NRAEnvID)
                                              (nraenv_of_oql o))))) (op)) @ₓ envs
                 ⊣ constant_env; xenv)%nraenv
              =
              lift (fun x : list (list (string * data)) => dcoll (map drec x))
                   match envs0 with
                   | Some envl' =>
                     env_map_concat_cast h s s0 (oql_interp h constant_env o) envl'
                   | None => None
                   end)
        by (apply one_from_cast_fold_step_is_map_concat_cast; assumption).
      apply (IHel xenv (match envs0 with
                        | Some envl' =>
                          env_map_concat_cast h s s0 (oql_interp h constant_env o) envl'
                        | None => None
                        end) envs H).
  Qed.

  (****************************
   * Where clause correctness *
   ****************************)
  
  Lemma nraenv_of_where_clause_correct
        (o:oql_expr) (xenv:data) (ol : option (list oql_env)):
    (forall (xenv : data) (env : oql_env),
        oql_interp h constant_env o env =
        (h ⊢ nraenv_of_oql o @ₓ drec env ⊣ constant_env; xenv)%nraenv) ->
    lift (fun x : list (list (string * data)) => dcoll (map drec x))
         (olift
            (lift_filter
               (fun x' : oql_env =>
                  match oql_interp h constant_env o x' with
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
                           (h ⊢ nraenv_of_oql o @ₓ x' ⊣ constant_env; xenv)%nraenv
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
    destruct (h ⊢ nraenv_of_oql o @ₓ drec a ⊣ constant_env; xenv)%nraenv; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct (lift_filter
             (fun x' : data =>
              match
                (h ⊢ nraenv_of_oql o @ₓ x' ⊣ constant_env; xenv)%nraenv
              with
              | Some (dbool b0) => Some b0
              | Some _ => None
              | None => None
              end) (map drec l)); destruct ((lift_filter
             (fun x' : oql_env =>
              match oql_interp h constant_env o x' with
              | Some (dbool b) => Some b
              | Some _ => None
              | None => None
              end) l)); simpl in *; try congruence.
    inversion IHl; subst.
    destruct b; reflexivity.
  Qed.

  (* Main theorem: OQL to NRAEnv translation is correct *)
  
  Theorem nraenv_of_oql_correct (e:oql_expr) :
    forall xenv:data, forall env:oql_env,
        oql_interp h constant_env e env =
        nraenv_eval h constant_env (nraenv_of_oql e) xenv (drec env).
  Proof.
    intros. revert xenv env.
    induction e; simpl; intros.
    (* OConst *)
    - reflexivity.
    (* OVar *)
    - reflexivity.
    (* OTable *)
    - reflexivity.
    (* OBinop *)
    - rewrite (IHe1 xenv env); rewrite (IHe2 xenv env).
      reflexivity.
    (* OUnop *)
    - rewrite (IHe xenv env).
      reflexivity.
    (* OSFW *)
    - destruct e1.
      + simpl in *.
        generalize nraenv_of_from_clause_correct; intros Hfrom.
        unfold nraenv_eval in *; simpl.
        rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
        generalize nraenv_of_select_expr_correct; intros Hselect.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hselect; [|assumption].
        reflexivity.
      + simpl in *.
        generalize nraenv_of_from_clause_correct; intros Hfrom.
        unfold nraenv_eval in *; simpl.
        rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
        generalize nraenv_of_select_expr_correct; intros Hselect.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hselect; [|assumption].
        rewrite push_lift_coll_in_rmap; simpl.
        rewrite olift_rondcoll_over_dcoll.
        reflexivity.
    - destruct e1.
      + simpl in *.
        generalize nraenv_of_from_clause_correct; intros Hfrom.
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
        generalize nraenv_of_from_clause_correct; intros Hfrom.
        unfold nraenv_eval in *; simpl.
        rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
        generalize nraenv_of_where_clause_correct; intros Hwhere.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hwhere; [|assumption].
        generalize nraenv_of_select_expr_correct; intros Hselect.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hselect; [|assumption].
        rewrite push_lift_coll_in_rmap; simpl.
        rewrite olift_rondcoll_over_dcoll.
        reflexivity.
    - destruct e1.
      + simpl in *.
        generalize nraenv_of_from_clause_correct; intros Hfrom.
        unfold nraenv_eval in *; simpl.
        rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
        generalize nraenv_of_select_expr_correct; intros Hselect.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hselect; [|assumption].
        reflexivity.
      + simpl in *.
        generalize nraenv_of_from_clause_correct; intros Hfrom.
        unfold nraenv_eval in *; simpl.
        rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
        generalize nraenv_of_select_expr_correct; intros Hselect.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hselect; [|assumption].
        rewrite push_lift_coll_in_rmap; simpl.
        rewrite olift_rondcoll_over_dcoll.
        reflexivity.
    - destruct e1.
      + simpl in *.
        generalize nraenv_of_from_clause_correct; intros Hfrom.
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
        generalize nraenv_of_from_clause_correct; intros Hfrom.
        unfold nraenv_eval in *; simpl.
        rewrite <- (Hfrom _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity]. 
        generalize nraenv_of_where_clause_correct; intros Hwhere.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hwhere; [|assumption].
        generalize nraenv_of_select_expr_correct; intros Hselect.
        unfold nraenv_eval in *; simpl.
        rewrite <- Hselect; [|assumption].
        rewrite push_lift_coll_in_rmap; simpl.
        rewrite olift_rondcoll_over_dcoll.
        reflexivity.
  Qed.

  (* Top-level translation call *)

  Definition translate_oql_to_nraenv (e:oql_expr) : nraenv :=
    (* Produces the initial plan *)
    NRAEnvApp (nraenv_of_oql e) (NRAEnvConst (drec nil)).

  (********************************************
   * Additional properties of the translation *
   ********************************************)
  
  (* OQL to NRAEnv translation is local env-free *)

  (* For fold_left, make sure to do the induction on el for *any* accumulator *)
  Lemma fold_left_ignore_env (el:list oql_in_expr) (a:nraenv) :
    nraenv_ignores_env a ->
    Forall (fun ab : oql_in_expr => nraenv_ignores_env (nraenv_of_oql (oin_expr ab))) el ->
    nraenv_ignores_env
      (fold_left
         (fun (opacc : nraenv) (from_in_expr : oql_in_expr) =>
            match from_in_expr with
            | OIn in_v from_expr =>
              (NRAEnvMapConcat
                 (NRAEnvMap
                    (NRAEnvUnop (ARec in_v) NRAEnvID)
                    (nraenv_of_oql from_expr)) opacc)%nraenv
            | OInCast in_v brand_name from_expr =>
             (NRAEnvMapConcat
                (NRAEnvMap (NRAEnvUnop (ARec in_v) NRAEnvID)
                           (NRAEnvUnop AFlatten
                                       (NRAEnvMap
                                          (NRAEnvEither (NRAEnvUnop AColl NRAEnvID)
                                                        (NRAEnvConst (dcoll nil)))
                                          (NRAEnvMap
                                             (NRAEnvUnop (ACast (brand_name::nil)) NRAEnvID)
                                             (nraenv_of_oql from_expr))))) opacc)%nraenv
            end)
         el a).
  Proof.
    intros.
    revert a H.
    induction el; simpl; intros; try assumption.
    inversion H0; clear H0; subst.
    specialize (IHel H4); clear H4.
    destruct a; simpl in *.
    - apply IHel.
      unfold nraenv_ignores_env.
      simpl; auto.
    - apply IHel.
      unfold nraenv_ignores_env.
      simpl; auto.
  Qed.

  Lemma oql_to_nraenv_ignores_env (e:oql_expr) :
    nraenv_ignores_env (nraenv_of_oql e).
  Proof.
    induction e; simpl;
    unfold nraenv_ignores_env; simpl;
    auto;
    destruct e1;
    simpl in *;
    repeat (split; auto);
    apply fold_left_ignore_env; unfold nraenv_ignores_env;
    simpl; auto.
  Qed.

End OQLtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
