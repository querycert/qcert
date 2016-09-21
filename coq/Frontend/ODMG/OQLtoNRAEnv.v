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
  Require Import RAlgEnv.

  Context {fruntime:foreign_runtime}.

  Context (h:list(string*string)).
  Context (constant_env:list (string*data)).


  (*****************************
   * OQL to NRAEnv translation *
   *****************************)
  
  Fixpoint algenv_of_oql (e:oql_expr) : algenv :=
    match e with
    | OConst d => ANConst d
    | OVar v => ANUnop (ADot v) ANID
    | OTable t => ANGetConstant t
    | OBinop b e1 e2 => ANBinop b (algenv_of_oql e1) (algenv_of_oql e2)
    | OUnop u e1 => ANUnop u (algenv_of_oql e1)
    | OSFW select_clause from_clause where_clause =>
      let algenv_of_from (opacc:algenv) (from_in_expr : oql_in_expr) :=
          let (in_v, from_expr) := from_in_expr in
          ANMapConcat (ANMap (ANUnop (ARec in_v) ANID) (algenv_of_oql from_expr)) opacc
      in
      let algenv_of_from_clause :=
          fold_left algenv_of_from from_clause (ANUnop AColl ANID)
      in
      let algenv_of_where_clause :=
          match where_clause with
          | OTrue => algenv_of_from_clause
          | OWhere where_expr =>
            ANSelect (algenv_of_oql where_expr) algenv_of_from_clause
          end
      in
      match select_clause with
      | OSelect select_expr =>
        ANMap (algenv_of_oql select_expr) algenv_of_where_clause
      | OSelectDistinct select_expr =>
        ANUnop ADistinct (ANMap (algenv_of_oql select_expr) algenv_of_where_clause)
      end
    end.


  (***************************
   * Translation correctness *
   ***************************)
  
  (* Some useful lemmas *)

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
  
  Lemma algenv_of_select_expr_correct
        (o:oql_expr) (xenv:data) (env0 : option (list oql_env)) :
    (forall (xenv : data) (env : oql_env),
        oql_interp h constant_env o env =
        (h ⊢ₑ algenv_of_oql o @ₑ (drec env) ⊣ constant_env; xenv )%algenv) ->
    olift (fun x0 : list oql_env => lift dcoll (rmap (oql_interp h constant_env o) x0)) env0 =
    olift
      (fun d : data =>
         lift_oncoll
           (fun c1 : list data =>
              lift dcoll
                   (rmap
                      (fun_of_algenv h constant_env (algenv_of_oql o) xenv)
                      c1)) d) (lift (fun x => dcoll (map drec x)) env0).
  Proof.
    intros.
    destruct env0; [|reflexivity]; simpl.
    induction l; simpl; try reflexivity.
    rewrite (H xenv).
    destruct (h ⊢ₑ algenv_of_oql o @ₑ (drec a) ⊣ constant_env; xenv)%algenv; simpl;
    [|reflexivity].
    destruct (rmap (oql_interp h constant_env o) l);
      destruct (rmap (fun_of_algenv h constant_env (algenv_of_oql o) xenv)
                     (map drec l)); simpl in *; congruence.
  Qed.


  (***************************
   * From clause correctness *
   ***************************)

  (* first off, prove the one-step used in the fold correctly adds one
     variable and does cartesian product (i.e., MapReduce) *)

  Lemma one_from_fold_step_is_map_concat s o op xenv envs envs0:
    (h ⊢ₑ op @ₑ envs ⊣ constant_env; xenv)%algenv =
    lift (fun x : list (list (string * data)) => dcoll (map drec x)) envs0 ->
    (forall (xenv0 : data) (env : oql_env),
       oql_interp h constant_env o env =
       (h ⊢ₑ algenv_of_oql o @ₑ drec env ⊣ constant_env; xenv0)%algenv) ->
    ((h ⊢ₑ (⋈ᵈ⟨χ⟨‵[| (s, ID)|] ⟩( algenv_of_oql o) ⟩( op))%algenv
        @ₑ envs ⊣ constant_env; xenv)%algenv =
     lift (fun x : list (list (string * data)) => dcoll (map drec x))
          (match envs0 with
           | Some envl' =>
             env_map_concat s (oql_interp h constant_env o) envl'
           | None => None
           end)).
  Proof.
    intros; simpl.
    rewrite H; simpl; clear H.
    destruct envs0; [|reflexivity]; simpl.
    induction l; try reflexivity; simpl.
    unfold env_map_concat in *; simpl.
    unfold rmap_concat in *; simpl.
    unfold oomap_concat in *; simpl.
    unfold oenv_map_concat_single in *; simpl.
    rewrite (H0 xenv).
    destruct (h ⊢ₑ algenv_of_oql o @ₑ drec a ⊣ constant_env; xenv)%algenv;
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
                  (h ⊢ₑ algenv_of_oql o @ₑ a0 ⊣ constant_env; xenv)%algenv
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

  (* Second, show that 'x in expr' translation is correct *)
  
  Lemma algenv_of_from_in_correct env o s xenv :
    (forall (xenv0 : data) (env0 : oql_env),
        oql_interp h constant_env o env0 =
        (h ⊢ₑ algenv_of_oql o @ₑ drec env0 ⊣ constant_env; xenv0)%algenv) ->
    (lift (fun x : list (list (string * data)) => dcoll (map drec x))
          (env_map_concat s (oql_interp h constant_env o) (env :: nil))) =
    (fun_of_algenv h constant_env (ANMapConcat (ANMap (ANUnop (ARec s) ANID) (algenv_of_oql o)) (ANUnop AColl ANID)) xenv (drec env)).
  Proof.
    intros; simpl.
    unfold rmap_concat; simpl.
    unfold env_map_concat; simpl.
    unfold oomap_concat; simpl.
    unfold oenv_map_concat_single; simpl.
    rewrite (H xenv); clear H.
    destruct (h ⊢ₑ algenv_of_oql o @ₑ drec env ⊣ constant_env; xenv)%algenv;
      try reflexivity; simpl.
    destruct d; simpl; try reflexivity.
    autorewrite with alg; simpl.
    rewrite app_nil_r.
    apply oql_nra_dual_map_concat.
  Qed.

  (* Finally, the main fold_left for a whole from clause is correct *)
  
  Lemma algenv_of_from_clause_correct op envs envs0 el xenv :
    Forall
      (fun ab : oql_in_expr =>
         forall (xenv : data) (env : oql_env),
           oql_interp h constant_env (oin_expr ab) env =
           (h ⊢ₑ algenv_of_oql (oin_expr ab) @ₑ drec env ⊣ constant_env;
             xenv)%algenv) el ->
    (h ⊢ₑ op @ₑ envs ⊣ constant_env; xenv)%algenv =
    (lift (fun x : list (list (string * data)) => dcoll (map drec x)) envs0) ->
    (lift (fun x : list (list (string * data)) => dcoll (map drec x))
          (fold_left
             (fun (envl : option (list oql_env))
                  (from_in_expr : oql_in_expr) =>
                let (in_v, from_expr) := from_in_expr in
                match envl with
                | Some envl' =>
                  env_map_concat in_v (oql_interp h constant_env from_expr) envl'
                | None => None
                end) el envs0)) =
    (h
       ⊢ₑ fold_left
       (fun (opacc : algenv) (from_in_expr : oql_in_expr) =>
          let (in_v, from_expr) := from_in_expr in
          ⋈ᵈ⟨χ⟨‵[| (in_v, ID)|] ⟩( algenv_of_oql from_expr) ⟩(opacc))
       el op @ₑ envs ⊣ constant_env; xenv)%algenv.
  Proof.
    intros.
    revert op xenv envs0 envs H0.
    induction el; simpl in *; intros; try (rewrite H0; reflexivity).
    destruct a; simpl in *.
    inversion H; subst; simpl in *.
    specialize (IHel H4); clear H H4.
    specialize (IHel (⋈ᵈ⟨χ⟨‵[| (s, ID)|] ⟩( algenv_of_oql o) ⟩( op))%algenv).
    assert ((h ⊢ₑ (⋈ᵈ⟨χ⟨‵[| (s, ID)|] ⟩( algenv_of_oql o) ⟩( op))%algenv
               @ₑ envs ⊣ constant_env; xenv)%algenv =
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
  Qed.


  (****************************
   * Where clause correctness *
   ****************************)
  
  Lemma algenv_of_where_clause_correct
        (o:oql_expr) (xenv:data) (ol : option (list oql_env)):
    (forall (xenv : data) (env : oql_env),
        oql_interp h constant_env o env =
        (h ⊢ₑ algenv_of_oql o @ₑ drec env ⊣ constant_env; xenv)%algenv) ->
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
                           (h ⊢ₑ algenv_of_oql o @ₑ x' ⊣ constant_env; xenv)%algenv
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
    destruct (h ⊢ₑ algenv_of_oql o @ₑ drec a ⊣ constant_env; xenv)%algenv; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct (lift_filter
             (fun x' : data =>
              match
                (h ⊢ₑ algenv_of_oql o @ₑ x' ⊣ constant_env; xenv)%algenv
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
  
  Theorem algenv_of_oql_correct (e:oql_expr) :
    forall xenv:data, forall env:oql_env,
        oql_interp h constant_env e env =
        fun_of_algenv h constant_env (algenv_of_oql e) xenv (drec env).
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
        rewrite <- (algenv_of_from_clause_correct _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
        rewrite <- algenv_of_select_expr_correct; [|assumption].
        reflexivity.
      + simpl in *.
        rewrite <- (algenv_of_from_clause_correct _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
        rewrite <- algenv_of_select_expr_correct; [|assumption].
        rewrite push_lift_coll_in_rmap; simpl.
        rewrite olift_rondcoll_over_dcoll.
        reflexivity.
    - destruct e1.
      + simpl in *.
        rewrite <- (algenv_of_from_clause_correct _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
        rewrite <- algenv_of_where_clause_correct; [|assumption].
        rewrite <- algenv_of_select_expr_correct; [|assumption].
        reflexivity.
      + simpl in *.
        rewrite <- (algenv_of_from_clause_correct _ _ (Some (env :: nil))) ; [idtac|assumption|reflexivity].
        rewrite <- algenv_of_where_clause_correct; [|assumption].
        rewrite <- algenv_of_select_expr_correct; [|assumption].
        rewrite push_lift_coll_in_rmap; simpl.
        rewrite olift_rondcoll_over_dcoll.
        reflexivity.
  Qed.

  (* Top-level translation call *)

  Definition translate_oql_to_algenv (e:oql_expr) : algenv :=
    (* Produces the initial plan *)
    ANApp (algenv_of_oql e) (ANConst (drec nil)).

  (********************************************
   * Additional properties of the translation *
   ********************************************)
  
  (* OQL to NRAEnv translation is local env-free *)

  Require Import RAlgEnvIgnore.

  (* For fold_left, make sure to do the induction on el for *any* accumulator *)
  Lemma fold_left_ignore_env (el:list oql_in_expr) (a:algenv) :
    ignores_env a ->
    Forall (fun ab : oql_in_expr => ignores_env (algenv_of_oql (oin_expr ab))) el ->
    ignores_env
      (fold_left
         (fun (opacc : algenv) (from_in_expr : oql_in_expr) =>
            let (in_v, from_expr) := from_in_expr in
            (⋈ᵈ⟨χ⟨‵[| (in_v, ID)|] ⟩( algenv_of_oql from_expr) ⟩( opacc))%algenv)
         el a).
  Proof.
    intros.
    revert a H.
    induction el; simpl; intros; try assumption.
    inversion H0; clear H0; subst.
    specialize (IHel H4); clear H4.
    destruct a; simpl in *.
    apply IHel.
    simpl; auto.
  Qed.
    
  Lemma oql_to_nraenv_ignores_env (e:oql_expr) :
    ignores_env (algenv_of_oql e).
  Proof.
    induction e; simpl; auto;
    destruct e1;
    simpl in *;
    repeat (split; auto);
    apply fold_left_ignore_env; simpl; auto.
  Qed.

End OQLtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
