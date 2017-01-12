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

Section cNRAEnv.
  Require Import String List Compare_dec.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.

  (** Nested Relational Algebra *)

  (** By convention, "static" parameters come first, followed by
     dependent operators. This allows for instanciation on those
     parameters *)

  Context {fruntime:foreign_runtime}.

  Inductive cnraenv : Set :=
  | ANID : cnraenv
  | ANConst : data -> cnraenv
  | ANBinop : binOp -> cnraenv -> cnraenv -> cnraenv
  | ANUnop : unaryOp -> cnraenv -> cnraenv
  | ANMap : cnraenv -> cnraenv -> cnraenv
  | ANMapConcat : cnraenv -> cnraenv -> cnraenv
  | ANProduct : cnraenv -> cnraenv -> cnraenv
  | ANSelect : cnraenv -> cnraenv -> cnraenv
  | ANDefault : cnraenv -> cnraenv -> cnraenv
  | ANEither :  cnraenv -> cnraenv -> cnraenv
  | ANEitherConcat :  cnraenv -> cnraenv -> cnraenv
  | ANApp : cnraenv -> cnraenv -> cnraenv
  | ANGetConstant : string -> cnraenv
  | ANEnv : cnraenv
  | ANAppEnv : cnraenv -> cnraenv -> cnraenv
  | ANMapEnv : cnraenv -> cnraenv
  .

  Tactic Notation "cnraenv_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANID"%string
  | Case_aux c "ANConst"%string
  | Case_aux c "ANBinop"%string
  | Case_aux c "ANUnop"%string
  | Case_aux c "ANMap"%string
  | Case_aux c "ANMapConcat"%string
  | Case_aux c "ANProduct"%string
  | Case_aux c "ANSelect"%string
  | Case_aux c "ANDefault"%string
  | Case_aux c "ANEither"%string
  | Case_aux c "ANEitherConcat"%string
  | Case_aux c "ANApp"%string
  | Case_aux c "ANGetConstant"%string
  | Case_aux c "ANEnv"%string
  | Case_aux c "ANAppEnv"%string
  | Case_aux c "ANMapEnv"%string].
  
  Global Instance cnraenv_eqdec : EqDec cnraenv eq.
  Proof.
    change (forall x y : cnraenv,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binOp_eqdec | apply unaryOp_eqdec | apply data_eqdec | apply string_eqdec].
  Defined.

  (** NRA+Env Semantics *)

  Context (h:list(string*string)).
  Context (constant_env:list (string*data)).
  Fixpoint cnraenv_eval (op:cnraenv) (env: data) (x:data) : option data :=
    match op with
      | ANID => Some x
      | ANConst rd => Some (normalize_data h rd)
      | ANBinop bop op1 op2 =>
        olift2 (fun d1 d2 => fun_of_binop h bop d1 d2) (cnraenv_eval op1 env x) (cnraenv_eval op2 env x)
      | ANUnop uop op1 =>
        olift (fun d1 => fun_of_unaryop h uop d1) (cnraenv_eval op1 env x)
      | ANMap op1 op2 =>
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (cnraenv_eval op1 env) c1)) d
        in olift aux_map (cnraenv_eval op2 env x)
      | ANMapConcat op1 op2 =>
        let aux_mapconcat d :=
            lift_oncoll (fun c1 => lift dcoll (rmap_concat (cnraenv_eval op1 env) c1)) d
        in olift aux_mapconcat (cnraenv_eval op2 env x)
      | ANProduct op1 op2 =>
        (* Note: (fun y => cnraenv_eval op2 x) does not depend on input,
           but we still use a nested look and delay op2 evaluation so it does not
           fail in case the op1 operand is an empty collection -- this makes sure
           to align the semantics with the NNRC version. - Jerome *)
        let aux_product d :=
            lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => cnraenv_eval op2 env x) c1)) d
        in olift aux_product (cnraenv_eval op1 env x)
      | ANSelect op1 op2 =>
        let pred x' :=
            match cnraenv_eval op1 env x' with
              | Some (dbool b) => Some b
              | _ => None
            end
        in
        let aux_select d :=
            lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
        in
        olift aux_select (cnraenv_eval op2 env x)
      | ANEither opl opr =>
        match x with
          | dleft dl => cnraenv_eval opl env dl
          | dright dr => cnraenv_eval opr env dr
          | _ => None
        end
      | ANEitherConcat op1 op2 =>
        match cnraenv_eval op1 env x, cnraenv_eval op2 env x with
          | Some (dleft (drec l)), Some (drec t)  =>
            Some (dleft (drec (rec_concat_sort l t)))
          | Some (dright (drec r)), Some (drec t)  =>
            Some (dright (drec (rec_concat_sort r t)))
          | _, _ => None
        end
      | ANDefault op1 op2 =>
        olift (fun d1 => match d1 with
                               | dcoll nil => cnraenv_eval op2 env x
                               | _ => Some d1
                         end) (cnraenv_eval op1 env x)
      | ANApp op2 op1 =>
        olift (fun x' => cnraenv_eval op2 env x') (cnraenv_eval op1 env x)
      | ANGetConstant s => edot constant_env s
      | ANEnv => (Some env)
      | ANAppEnv op2 op1 =>
        (* Note: evaluate op1 to create a new environment;
                 evaluate op2 in that new environment *)
        (* This is the parallel to AApp, but for the environment *)
        olift (fun env' => cnraenv_eval op2 env' x) (cnraenv_eval op1 env x)
      | ANMapEnv op1 =>
        lift_oncoll (fun c1 => lift dcoll (rmap ((fun env' => cnraenv_eval op1 env' x)) c1)) env
    end.

  (** Functions used to map dual input env/data into single input *)
  (* Input encoding *)

  Require Import NRARuntime.
  Require Import String List RList.
  
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Definition ARecEither f :=
    AEither (AUnop ALeft (AUnop (ARec f) AID)) (AUnop ARight (AUnop (ARec f) AID)).
  
  Fixpoint nra_of_cnraenv (ae:cnraenv) : nra :=
    match ae with
      | ANID => pat_data
      | ANConst d => (AConst d)
      | ANBinop b ae1 ae2 => ABinop b (nra_of_cnraenv ae1) (nra_of_cnraenv ae2)
      | ANUnop u ae1 => AUnop u (nra_of_cnraenv ae1)
      | ANMap ea1 ea2 =>
        AMap (nra_of_cnraenv ea1)
             (unnest_two
                "a1"
                "PDATA"
                (AUnop AColl (pat_wrap_a1 (nra_of_cnraenv ea2))))
      | ANMapConcat ea1 ea2 =>
        (AMap (ABinop AConcat
                      (AUnop (ADot "PDATA") AID)
                      (AUnop (ADot "PDATA2") AID))
              (AMapConcat
                 (AMap (AUnop (ARec "PDATA2") AID) (nra_of_cnraenv ea1))
                 (unnest_two
                    "a1"
                    "PDATA"
                    (AUnop AColl (pat_wrap_a1 (nra_of_cnraenv ea2))))))
      | ANProduct ea1 ea2 => AProduct (nra_of_cnraenv ea1) (nra_of_cnraenv ea2)
      | ANSelect ea1 ea2 =>
        (AMap (AUnop (ADot "PDATA") AID)
              (ASelect (nra_of_cnraenv ea1)
                       (unnest_two
                          "a1"
                          "PDATA"
                          (AUnop AColl (pat_wrap_a1 (nra_of_cnraenv ea2))))))
      | ANDefault ea1 ea2 => ADefault (nra_of_cnraenv ea1) (nra_of_cnraenv ea2)
      | ANEither eal ear => AApp
                                  (AEither (nra_of_cnraenv eal) (nra_of_cnraenv ear))
                                  (AEitherConcat
                                     (AApp (ARecEither "PDATA") pat_data)
                                     (ABinop AConcat 
                                             (AUnop (ARec "PBIND") pat_bind)
                                             (AUnop (ARec "PCONST") pat_const_env)))
      | ANEitherConcat ea1 ea2 => AEitherConcat (nra_of_cnraenv ea1) (nra_of_cnraenv ea2)
      | ANApp ea1 ea2 => AApp (nra_of_cnraenv ea1) (pat_wrap (nra_of_cnraenv ea2))
      | ANGetConstant s => AUnop (ADot s) pat_const_env 
      | ANEnv => pat_bind
      | ANAppEnv ea1 ea2 =>
        AApp (nra_of_cnraenv ea1)
             (pat_context pat_const_env (nra_of_cnraenv ea2) pat_data)
      | ANMapEnv ea1 =>
        (* fix this: the pat_data should change to a pat_pair *)
        AMap (nra_of_cnraenv ea1)
             (unnest_two
                "a1"
                "PBIND"
                (AUnop AColl (pat_wrap_bind_a1 pat_data)))
    end.

  Lemma rmap_map_rec1 l s:
    rmap (fun x : data => Some (drec ((s, x) :: nil))) l =
    Some (map (fun x : data => (drec ((s, x) :: nil))) l).
  Proof.
    induction l; try reflexivity; simpl; rewrite IHl; reflexivity.
  Qed.

  Lemma rmap_map_rec2 c env a1 l :
    (rmap
       (fun x : data =>
          match x with
            | drec r1 =>
              Some
                (drec
                   (rec_concat_sort
                      (("PBIND", env) :: ("PCONST", c) :: ("a1", dcoll a1) :: nil) r1))
            | _  => None
          end)
       (map (fun x : data => drec (("PDATA", x) :: nil)) l))
    =
    Some (map (fun x : data =>  drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", x) :: ("a1", dcoll a1) :: nil)) l).
  Proof.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.

  Lemma rmap_map_rec3 c d a1 l :
    (rmap
       (fun x : data =>
          match x with
            | drec r1 =>
              Some
                (drec
                   (rec_concat_sort
                      (("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil) r1))
            | _ => None
          end)
       (map (fun x : data => drec (("PBIND", x) :: nil)) l))
    =
    Some (map (fun x : data =>  drec (("PBIND", x) :: ("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil)) l).
  Proof.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.

  Lemma option_id {A} (x:option A) :
    (match x with None => None | Some y => Some y end) = x.
  Proof.
    destruct x; reflexivity.
  Qed.
  
  Lemma rmap_map_unnest2 c env a l0 l1 :
    rmap
      (fun x : data =>
         olift2
           (fun d1 d2 : data =>
              match d1 with
                | drec r1 =>
                  match d2 with
                    | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                    | _ => None
                  end
                | _ => None
              end)
           match x with
             | drec r => edot r "PDATA"
             | _ => None
           end
           match x with
             | drec r => edot r "PDATA2"
             | _ => None
           end)
      (map
         (fun x : data =>
            drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", a) :: ("PDATA2", x) :: nil)) l0 ++ l1)
    =
    olift2 (fun d1 d2 => Some (d1 ++ d2))
           (rmap
              (fun x : data =>
                 match a with
                   | drec r2 =>
                     match x with
                       | drec r1 => Some (drec (rec_concat_sort r2 r1))
                       | _ => None
                     end
                   | _ => None
                 end) l0)
           (rmap
              (fun x : data =>
                 olift2
                   (fun d1 d2 : data =>
                      match d1 with
                        | drec r1 =>
                          match d2 with
                            | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                            | _ => None
                          end
                        | _ => None
                      end)
                   match x with
                     | drec r => edot r "PDATA"
                     | _ => None
                   end
                   match x with
                     | drec r => edot r "PDATA2"
                     | _ => None
                   end)
              l1).
  Proof.
    induction l0; try reflexivity; simpl.
    rewrite option_id; reflexivity.
    rewrite IHl0; clear IHl0; simpl.
    destruct a; try reflexivity.
    destruct a0; try reflexivity.
    simpl.
    destruct ((rmap
           (fun x : data =>
            match x with
            | drec r1 => Some (drec (rec_concat_sort l r1))
            | _ => None
            end) l0)); try reflexivity; simpl.
    generalize (     rmap
       (fun x : data =>
        olift2
          (fun d1 d2 : data =>
           match d1 with
           | drec r1 =>
               match d2 with
               | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
               | _ => None
               end
           | _ => None
           end)
          match x with
          | drec r => edot r "PDATA"
          | _ => None
          end
          match x with
          | drec r => edot r "PDATA2"
          | _ => None
          end) l1); intros.
    destruct o; reflexivity.
  Qed.

  Lemma omap_concat_map_rec c env a1 l :
    omap_concat
      (drec (("PBIND", env) :: ("PCONST", c) :: ("a1", dcoll a1) :: nil))
      (map (fun x : data => drec (("PDATA", x) :: nil)) l)
    =
    Some (map (fun x : data =>  drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", x) :: ("a1", dcoll a1) :: nil)) l).
  Proof.
    unfold omap_concat; simpl.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.

  Lemma omap_concat_map_rec2 c env a l :
    omap_concat (drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", a) :: nil))
                (map (fun x : data => drec (("PDATA2", x) :: nil)) l)

    =
    Some (map (fun x : data =>  drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", a) :: ("PDATA2", x) :: nil)) l).
  Proof.
    unfold omap_concat; simpl.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.

  Lemma omap_concat_map_rec3 c d a1 l :
    omap_concat
      (drec (("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil))
      (map (fun x : data => drec (("PBIND", x) :: nil)) l)
    =
    Some (map (fun x : data =>  drec (("PBIND", x) :: ("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil)) l).
  Proof.
    unfold omap_concat; simpl.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.

  Lemma omap_concat_unnest c env a a1 l :
    omap_concat
      (drec (("PBIND", env) :: ("PCONST", c) :: ("a1", dcoll a1) :: nil))
      (drec (("PDATA", a) :: nil)
            :: map (fun x : data => drec (("PDATA", x) :: nil)) l)
    =
    Some (drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", a) :: ("a1", dcoll a1) :: nil) ::
               (map (fun x : data => drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", x) :: ("a1", dcoll a1) :: nil)) l)).
  Proof.
    unfold omap_concat; simpl.
    rewrite rmap_map_rec2; simpl; reflexivity.
  Qed.

  Lemma omap_concat_unnest2 c d a a1 l :
    omap_concat
      (drec (("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil))
      (drec (("PBIND", a) :: nil)
            :: map (fun x : data => drec (("PBIND", x) :: nil)) l)
    =
    Some (drec (("PBIND", a) :: ("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil) ::
               (map (fun x : data => drec (("PBIND", x) :: ("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll a1) :: nil)) l)).
  Proof.
    unfold omap_concat; simpl.
    rewrite rmap_map_rec3; simpl; reflexivity.
  Qed.

  Lemma rmap_remove1 c env l l2:
    rmap
      (fun x : data =>
         match x with
           | drec r => Some (drec (rremove r "a1"))
           | _ => None
         end)
      (map
         (fun x : data =>
            drec
              (("PBIND", env) :: ("PCONST", c) :: ("PDATA", x) :: ("a1", dcoll l2) :: nil))
         l)
    =
    Some (map (fun x: data => drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", x) :: nil)) l).
  Proof.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.
  
  Lemma rmap_remove2 c d l l2:
    rmap
      (fun x : data =>
         match x with
           | drec r => Some (drec (rremove r "a1"))
           | _ => None
         end)
      (map
         (fun x : data =>
            drec
              (("PBIND", x) :: ("PCONST", c) :: ("PDATA", d) :: ("a1", dcoll l2) :: nil))
         l)
    =
    Some (map (fun x: data => drec (("PBIND", x) :: ("PCONST", c) :: ("PDATA", d) :: nil)) l).
  Proof.
    induction l; try reflexivity; simpl.
    rewrite IHl; reflexivity.
  Qed.
  
  Lemma rmap_one1 c env a l:
    rmap
      (fun x : data =>
         match x with
           | drec r => edot r "PDATA"
           | _ => None
         end) (drec (("PBIND", env) :: ("PCONST", c) :: ("PDATA", a) :: nil) :: l)
    =
    match
      rmap
        (fun x : data =>
           match x with
             | drec r => edot r "PDATA"
             | _ => None
           end) l
    with
      | Some a' => Some (a :: a')
      | None => None
    end.
  Proof.
    reflexivity.
  Qed.

  Lemma unfold_env_nra (ae:cnraenv) (env:data) (x:data) :
    (cnraenv_eval ae env x) = (h ⊢ (nra_of_cnraenv ae) @ₐ (pat_context_data (drec constant_env) env x)).
  Proof.
    revert env x; cnraenv_cases (induction ae) Case; simpl; intros.
    - Case "ANID"%string.
      simpl; reflexivity.
    - Case "ANConst"%string.
      reflexivity.
    - Case "ANBinop"%string.
      rewrite IHae1; rewrite IHae2; reflexivity.
    - Case "ANUnop"%string.
      rewrite IHae; reflexivity.
    - Case "ANMap"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_cnraenv ae2) @ₐ (pat_context_data (drec constant_env) env x));
        intros; clear ae2 x.
      unfold olift.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold rmap_concat, oomap_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite rmap_map_rec1; simpl; intros.
      rewrite omap_concat_unnest; simpl.
      rewrite omap_concat_map_rec in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite rmap_remove1 in *; simpl.
      rewrite (IHae1 env a); unfold pat_context_data; simpl.
      generalize (h ⊢ (nra_of_cnraenv ae1) @ₐ (drec
                   (("PBIND", env)
                    :: ("PCONST", drec constant_env) :: ("PDATA", a) :: nil))); intros.
      destruct o; try reflexivity; simpl.
      unfold lift, lift_oncoll in *.
      revert IHl.
      destruct (rmap (nra_eval h (nra_of_cnraenv ae1))
         (map (fun x : data =>
           drec
             (("PBIND", env)
              :: ("PCONST", drec constant_env) :: ("PDATA", x) :: nil)) l)); try reflexivity; try congruence; simpl; destruct (rmap (cnraenv_eval ae1 env) l); try reflexivity; try congruence.
    - Case "ANMapConcat"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_cnraenv ae2) @ₐ (pat_context_data (drec constant_env) env x)); intros; clear ae2 x.
      unfold olift.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold rmap_concat, oomap_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite rmap_map_rec1; simpl; intros.
      rewrite omap_concat_unnest; simpl.
      rewrite omap_concat_map_rec in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite rmap_remove1 in *; simpl.
      rewrite (IHae1 env a); unfold pat_context_data; simpl.
      generalize (h ⊢ (nra_of_cnraenv ae1) @ₐ(drec
            (("PBIND", env)
             :: ("PCONST", drec constant_env) :: ("PDATA", a) :: nil))); intros.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      rewrite rmap_map_rec1 in *; simpl in *.
      rewrite omap_concat_map_rec2 in *.
      unfold lift in *; simpl in *.
      revert IHl; generalize (
            oflat_map
              (fun a0 : data =>
               match
                 match h ⊢ (nra_of_cnraenv ae1) @ₐ a0 with
                 | Some x' =>
                     lift_oncoll
                       (fun c1 : list data =>
                        match
                          rmap
                            (fun x : data =>
                             Some (drec (("PDATA2", x) :: nil))) c1
                        with
                        | Some a' => Some (dcoll a')
                        | None => None
                        end) x'
                 | None => None
                 end
               with
               | Some (dcoll y) => omap_concat a0 y
               | _ => None
               end)
              (map
              (fun x : data =>
               drec
                  (("PBIND", env)
                     :: ("PCONST", drec constant_env) :: ("PDATA", x) :: nil)) l)
                    ); intros.
      destruct o; try reflexivity; try congruence; simpl.
      * unfold lift_oncoll in *; simpl in *.
        rewrite rmap_map_unnest2; simpl in *.
        revert IHl; generalize (
                        (rmap
          (fun x : data =>
           olift2
             (fun d1 d2 : data =>
              match d1 with
              | drec r1 =>
                  match d2 with
                  | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                  | _ => None
                  end
              | _ => None
              end)
             match x with
             | drec r => edot r "PDATA"
             | _ => None
             end
             match x with
             | drec r => edot r "PDATA2"
             | _ => None
             end) l1)
                      ); generalize (oflat_map
            (fun a0 : data =>
             match cnraenv_eval ae1 env a0 with
             | Some (dcoll y) => omap_concat a0 y
             | _ => None
             end) l) ; intros.
        destruct o; try reflexivity; try congruence; simpl.
        destruct o0; try reflexivity; try congruence; simpl.
        inversion IHl; clear IHl H0.
        unfold olift2, omap_concat; simpl.
        unfold orecconcat; simpl.
        generalize (       rmap
         (fun x : data =>
          match a with
          | drec r2 =>
              match x with
              | drec r1 => Some (drec (rec_concat_sort r2 r1))
              | _ => None
              end
          | _ => None
          end) l0); simpl; intros.
        destruct o; try reflexivity; simpl.
        destruct o0; try reflexivity; try congruence; simpl.
      * unfold olift2; simpl.
        destruct (omap_concat a l0); simpl; try reflexivity.
        revert IHl; generalize (oflat_map
         (fun a0 : data =>
          match cnraenv_eval ae1 env a0 with
          | Some (dcoll y) => omap_concat a0 y
          | _ => None
          end) l); intros.
        destruct o; try reflexivity; congruence.
    - Case "ANProduct"%string.
      rewrite IHae1; rewrite IHae2; reflexivity.
    - Case "ANSelect"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_cnraenv ae2) @ₐ (pat_context_data (drec constant_env) env x)); intros; clear ae2 x.
      unfold olift.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold rmap_concat, oomap_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite rmap_map_rec1; simpl; intros.
      rewrite omap_concat_unnest; simpl.
      rewrite omap_concat_map_rec in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite rmap_remove1 in *; simpl.
      rewrite (IHae1 env a); unfold pat_context_data; simpl.
      generalize (h ⊢ (nra_of_cnraenv ae1) @ₐ(drec
            (("PBIND", env)
             :: ("PCONST", drec constant_env) :: ("PDATA", a) :: nil))); intros.
      destruct o; try reflexivity; simpl.
      unfold lift, lift_oncoll in *.
      destruct d; try reflexivity; simpl.
      destruct b; try reflexivity; simpl.
      * revert IHl.
        generalize (lift_filter
                      (fun x' : data =>
                         match cnraenv_eval ae1 env x' with
                           | Some (dbool b) => Some b
                           | _ => None
                         end) l);
          generalize (lift_filter
                        (fun x' : data =>
                           match h ⊢ (nra_of_cnraenv ae1) @ₐ x' with
                             | Some (dbool b) => Some b
                             | _ => None
                           end)
                        (map
              (fun x : data =>
               drec
                 (("PBIND", env)
                  :: ("PCONST", drec constant_env) :: ("PDATA", x) :: nil)) l));
          intros.
        destruct o; destruct o0; try congruence; try reflexivity;
        rewrite rmap_one1;
        revert IHl;
        generalize (rmap
                      (fun x : data =>
                         match x with
                           | drec r => edot r "PDATA"
                                   | _ => None
                         end) l0); intros;
        destruct o; try reflexivity; congruence.
      * revert IHl.
        generalize (lift_filter
                      (fun x' : data =>
                         match cnraenv_eval ae1 env x' with
                           | Some (dbool b) => Some b
                           | _ => None
                         end) l);
          generalize (lift_filter
                        (fun x' : data =>
                           match h ⊢ (nra_of_cnraenv ae1) @ₐ x' with
                             | Some (dbool b) => Some b
                             | _ => None
                           end)
                         (map
              (fun x : data =>
               drec
                (("PBIND", env)
                :: ("PCONST", drec constant_env) :: ("PDATA", x) :: nil)) l));
          intros.
        destruct o; destruct o0; try congruence; reflexivity.
    - Case "ANDefault"%string.
      rewrite IHae1; rewrite IHae2; reflexivity.
    - Case "ANEither"%string.
      destruct x; simpl; trivial; [rewrite IHae1|rewrite IHae2]; reflexivity.
    - Case "ANEitherConcat"%string.
      rewrite IHae2. generalize ((h ⊢ (nra_of_cnraenv ae2) @ₐ (pat_context_data (drec constant_env) env x))); intros.
      destruct o; try reflexivity; simpl;
      rewrite IHae1; reflexivity.
    - Case "ANApp"%string.
      rewrite IHae2. generalize ((h ⊢ (nra_of_cnraenv ae2) @ₐ (pat_context_data (drec constant_env) env x))); intros.
      destruct o; try reflexivity; simpl.
      rewrite IHae1; reflexivity.
    - Case "ANGetConstant"%string.
      reflexivity.
    - Case "ANEnv"%string.
      reflexivity.
    - Case "ANAppEnv"%string.
      rewrite IHae2; clear IHae2.
      generalize (h ⊢ (nra_of_cnraenv ae2) @ₐ (pat_context_data (drec constant_env) env x)); intros.
      destruct o; try reflexivity; simpl.
      apply IHae1.
    - Case "ANMapEnv"%string.
      unfold lift, olift, rmap_concat, oomap_concat; simpl.
      destruct env; try reflexivity; simpl.
      induction l; try reflexivity; simpl; unfold lift in *; simpl.
      unfold rmap_concat, oomap_concat in *; simpl in *.
      unfold lift in *; simpl.
      revert IHl; rewrite rmap_map_rec1; simpl; intros.
      rewrite omap_concat_unnest2; simpl.
      rewrite omap_concat_map_rec3 in IHl; simpl in *.
      rewrite app_nil_r in *.
      rewrite rmap_remove2 in *; simpl.
      rewrite (IHae a x); unfold pat_context_data; simpl.
      generalize (h ⊢ (nra_of_cnraenv ae) @ₐ (drec (("PBIND", a) :: ("PCONST", drec constant_env) :: ("PDATA", x) :: nil))); intros.
      destruct o; try reflexivity; simpl.
      unfold lift, lift_oncoll in *.
      revert IHl.
      destruct (rmap (nra_eval h (nra_of_cnraenv ae))
         (map (fun x0 : data => drec (("PBIND", x0) :: ("PCONST", drec constant_env) :: ("PDATA", x) :: nil))
              l)); try reflexivity; try congruence; simpl; destruct (rmap (fun env' => (cnraenv_eval ae env' x)) l); try reflexivity; try congruence.
  Qed.
  
End cNRAEnv.

(* Delimit Scope cnraenv_scope with cnraenv. *)
Delimit Scope cnraenv_scope with cnraenv.

Notation "h ⊢ₑ op @ₑ x ⊣ c ; env " := (cnraenv_eval h c op env x) (at level 10) : cnraenv_scope.

Section RCnraenv2.
  Local Open Scope cnraenv.

  Context {fruntime:foreign_runtime}.

  Lemma cnraenv_eval_const_sort h p x c env :
    h ⊢ₑ p @ₑ x ⊣ (rec_sort c); env = h ⊢ₑ p @ₑ x ⊣ c; env.
  Proof.
    revert x c env.
    induction p; simpl; unfold olift, olift2; intros; trivial;
    try rewrite IHp; try rewrite IHp1; try rewrite IHp2; trivial.
    - match_destr.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply rmap_ext; intros.
      congruence.
    - match_destr.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply rmap_concat_ext; intros.
      congruence.
    - match_destr.
      apply lift_oncoll_ext; intros.
      f_equal.
      apply lift_filter_ext; intros.
      rewrite IHp1; match_destr.
    - match_destr.
    - match_destr.
    - unfold edot. 
      rewrite (assoc_lookupr_drec_sort (odt:=ODT_string)).
      trivial.
    - match_destr.
    - apply lift_oncoll_ext; intros.
      f_equal.
      apply rmap_ext; intros.
      congruence.
  Qed.

  Lemma unfold_env_nra_sort h c (ae:cnraenv) (env:data) (x:data) :
    (cnraenv_eval h c ae env x) = (h ⊢ (nra_of_cnraenv ae) @ₐ (pat_context_data (drec (rec_sort c)) env x)).
  Proof.
    rewrite <- (cnraenv_eval_const_sort h _ x c env).
    rewrite unfold_env_nra by trivial.
    trivial.
  Qed.

   (* evaluation preserves normalization *)
  Lemma cnraenv_eval_normalized h constant_env {op:cnraenv} {env d:data} {o} :
    cnraenv_eval h constant_env op env d = Some o ->
    Forall (fun x => data_normalized h (snd x)) constant_env ->
    data_normalized h env ->
    data_normalized h d ->
    data_normalized h o.
  Proof.
    Hint Resolve dnrec_sort.
    rewrite unfold_env_nra_sort; intros.
    eauto.
  Qed.

  End RCnraenv2.

  
Notation "'ID'" := (ANID)  (at level 50) : cnraenv_scope.
Notation "'ENV'" := (ANEnv)  (at level 50) : cnraenv_scope.
Notation "CGET⟨ s ⟩" := (ANGetConstant s) (at level 50) : cnraenv_scope.
  
Notation "‵‵ c" := (ANConst (dconst c))  (at level 0) : cnraenv_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (ANConst c)  (at level 0) : cnraenv_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (ANConst (dcoll nil))  (at level 0) : cnraenv_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (ANConst (drec nil)) (at level 50) : cnraenv_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (ANBinop AAnd r1 r2) (right associativity, at level 65): cnraenv_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (ANBinop AOr r1 r2) (right associativity, at level 70): cnraenv_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (ANBinop AEq r1 r2) (right associativity, at level 70): cnraenv_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (ANBinop ALt r1 r2) (no associativity, at level 70): cnraenv_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (ANBinop AUnion r1 r2) (right associativity, at level 70): cnraenv_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (ANBinop AMinus r1 r2) (right associativity, at level 70): cnraenv_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (ANBinop AMin r1 r2) (right associativity, at level 70): cnraenv_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (ANBinop AMax r1 r2) (right associativity, at level 70): cnraenv_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((ANBinop AConcat) p r) (at level 70) : cnraenv_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((ANBinop AMergeConcat) p r) (at level 70) : cnraenv_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (ANUnop ANeg r1) (right associativity, at level 70): cnraenv_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (ANUnop ADistinct r1) (right associativity, at level 70): cnraenv_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (ANUnop ACount r1) (right associativity, at level 70): cnraenv_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (ANUnop AFlatten d) (at level 50) : cnraenv_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((ANUnop AColl) d)  (at level 50) : cnraenv_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((ANUnop (ARec s)) r) (at level 50) : cnraenv_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((ANUnop (ARecRemove s1)) r) (at level 50) : cnraenv_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((ANUnop (ARecProject s1)) r) (at level 50) : cnraenv_scope.          (* π = \pi *)
Notation "p · r" := ((ANUnop (ADot r)) p) (left associativity, at level 40): cnraenv_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (ANMap p r) (at level 70) : cnraenv_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (ANMapConcat e2 e1) (at level 70) : cnraenv_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (ANProduct r1 r2) (right associativity, at level 70): cnraenv_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (ANSelect p r) (at level 70) : cnraenv_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (ANDefault r1 r2) (right associativity, at level 70): cnraenv_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (ANApp r1 r2) (right associativity, at level 60): cnraenv_scope.           (* ◯ = \bigcirc *)

Notation "r1 ◯ₑ r2" := (ANAppEnv r1 r2) (right associativity, at level 60): cnraenv_scope.           (* ◯ = \bigcirc *)
Notation "χᵉ⟨ p ⟩()" := (ANMapEnv p) (at level 70) : cnraenv_scope.                              (* χ = \chi *)

Hint Resolve cnraenv_eval_normalized.

Tactic Notation "cnraenv_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANID"%string
  | Case_aux c "ANConst"%string
  | Case_aux c "ANBinop"%string
  | Case_aux c "ANUnop"%string
  | Case_aux c "ANMap"%string
  | Case_aux c "ANMapConcat"%string
  | Case_aux c "ANProduct"%string
  | Case_aux c "ANSelect"%string
  | Case_aux c "ANDefault"%string
  | Case_aux c "ANEither"%string
  | Case_aux c "ANEitherConcat"%string
  | Case_aux c "ANApp"%string
  | Case_aux c "ANGetConstant"%string
  | Case_aux c "ANEnv"%string
  | Case_aux c "ANAppEnv"%string
  | Case_aux c "ANMapEnv"%string].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
