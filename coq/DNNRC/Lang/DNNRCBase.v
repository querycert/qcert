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
Require Import Decidable.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNRAEnv.

Section DNNRCBase.
  Context {fruntime:foreign_runtime}.
  
  (** Named Nested Relational Calculus *)
  
  Definition var := string.

  Section plug.
    Context {plug_type:Set}.

    Definition coll_bindings := list (string * (list data)).

    Definition bindings_of_coll_bindings (cb:coll_bindings) : bindings :=
      map (fun xy => (fst xy, dcoll (snd xy))) cb.
    
    Class AlgPlug :=
      mkAlgPlug {
          plug_eval : brand_relation_t -> coll_bindings -> plug_type -> option data
          ; plug_normalized :
            forall (h:brand_relation_t) (op:plug_type), forall (constant_env:coll_bindings) (o:data),
                Forall (fun x => data_normalized h (snd x)) (bindings_of_coll_bindings constant_env) ->
                plug_eval h constant_env op = Some o -> data_normalized h o;
(*        plug_equiv {h} (op1 op2:T) :
            forall (env:bindings),
              Forall (data_normalized h) (map snd env) ->
              plug_eval h env op1 = plug_eval h env op2 *)
        }.

  End plug.
  Global Arguments AlgPlug : clear implicits. 
  
  Section GenDNNRCBase.
    (* Type for DNNRC AST annotations and plugged-in language *)
    Context {A plug_type:Set}.

    Unset Elimination Schemes.

    Inductive dnnrc_base  : Set :=
    | DNNRCGetConstant : A -> var -> dnnrc_base
    | DNNRCVar : A -> var -> dnnrc_base
    | DNNRCConst : A -> data -> dnnrc_base
    | DNNRCBinop : A -> binary_op -> dnnrc_base -> dnnrc_base -> dnnrc_base
    | DNNRCUnop : A -> unary_op -> dnnrc_base -> dnnrc_base
    | DNNRCLet : A -> var -> dnnrc_base -> dnnrc_base -> dnnrc_base
    | DNNRCFor : A -> var -> dnnrc_base -> dnnrc_base -> dnnrc_base
    | DNNRCIf : A -> dnnrc_base -> dnnrc_base -> dnnrc_base -> dnnrc_base
    | DNNRCEither : A -> dnnrc_base -> var -> dnnrc_base -> var -> dnnrc_base -> dnnrc_base
    | DNNRCGroupBy : A -> string -> list string -> dnnrc_base -> dnnrc_base
    | DNNRCCollect : A -> dnnrc_base -> dnnrc_base
    | DNNRCDispatch : A -> dnnrc_base -> dnnrc_base
    | DNNRCAlg : A -> plug_type -> list (string * dnnrc_base) -> dnnrc_base.

    Set Elimination Schemes.

    (** Induction principles used as backbone for inductive proofs on dnnrc_base *)

    Definition dnnrc_base_rect (P : dnnrc_base -> Type)
               (fdgetconstant : forall a, forall v, P (DNNRCGetConstant a v))
               (fdvar : forall a, forall v, P (DNNRCVar a v))
               (fdconst : forall a, forall d : data, P (DNNRCConst a d))
               (fdbinop : forall a, forall b, forall n1 n2 : dnnrc_base, P n1 -> P n2 -> P (DNNRCBinop a b n1 n2))
               (fdunop : forall a, forall u, forall n : dnnrc_base, P n -> P (DNNRCUnop a u n))
               (fdlet : forall a, forall v, forall n1 n2 : dnnrc_base, P n1 -> P n2 -> P (DNNRCLet a v n1 n2))
               (fdfor : forall a, forall v, forall n1 n2 : dnnrc_base, P n1 -> P n2 -> P (DNNRCFor a v n1 n2))
               (fdif : forall a, forall n1 n2 n3 : dnnrc_base, P n1 -> P n2 -> P n3 -> P (DNNRCIf a n1 n2 n3))
               (fdeither : forall a, forall n0 n1 n2, forall v1 v2,
                       P n0 -> P n1 -> P n2 -> P (DNNRCEither a n0 v1 n1 v2 n2))
               (fdgroupby : forall a, forall g, forall sl, forall n : dnnrc_base, P n -> P (DNNRCGroupBy a g sl n))
               (fdcollect : forall a, forall n : dnnrc_base, P n -> P (DNNRCCollect a n))
               (fddispatch : forall a, forall n : dnnrc_base, P n -> P (DNNRCDispatch a n))
               (fdalg : forall a, forall op:plug_type, forall r : list (string*dnnrc_base), Forallt (fun n => P (snd n)) r -> P (DNNRCAlg a op r))
      :=
        fix F (n : dnnrc_base) : P n :=
          match n as n0 return (P n0) with
          | DNNRCGetConstant a v => fdgetconstant a v
          | DNNRCVar a v => fdvar a v
          | DNNRCConst a d => fdconst a d
          | DNNRCBinop a b n1 n2 => fdbinop a b n1 n2 (F n1) (F n2)
          | DNNRCUnop a u n => fdunop a u n (F n)
          | DNNRCLet a v n1 n2 => fdlet a v n1 n2 (F n1) (F n2)
          | DNNRCFor a v n1 n2 => fdfor a v n1 n2 (F n1) (F n2)
          | DNNRCIf a n1 n2 n3 => fdif a n1 n2 n3 (F n1) (F n2) (F n3)
          | DNNRCEither a n0 v1 n1 v2 n2 => fdeither a n0 n1 n2 v1 v2 (F n0) (F n1) (F n2)
          | DNNRCGroupBy a g sl n => fdgroupby a g sl n (F n)
          | DNNRCCollect a n => fdcollect a n (F n)
          | DNNRCDispatch a n => fddispatch a n (F n)
          | DNNRCAlg a op r =>
            fdalg a op r ((fix F3 (r : list (string * dnnrc_base)) : Forallt (fun n => P (snd n)) r :=
                             match r as c0 with
                             | nil => Forallt_nil _
                             | cons n c0 => @Forallt_cons _ _ _ _ (F (snd n)) (F3 c0)
                             end) r)
          end.

    (** Induction principles used as backbone for inductive proofs on dnnrc_base *)
    Definition dnnrc_base_ind (P : dnnrc_base -> Prop)
               (fdgetconstant : forall a, forall v, P (DNNRCGetConstant a v))
               (fdvar : forall a, forall v, P (DNNRCVar a v))
               (fdconst : forall a, forall d : data, P (DNNRCConst a d))
               (fdbinop : forall a, forall b, forall n1 n2 : dnnrc_base, P n1 -> P n2 -> P (DNNRCBinop a b n1 n2))
               (fdunop : forall a, forall u, forall n : dnnrc_base, P n -> P (DNNRCUnop a u n))
               (fdlet : forall a, forall v, forall n1 n2 : dnnrc_base, P n1 -> P n2 -> P (DNNRCLet a v n1 n2))
               (fdfor : forall a, forall v, forall n1 n2 : dnnrc_base, P n1 -> P n2 -> P (DNNRCFor a v n1 n2))
               (fdif : forall a, forall n1 n2 n3 : dnnrc_base, P n1 -> P n2 -> P n3 -> P (DNNRCIf a n1 n2 n3))
               (fdeither : forall a, forall n0 n1 n2, forall v1 v2,
                       P n0 -> P n1 -> P n2 -> P (DNNRCEither a n0 v1 n1 v2 n2))
               (fdgroupby : forall a, forall g, forall sl, forall n : dnnrc_base, P n -> P (DNNRCGroupBy a g sl n))
               (fdcollect : forall a, forall n : dnnrc_base, P n -> P (DNNRCCollect a n))
               (fddispatch : forall a, forall n : dnnrc_base, P n -> P (DNNRCDispatch a n))
               (fdalg : forall a, forall op:plug_type, forall r : list (string*dnnrc_base), Forall (fun n => P (snd n)) r -> P (DNNRCAlg a op r))
      :=
        fix F (n : dnnrc_base) : P n :=
          match n as n0 return (P n0) with
          | DNNRCGetConstant a v => fdgetconstant a v
          | DNNRCVar a v => fdvar a v
          | DNNRCConst a d => fdconst a d
          | DNNRCBinop a b n1 n2 => fdbinop a b n1 n2 (F n1) (F n2)
          | DNNRCUnop a u n => fdunop a u n (F n)
          | DNNRCLet a v n1 n2 => fdlet a v n1 n2 (F n1) (F n2)
          | DNNRCFor a v n1 n2 => fdfor a v n1 n2 (F n1) (F n2)
          | DNNRCIf a n1 n2 n3 => fdif a n1 n2 n3 (F n1) (F n2) (F n3)
          | DNNRCEither a n0 v1 n1 v2 n2 => fdeither a n0 n1 n2 v1 v2 (F n0) (F n1) (F n2)
          | DNNRCGroupBy a g sl n => fdgroupby a g sl n (F n)
          | DNNRCCollect a n => fdcollect a n (F n)
          | DNNRCDispatch a n => fddispatch a n (F n)
          | DNNRCAlg a op r =>
            fdalg a op r ((fix F3 (r : list (string*dnnrc_base)) : Forall (fun n => P (snd n)) r :=
                             match r as c0 with
                             | nil => Forall_nil _
                             | cons n c0 => @Forall_cons _ _ _ _ (F (snd n)) (F3 c0)
                             end) r)
          end.

    Definition dnnrc_base_rec (P:dnnrc_base->Set) := @dnnrc_base_rect P.

    Lemma dnnrc_baseInd2 (P : dnnrc_base -> Prop)
          (fdgetconstant : forall a, forall v, P (DNNRCGetConstant a v))
          (fdvar : forall a, forall v, P (DNNRCVar a v))
          (fdconst : forall a, forall d : data, P (DNNRCConst a d))
          (fdbinop : forall a, forall b, forall n1 n2 : dnnrc_base, P (DNNRCBinop a b n1 n2))
          (fdunop : forall a, forall u, forall n : dnnrc_base, P (DNNRCUnop a u n))
          (fdlet : forall a, forall v, forall n1 n2 : dnnrc_base, P (DNNRCLet a v n1 n2))
          (fdfor : forall a, forall v, forall n1 n2 : dnnrc_base, P (DNNRCFor a v n1 n2))
          (fdif : forall a, forall n1 n2 n3 : dnnrc_base, P (DNNRCIf a n1 n2 n3))
          (fdeither : forall a, forall n0 n1 n2, forall v1 v2,
                  P (DNNRCEither a n0 v1 n1 v2 n2))
          (fdgroupby : forall a, forall g, forall sl, forall n : dnnrc_base, P n -> P (DNNRCGroupBy a g sl n))
          (fdcollect : forall a, forall n : dnnrc_base, P (DNNRCCollect a n))
          (fddispatch : forall a, forall n : dnnrc_base, P (DNNRCDispatch a n))
          (fdalg : forall a, forall op:plug_type, forall r : list (string*dnnrc_base), Forall (fun n => P (snd n)) r -> P (DNNRCAlg a op r))
: forall n, P n.
    Proof.
      intros.
      apply dnnrc_base_ind; trivial.
    Qed.

    Definition dnnrc_base_annotation_get (d:dnnrc_base) : A
      := match d with
         | DNNRCGetConstant a _ => a
         | DNNRCVar a _ => a
         | DNNRCConst a _ => a
         | DNNRCBinop a _ _ _ => a
         | DNNRCUnop a _ _ => a
         | DNNRCLet a _ _ _ => a
         | DNNRCFor a _ _ _ => a
         | DNNRCIf a _ _ _ => a
         | DNNRCEither a _ _ _ _ _ => a
         | DNNRCGroupBy a _ _ _ => a
         | DNNRCCollect a _ => a
         | DNNRCDispatch a _ => a
         | DNNRCAlg a _ _ => a
         end.

    Definition dnnrc_base_annotation_update (f:A->A) (d:dnnrc_base) : dnnrc_base
      := match d with
         | DNNRCGetConstant a v => DNNRCGetConstant (f a) v
         | DNNRCVar a v => DNNRCVar (f a) v
         | DNNRCConst a c => DNNRCConst (f a) c
         | DNNRCBinop a b d₁ d₂ => DNNRCBinop (f a) b d₁ d₂
         | DNNRCUnop a u d₁ => DNNRCUnop (f a) u d₁
         | DNNRCLet a x d₁ d₂ => DNNRCLet (f a) x d₁ d₂
         | DNNRCFor a x d₁ d₂ => DNNRCFor (f a) x d₁ d₂
         | DNNRCIf a d₀ d₁ d₂ => DNNRCIf (f a) d₀ d₁ d₂
         | DNNRCEither a d₀ x₁ d₁ x₂ d₂ => DNNRCEither (f a) d₀ x₁ d₁ x₂ d₂
         | DNNRCGroupBy a g sl d₁ => DNNRCGroupBy (f a) g sl d₁
         | DNNRCCollect a d₀ => DNNRCCollect (f a) d₀
         | DNNRCDispatch a d₀ => DNNRCDispatch (f a) d₀
         | DNNRCAlg a p args => DNNRCAlg (f a) p args
         end .

    Context (h:brand_relation_t).
    Context (constant_env:list (string*ddata)).
    Fixpoint dnnrc_base_eval `{plug: AlgPlug plug_type} (env:dbindings) (e:dnnrc_base) : option ddata :=
      match e with
      | DNNRCGetConstant _ x =>
        edot constant_env x
      | DNNRCVar _ x =>
        lookup equiv_dec env x
      | DNNRCConst _ d =>
        Some (Dlocal (normalize_data h d))
      | DNNRCBinop _ bop e1 e2 =>
        olift2 (fun d1 d2 => lift Dlocal (binary_op_eval h bop d1 d2))
               (olift checkLocal (dnnrc_base_eval env e1)) (olift checkLocal (dnnrc_base_eval env e2))
      | DNNRCUnop _ uop e1 =>
        olift (fun d1 => lift Dlocal (unary_op_eval h uop d1)) (olift checkLocal (dnnrc_base_eval env e1))
      | DNNRCLet _ x e1 e2 =>
        match dnnrc_base_eval env e1 with
        | Some d => dnnrc_base_eval ((x,d)::env) e2
        | _ => None
        end
      | DNNRCFor _ x e1 e2 =>
        match dnnrc_base_eval env e1 with
        | Some (Ddistr c1) =>
          let inner_eval d1 :=
              let env' := (x,Dlocal d1) :: env in olift checkLocal (dnnrc_base_eval env' e2)
          in
          lift (fun coll => Ddistr coll) (lift_map inner_eval c1)
        | Some (Dlocal (dcoll c1)) =>
          let inner_eval d1 :=
              let env' := (x,Dlocal d1) :: env in olift checkLocal (dnnrc_base_eval env' e2)
          in
          lift (fun coll => Dlocal (dcoll coll)) (lift_map inner_eval c1)
        | Some (Dlocal _) => None
        | None => None
        end
      | DNNRCIf _ e1 e2 e3 =>
        let aux_if d :=
            match d with
            | dbool b =>
              if b then dnnrc_base_eval env e2 else dnnrc_base_eval env e3
            | _ => None
            end
        in olift aux_if (olift checkLocal (dnnrc_base_eval env e1))
      | DNNRCEither _ ed xl el xr er =>
        match olift checkLocal (dnnrc_base_eval env ed) with
        | Some (dleft dl) =>
          dnnrc_base_eval ((xl,Dlocal dl)::env) el
        | Some (dright dr) =>
          dnnrc_base_eval ((xr,Dlocal dr)::env) er
        | _ => None
        end
      | DNNRCGroupBy _ g sl e1 =>
        None (* XXX TODO XXX *)
      | DNNRCCollect _ e1 =>
        let collected := olift checkDistrAndCollect (dnnrc_base_eval env e1) in
        lift Dlocal collected
      | DNNRCDispatch _ e1 =>
        match olift checkLocal (dnnrc_base_eval env e1) with
        | Some (dcoll c1) =>
          Some (Ddistr c1)
        | _ => None
        end
      | DNNRCAlg _ plug nnrcbindings =>
        match listo_to_olist (map (fun x =>
               match dnnrc_base_eval env (snd x) with
               | Some (Ddistr coll) => Some (fst x, coll)
               | _ => None
               end) nnrcbindings) with 
        | Some args =>
          match plug_eval h args plug with
          | Some (dcoll c) => Some (Ddistr c)
          | _ => None
          end
        | None => None
        end
      end.

    (* evaluation preserves normalization *)

    Lemma Forall_dcoll_map_lift l:
      Forall (fun x : string * (list data) => data_normalized h (dcoll (snd x))) l ->
      Forall (fun x : string * data => data_normalized h (snd x))
             (map (fun xy : string * list data => (fst xy, dcoll (snd xy))) l).
    Proof.
      intros; induction l; simpl in *.
      - apply Forall_nil.
      - rewrite Forall_forall in *; intros.
        simpl in *.
        assert (forall x : string * list data,
                   In x l -> data_normalized h (dcoll (snd x)))
          by (intros; apply H; auto).
        specialize (IHl H1).
        elim H0; clear H0; intros.
        subst; simpl.
        apply H.
        left; auto.
        rewrite Forall_forall in IHl.
        apply IHl.
        assumption.
    Qed.

    Lemma Forall_dcoll_map_lift2 l:
      Forall (fun x : string * data => data_normalized h (snd x))
             (map (fun xy : string * list data => (fst xy, dcoll (snd xy))) l) ->
      Forall (fun x : string * (list data) => data_normalized h (dcoll (snd x))) l.
    Proof.
      intros.
      induction l; simpl in *.
      - apply Forall_nil.
      - assert (Forall (fun x : string * data => data_normalized h (snd x))
                       (map (fun xy : string * list data => (fst xy, dcoll (snd xy))) l)).
        + clear IHl. rewrite Forall_forall in *; intros.
          apply H.
          simpl.
          auto.
        + specialize (IHl H0); clear H0.
          rewrite Forall_forall in *; intros.
          simpl in *.
          elim H0; clear H0; intros.
          subst.
          apply (H (fst x, (dcoll (snd x)))); left; auto.
          auto.
    Qed.

    Lemma Forall_dcoll_map_lift3 l:
      Forall (fun x : string * data => data_normalized h (snd x))
             (map (fun xy : string * list data => (fst xy, dcoll (snd xy))) l) <->
      Forall (fun x : string * (list data) => data_normalized h (dcoll (snd x))) l.
    Proof.
      split.
      apply Forall_dcoll_map_lift2.
      apply Forall_dcoll_map_lift.
    Qed.

    Lemma dnnrc_base_alg_bindings_normalized {plug:AlgPlug plug_type} denv l r :
      Forall (ddata_normalized h) (map snd denv) ->
      Forall
        (fun n : string * dnnrc_base =>
           forall (denv : dbindings) (o : ddata),
             dnnrc_base_eval denv (snd n) = Some o ->
             Forall (ddata_normalized h) (map snd denv) -> ddata_normalized h o) r ->
      lift_map
         (fun x : string * dnnrc_base =>
          match dnnrc_base_eval denv (snd x) with
          | Some (Dlocal _) => None
          | Some (Ddistr coll) => Some (fst x, coll)
          | None => None
          end) r = Some l ->
      Forall (fun x : string * (list data) => data_normalized h (dcoll (snd x))) l.
    Proof.
      revert r; induction l; intros; trivial.
      destruct r; simpl in * ; [invcs H1 | ] .
      invcs H0.
      case_eq (dnnrc_base_eval denv (snd p))
      ; intros; rewrite H0 in H1
      ; try discriminate.
      destruct d; try discriminate.
      apply some_lift in H1.
      destruct H1 as [? req eqq].
      invcs eqq.
      specialize (IHl _ H H5 req).
      constructor; trivial.
      simpl.
      specialize (H4 _ _ H0 H).
      invcs H4.
      constructor; trivial.
    Qed.

    Lemma dnnrc_base_eval_normalized {plug:AlgPlug plug_type} denv e {o} :
      Forall (ddata_normalized h) (map snd constant_env) ->
      Forall (ddata_normalized h) (map snd denv) ->
      dnnrc_base_eval denv e = Some o ->
      ddata_normalized h o.
    Proof.
      intros Hc.
      revert denv o. induction e; intros denv o H0 ?; simpl in H.
      - rewrite Forall_forall in Hc.
        unfold edot in H. apply assoc_lookupr_in in H.
        apply (Hc o).
        rewrite in_map_iff.
        exists (v,o); eauto.
      - rewrite Forall_forall in H0.
        apply lookup_in in H.
        apply (H0 o).
        rewrite in_map_iff.
        exists (v,o); eauto.
      - inversion H; subst; intros.
        apply dnormalize_normalizes_local.
      - case_eq (dnnrc_base_eval denv e1); [intros ? eqq1 | intros eqq1];
        (rewrite eqq1 in *;
          case_eq (dnnrc_base_eval denv e2); [intros ? eqq2 | intros eqq2];
          rewrite eqq2 in *); simpl in *; try discriminate.
         + destruct d; destruct d0; simpl in H; try congruence;
           destruct o; simpl in *; unfold lift in H;
           case_eq (binary_op_eval h b d d0); intros; rewrite H1 in *; try congruence;
           inversion H; subst; clear H;
           constructor;
           eapply binary_op_eval_normalized; eauto.
           specialize (IHe1 denv (Dlocal d) H0 eqq1);
           inversion IHe1; assumption.
           specialize (IHe2 denv (Dlocal d0) H0 eqq2);
           inversion IHe2; assumption.
         + unfold olift2 in H; simpl in H.
           destruct d; simpl in H; congruence.
      - case_eq (dnnrc_base_eval denv e); [intros ? eqq1 | intros eqq1];
        rewrite eqq1 in *;
        simpl in *; try discriminate.
        destruct d; simpl in H; try congruence;
        destruct o; simpl in H; unfold lift in H;
        case_eq (unary_op_eval h u d); intros; rewrite H1 in H;
        inversion H; subst; clear H;
        constructor;
        eapply unary_op_eval_normalized; eauto.
        specialize (IHe denv (Dlocal d) H0 eqq1); inversion IHe; assumption.
      - case_eq (dnnrc_base_eval denv e1); [intros ? eqq1 | intros eqq1];
        rewrite eqq1 in *;
        simpl in *; try discriminate;
        case_eq (dnnrc_base_eval ((v,d)::denv) e2); [intros ? eqq2 | intros eqq2];
        rewrite eqq2 in *;
        simpl in *; try discriminate.
        inversion H; subst; clear H.
        eapply (IHe2 ((v, d) :: denv)); eauto.
        constructor; eauto.
      - case_eq (dnnrc_base_eval denv e1); [intros ? eqq1 | intros eqq1];
        rewrite eqq1 in *;
        simpl in *; try discriminate;
        unfold checkLocal in H; simpl in H.
        destruct d; try discriminate.
        { destruct d; try discriminate. (* Local case for DNNRCFor *)
          specialize (IHe1 _ _ H0 eqq1).
          inversion IHe1; subst.
          apply some_lift in H.
          destruct H; subst.
          constructor; constructor.
          inversion H2; subst; clear H2.
          apply (lift_map_Forall e H1); intros.
          case_eq (dnnrc_base_eval ((v, Dlocal x0) :: denv) e2); intros;
          rewrite H3 in H; simpl in H; try congruence.
          destruct d; simpl in H; try congruence.
          inversion H; subst; clear H.
          specialize (IHe2 ((v, Dlocal x0) :: denv)).
          assert (ddata_normalized h (Dlocal z)).
          apply IHe2.
          constructor; eauto.
          constructor; assumption. assumption.
          inversion H; assumption. }
        { specialize (IHe1 _ _ H0 eqq1). (* Distr case for DNNRCFor *)
          inversion IHe1; subst.
          apply some_lift in H.
          destruct H; subst.
          constructor.
          apply (lift_map_Forall e H2); intros.
          case_eq (dnnrc_base_eval ((v, Dlocal x0) :: denv) e2); intros;
          rewrite H3 in H; simpl in H; try congruence.
          destruct d; simpl in H; try congruence.
          inversion H; subst; clear H.
          specialize (IHe2 ((v, Dlocal x0) :: denv)).
          assert (ddata_normalized h (Dlocal z)).
          apply IHe2.
          constructor; eauto; try assumption.
          constructor; assumption. assumption.
          inversion H; assumption. }
      - case_eq (dnnrc_base_eval denv e1); [intros ? eqq1 | intros eqq1];
        rewrite eqq1 in *;
        simpl in *; try discriminate.
        destruct d; try discriminate.
        destruct d; try discriminate.
        simpl in *.
        destruct b; eauto.
      - case_eq (dnnrc_base_eval denv e1); [intros ? eqq1 | intros eqq1];
        rewrite eqq1 in *;
        simpl in *; try discriminate.
        specialize (IHe1 _ _ H0 eqq1).
        destruct d; try discriminate.
        destruct d; simpl in H; try discriminate;
        inversion IHe1; subst.
        + eapply (IHe2 ((v1, Dlocal d) :: denv)); eauto.
          constructor; eauto.
          constructor; eauto;
          inversion H2; assumption.
        + eapply (IHe3 ((v2, Dlocal d) :: denv)); eauto.
          constructor; eauto.
          constructor; eauto.
          inversion H2; assumption.
      - congruence. (* XXX GroupBy Case TODO XXX *)
      - unfold lift in H.
        case_eq (dnnrc_base_eval denv e); intros; rewrite H1 in H; simpl in H;
        try discriminate.
        destruct d; simpl in *; try discriminate.
        inversion H; subst; clear H.
        specialize (IHe denv (Ddistr l) H0 H1).
        inversion IHe; constructor; constructor; assumption.
      - case_eq (dnnrc_base_eval denv e); intros; rewrite H1 in H; simpl in H;
        try discriminate.
        destruct d; simpl in *; try discriminate.
        destruct d; simpl in *; try discriminate.
        inversion H; subst; clear H.
        specialize (IHe denv (Dlocal (dcoll l)) H0 H1).
        inversion IHe; inversion H2; constructor; assumption.
      - simpl in H1.
        rewrite <- listo_to_olist_simpl_lift_map in H1.
        case_eq (lift_map
           (fun x : string * dnnrc_base =>
            match dnnrc_base_eval denv (snd x) with
            | Some (Dlocal _) => None
            | Some (Ddistr coll) => Some (fst x, coll)
            | None => None
            end) r); intros; rewrite H2 in H1; try discriminate.
        case_eq (plug_eval h l op); intros;
        rewrite H3 in H1; simpl in *; try discriminate.
        destruct d; try discriminate.
        inversion H1; subst; clear H1.
        assert (data_normalized h (dcoll l0)).
        + apply (plug_normalized h op l (dcoll l0)); trivial.
          apply Forall_dcoll_map_lift.
          unfold bindings_of_coll_bindings.
          apply (@dnnrc_base_alg_bindings_normalized _ denv l r H0); eauto.
          rewrite Forall_forall in *. eauto.
        + econstructor; inversion H1; assumption.
    Qed.

    Corollary dnnrc_base_eval_normalized_local {plug:AlgPlug plug_type} denv e {d} :
      Forall (ddata_normalized h) (map snd constant_env) ->
      Forall (ddata_normalized h) (map snd denv) ->
      dnnrc_base_eval denv e = Some (Dlocal d) ->
      data_normalized h d.
    Proof.
      intros.
      assert (ddata_normalized h (Dlocal d)).
      apply (dnnrc_base_eval_normalized denv e); assumption.
      inversion H2; assumption.
    Qed.
         
    Fixpoint dnnrc_base_subst_var_to_const (constants:list string) (e:dnnrc_base) : dnnrc_base
      := match e with
         | DNNRCGetConstant a y => DNNRCGetConstant a y
         | DNNRCVar a y => if in_dec string_eqdec y constants
                        then DNNRCGetConstant a y
                        else DNNRCVar a y
         | DNNRCConst a d => DNNRCConst a d
         | DNNRCBinop a bop e1 e2 => DNNRCBinop a bop
                                            (dnnrc_base_subst_var_to_const constants e1)
                                            (dnnrc_base_subst_var_to_const constants e2)
         | DNNRCUnop a uop e1 => DNNRCUnop a uop (dnnrc_base_subst_var_to_const constants e1)
         | DNNRCLet a y e1 e2 => 
           DNNRCLet a y 
                   (dnnrc_base_subst_var_to_const constants e1) 
                   (if in_dec string_eqdec y constants
                    then e2
                    else dnnrc_base_subst_var_to_const constants e2)
         | DNNRCFor a y e1 e2 => 
           DNNRCFor a y 
                   (dnnrc_base_subst_var_to_const constants e1) 
                   (if in_dec string_eqdec y constants
                    then e2
                    else dnnrc_base_subst_var_to_const constants e2)
         | DNNRCIf a e1 e2 e3 => DNNRCIf a
                                 (dnnrc_base_subst_var_to_const constants e1)
                                 (dnnrc_base_subst_var_to_const constants e2)
                                 (dnnrc_base_subst_var_to_const constants e3)
         | DNNRCEither a ed xl el xr er =>
           DNNRCEither a (dnnrc_base_subst_var_to_const constants ed)
                      xl
                      (if in_dec string_eqdec xl constants
                       then el
                       else dnnrc_base_subst_var_to_const constants el)
                      xr
                      (if in_dec string_eqdec xr constants
                       then er
                       else dnnrc_base_subst_var_to_const constants er)
         | DNNRCGroupBy a g sl e1 => DNNRCGroupBy a g sl (dnnrc_base_subst_var_to_const constants e1)
         | DNNRCCollect a e1 => DNNRCCollect a (dnnrc_base_subst_var_to_const constants e1)
         | DNNRCDispatch a e1 => DNNRCDispatch a (dnnrc_base_subst_var_to_const constants e1)
         | DNNRCAlg a p l => DNNRCAlg a p l
         end.
  End GenDNNRCBase.

  Section NraEnvPlug.
    Definition nraenv_eval h aconstant_env op :=
      let aenv := drec nil in (* empty local environment to start, which is an empty record *)
      let aid := dcoll ((drec nil)::nil) in (* to be checked *)
      nraenv_core_eval h (bindings_of_coll_bindings aconstant_env) op aenv aid.

    Lemma nraenv_eval_normalized h :
      forall op:nraenv_core, forall (constant_env:coll_bindings) (o:data),
      Forall (fun x => data_normalized h (snd x)) (bindings_of_coll_bindings constant_env) ->
      nraenv_eval h constant_env op = Some o ->
      data_normalized h o.
    Proof.
      intros.
      specialize (@nraenv_core_eval_normalized _ h (bindings_of_coll_bindings constant_env) op (drec nil) (dcoll ((drec nil)::nil))); intros.
      unfold bindings_of_coll_bindings.
      apply H1; try assumption.
      repeat constructor.
      repeat constructor.
    Qed.

    Global Program Instance NRAEnvPlug : (@AlgPlug nraenv_core) :=
      mkAlgPlug nraenv_eval nraenv_eval_normalized.

    Definition dnnrc_nraenv_core {A} := @dnnrc_base A nraenv_core.

  End NraEnvPlug.

End DNNRCBase.

(* XXX Coq 8.6 Error: The "clear implicits" flag is incompatible with implicit annotations *)
(* Global Arguments AlgPlug {fruntime} plug_type : clear implicits.  *)
(* Global Arguments dnnrc {fruntime} A plug_type: clear implicits.  *)

Tactic Notation "dnnrc_base_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "DNNRCGetConstant"%string
  | Case_aux c "DNNRCVar"%string
  | Case_aux c "DNNRCConst"%string
  | Case_aux c "DNNRCBinop"%string
  | Case_aux c "DNNRCUnop"%string
  | Case_aux c "DNNRCLet"%string
  | Case_aux c "DNNRCFor"%string
  | Case_aux c "DNNRCIf"%string
  | Case_aux c "DNNRCEither"%string
  | Case_aux c "DNNRCGroupBy"%string
  | Case_aux c "DNNRCCollect"%string
  | Case_aux c "DNNRCDispatch"%string
  | Case_aux c "DNNRCAlg"%string ].

(* end hide *)

