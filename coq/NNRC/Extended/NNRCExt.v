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

Section NNRCExt.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.

  Require Import Utils BasicRuntime.
  Require Import NNRC.

  (** Named Nested Relational Calculus - Extended *)

  Context {fruntime:foreign_runtime}.
  Context {h:brand_relation_t}.
  
  Definition var := string.
  
  Inductive nnrc_ext :=
  | NNRCExt_Var : var -> nnrc_ext
  | NNRCExt_Const : data -> nnrc_ext
  | NNRCExt_Binop : binOp -> nnrc_ext -> nnrc_ext -> nnrc_ext
  | NNRCExt_Unop : unaryOp -> nnrc_ext -> nnrc_ext
  | NNRCExt_Let : var -> nnrc_ext -> nnrc_ext -> nnrc_ext
  | NNRCExt_For : var -> nnrc_ext -> nnrc_ext -> nnrc_ext
  | NNRCExt_If : nnrc_ext -> nnrc_ext -> nnrc_ext -> nnrc_ext
  | NNRCExt_Either : nnrc_ext -> var -> nnrc_ext -> var -> nnrc_ext -> nnrc_ext
  | NNRCExt_GroupBy : string -> list string -> nnrc_ext -> nnrc_ext.

  Tactic Notation "nnrc_ext_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "NNRCExt_Var"%string
    | Case_aux c "NNRCExt_Const"%string
    | Case_aux c "NNRCExt_Binop"%string
    | Case_aux c "NNRCExt_Unop"%string
    | Case_aux c "NNRCExt_Let"%string
    | Case_aux c "NNRCExt_For"%string
    | Case_aux c "NNRCExt_If"%string
    | Case_aux c "NNRCExt_Either"%string
    | Case_aux c "NNRCExt_GroupBy"%string].

  Global Instance nnrc_ext_eqdec : EqDec nnrc_ext eq.
  Proof.
    change (forall x y : nnrc_ext,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binOp_eqdec | apply unaryOp_eqdec
                 | apply data_eqdec | apply string_eqdec].
    - decide equality; apply string_dec.
  Defined.

  Section macros.
    Definition nnrc_group_by (g:string) (sl:list string) (e:nrc) : nrc :=
      let t0 := "$group0"%string in
      let t1 := "$group1"%string in
      let t2 := "$group2"%string in
      let t3 := "$group3"%string in
      NRCLet t0 e
             (NRCFor t2
                     (NRCUnop ADistinct
                              (NRCFor t1 (NRCVar t0) (NRCUnop (ARecProject sl) (NRCVar t1))))
                     (NRCBinop AConcat
                               (NRCUnop (ARec g)
                                        (NRCUnop AFlatten
                                                 (NRCFor t3 (NRCVar t0)
                                                         (NRCIf (NRCBinop AEq (NRCVar t2) (NRCUnop (ARecProject sl) (NRCVar t3))) (NRCVar t3) (NRCConst (dcoll nil))))))
                               (NRCVar t2))).

  End macros.
  
  Section translation.
    Fixpoint nnrc_ext_to_nnrc (e:nnrc_ext) : nrc :=
      match e with
      | NNRCExt_Var v => NRCVar v
      | NNRCExt_Const d => NRCConst d
      | NNRCExt_Binop b e1 e2 =>
        NRCBinop b (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2)
      | NNRCExt_Unop u e1 =>
        NRCUnop u (nnrc_ext_to_nnrc e1)
      | NNRCExt_Let v e1 e2 =>
        NRCLet v (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2)
      | NNRCExt_For v e1 e2 =>
        NRCFor v (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2)
      | NNRCExt_If e1 e2 e3 =>
        NRCIf (nnrc_ext_to_nnrc e1) (nnrc_ext_to_nnrc e2) (nnrc_ext_to_nnrc e3)
      | NNRCExt_Either e1 v2 e2 v3 e3 =>
        NRCEither (nnrc_ext_to_nnrc e1) v2 (nnrc_ext_to_nnrc e2) v3 (nnrc_ext_to_nnrc e3)
      | NNRCExt_GroupBy g sl e1 =>
        nnrc_group_by g sl (nnrc_ext_to_nnrc e1)
      end.

    Fixpoint nnrc_to_nnrc_ext (e:nrc) : nnrc_ext :=
      match e with
      | NRCVar v => NNRCExt_Var v
      | NRCConst d => NNRCExt_Const d
      | NRCBinop b e1 e2 =>
        NNRCExt_Binop b (nnrc_to_nnrc_ext e1) (nnrc_to_nnrc_ext e2)
      | NRCUnop u e1 =>
        NNRCExt_Unop u (nnrc_to_nnrc_ext e1)
      | NRCLet v e1 e2 =>
        NNRCExt_Let v (nnrc_to_nnrc_ext e1) (nnrc_to_nnrc_ext e2)
      | NRCFor v e1 e2 =>
        NNRCExt_For v (nnrc_to_nnrc_ext e1) (nnrc_to_nnrc_ext e2)
      | NRCIf e1 e2 e3 =>
        NNRCExt_If (nnrc_to_nnrc_ext e1) (nnrc_to_nnrc_ext e2) (nnrc_to_nnrc_ext e3)
      | NRCEither e1 v2 e2 v3 e3 =>
        NNRCExt_Either (nnrc_to_nnrc_ext e1) v2 (nnrc_to_nnrc_ext e2) v3 (nnrc_to_nnrc_ext e3)
      end.

    Lemma nnrc_to_nnrc_ext_round_trips (e:nrc) :
      (nnrc_ext_to_nnrc (nnrc_to_nnrc_ext e)) = e.
    Proof.
      induction e; simpl; try reflexivity;
        try (rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity);
        try (rewrite IHe1; rewrite IHe2; reflexivity);
        try (rewrite IHe; reflexivity).
    Qed.

  End translation.

  Section semantics.
    (** Semantics of NNRCExt *)

    Definition nnrc_ext_eval (env:bindings) (e:nnrc_ext) : option data :=
      nrc_eval h env (nnrc_ext_to_nnrc e).

    Remark nnrc_ext_to_nnrc_eq (e:nnrc_ext):
      forall env,
        nnrc_ext_eval env e = nrc_eval h env (nnrc_ext_to_nnrc e).
    Proof.
      intros; reflexivity.
    Qed.

    Remark nnrc_to_nnrc_ext_eq (e:nrc):
      forall env,
        nrc_eval h env e = nnrc_ext_eval env (nnrc_to_nnrc_ext e).
    Proof.
      unfold nnrc_ext_eval.
      rewrite nnrc_to_nnrc_ext_round_trips.
      reflexivity.
    Qed.

    (* we are only sensitive to the environment up to lookup *)
    Global Instance nnrc_ext_eval_lookup_equiv_prop :
      Proper (lookup_equiv ==> eq ==> eq) nnrc_ext_eval.
    Proof.
      generalize nrc_eval_lookup_equiv_prop; intros.
      unfold Proper, respectful, lookup_equiv in *; intros; subst.
      unfold nnrc_ext_eval.
      rewrite (H h x y H0 (nnrc_ext_to_nnrc y0) (nnrc_ext_to_nnrc y0)).
      reflexivity.
      reflexivity.
    Qed.
    
  End semantics.

End NNRCExt.

(* begin hide *)

Tactic Notation "nnrc_ext_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NRCExt_Var"%string
  | Case_aux c "NRCExt_Const"%string
  | Case_aux c "NRCExt_Binop"%string
  | Case_aux c "NRCExt_Unop"%string
  | Case_aux c "NRCExt_Let"%string
  | Case_aux c "NRCExt_For"%string
  | Case_aux c "NRCExt_If"%string
  | Case_aux c "NRCExt_Either"%string
  | Case_aux c "NRCExt_GroupBy"%string].

(* end hide *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
