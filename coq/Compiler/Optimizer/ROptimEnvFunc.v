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

Section ROptimEnvFunc.

  Require Import List ListSet String.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.

  Require Import RAlgEq RAlgEnv RAlgEnvEq RAlgEnvSize ROptim ROptimEnv.

  Context {fruntime:foreign_runtime}.

  (* Optimization functions correponding to the equivalence relations *)

  Local Open Scope alg_scope.
  Local Open Scope algenv_scope.

  (** Apply the function f to the direct child of p *)
  Definition algenv_map (f: algenv -> algenv) (p: algenv) :=
    match p with
      | ANID => ANID
      | ANConst rd => ANConst rd
      | ANBinop bop op1 op2 => ANBinop bop (f op1) (f op2)
      | ANUnop uop op1 => ANUnop uop (f op1)
      | ANMap op1 op2 => ANMap (f op1) (f op2)
      | ANMapConcat op1 op2 => ANMapConcat (f op1) (f op2)
      | ANProduct op1 op2 => ANProduct (f op1) (f op2)
      | ANSelect op1 op2 => ANSelect (f op1) (f op2)
      | ANEither op1 op2 => ANEither (f op1) (f op2)
      | ANEitherConcat op1 op2 => ANEitherConcat (f op1) (f op2)
      | ANDefault op1 op2 => ANDefault (f op1) (f op2)
      | ANApp op1 op2 => ANApp (f op1) (f op2)
      | ANGetConstant s => ANGetConstant s
      | ANEnv => ANEnv
      | ANAppEnv op1 op2 => ANAppEnv (f op1) (f op2)
      | ANMapEnv op1 => ANMapEnv (f op1)
    end.

  Lemma algenv_map_correctness:
    forall f: algenv -> algenv,
    forall p: algenv,
      (forall p', f p'  ≡ₑ p') -> algenv_map f p ≡ₑ p.
  Proof.
    intros f p Hf.
    algenv_cases (induction p) Case;
      try solve [simpl; repeat rewrite Hf; reflexivity].
  Qed.

  (** Apply the function f to all subexpression fo p. *)
  (* Fixpoint algenv_map_deep (f: algenv -> algenv) (p: algenv) := *)
  (*   f (algenv_map (fun p' => algenv_map_deep f p') p). *)
  (* Java equivalent: NraOptimizer.talgenv_map_deep (sic) *)
  Fixpoint algenv_map_deep (f: algenv -> algenv) (p: algenv) :=
    match p with
      | ANID => f ANID
      | ANConst rd => f (ANConst rd)
      | ANBinop bop op1 op2 => f (ANBinop bop (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANUnop uop op1 => f (ANUnop uop (algenv_map_deep f op1))
      | ANMap op1 op2 => f (ANMap (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANMapConcat op1 op2 => f (ANMapConcat (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANProduct op1 op2 => f (ANProduct (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANSelect op1 op2 => f (ANSelect (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANDefault op1 op2 => f (ANDefault (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANEither op1 op2 => f (ANEither (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANEitherConcat op1 op2 => f (ANEitherConcat (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANApp op1 op2 => f (ANApp (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANGetConstant s => f (ANGetConstant s)
      | ANEnv => f ANEnv
      | ANAppEnv op1 op2 => f (ANAppEnv (algenv_map_deep f op1) (algenv_map_deep f op2))
      | ANMapEnv op1 => f (ANMapEnv (algenv_map_deep f op1))
    end.

  Lemma algenv_map_deep_correctness:
    forall f: algenv -> algenv,
    forall p: algenv,
      (forall p', f p'  ≡ₑ p') -> algenv_map_deep f p ≡ₑ p.
  Proof.
    intros f p Hf.
    algenv_cases (induction p) Case;
      try solve [simpl; repeat rewrite Hf; reflexivity];
      try solve [ simpl; repeat rewrite Hf; rewrite IHp; reflexivity ];
      try solve [ simpl; repeat rewrite Hf; rewrite IHp1; rewrite IHp2; reflexivity ].
  Qed.

  (* Java equivalent: NraOptimizer.optim_iter *)
  Fixpoint optim_iter (optim: algenv -> algenv) (fuel: nat) (p: algenv) :=
    match fuel with
      | 0 => p
      | S n => optim_iter optim n (optim p)
    end.

  Lemma optim_iter_correctness optim n p:
    (forall p', optim p' ≡ₑ p') -> optim_iter optim n p ≡ₑ p.
  Proof.
    generalize p; clear p.
    induction n; try reflexivity.
    intros p Hoptim.
    simpl.
    rewrite IHn; try assumption.
    apply Hoptim.
  Qed.

  Require Import Recdef.
  Require Import Compare_dec.

  (* Java equivalent: NraOptimizer.optim_size (inlined) *) 
  Function optim_cost (optim: algenv -> algenv) (cost: algenv -> nat) (p: algenv) { measure cost p } :=
    let p' := optim p in
    match nat_compare (cost p') (cost p) with
      | Lt => optim_cost optim cost p'
      | _ => p'
    end.
  Proof.
    intros optim cost p Hcmp.
    apply nat_compare_lt in Hcmp.
    exact Hcmp.
  Defined.

  Lemma optim_cost_correctness optim cost p:
    (forall p', optim p' ≡ₑ p') -> optim_cost optim cost p ≡ₑ p.
  Proof.
    intros Hoptim.
    functional induction optim_cost optim cost p.
    - rewrite IHa.
      apply Hoptim.
    - apply Hoptim.
  Qed.

  Hint Rewrite optim_cost_correctness : optim_correct.

  (* Java equivalent: NraOptimizer.optim_size *)
  Definition optim_size (optim: algenv -> algenv) (p: algenv) :=
    optim_cost optim algenv_size p.

  Lemma optim_size_correctness optim p:
    (forall p', optim p' ≡ₑ p') -> optim_size optim p ≡ₑ p.
  Proof.
    intros Hoptim.
    unfold optim_size.
    apply optim_cost_correctness.
    assumption.
  Qed.

  Hint Rewrite optim_size_correctness : optim_correct.


  (* *************************** *)

  Ltac correctness_prover :=
          simpl; repeat progress (try match goal with
        | [|- context [match ?p with | _ => _ end] ] => destruct p
      end; try reflexivity; try autorewrite with envmap_eqs; try unfold equiv in *; try subst).

  Ltac prove_correctness p :=
    algenv_cases (destruct p) Case;
    correctness_prover.

  (* *************************** *)

  (* XXX Do we want to put the 3 following rules? *)
  (* P1 ∧ P2 ≡ P2 ∧ P1 *)
  (* (P1 ⋃ P2) ⋃ P3 ≡ P1 ⋃ (P2 ⋃ P3) *)

  (* σ⟨ P ⟩(P1 ⋃ P2) ≡ σ⟨ P ⟩(P1) ⋃ σ⟨ P ⟩(P2) *)
  Definition envunion_select_distr_fun (p: algenv) :=
    match p with
        ANSelect p (ANBinop AUnion p1 p2) =>
        ANBinop AUnion (ANSelect p p1) (ANSelect p p2)
      | _ => p
    end.

  Lemma envunion_select_distr_fun_correctness p:
    envunion_select_distr_fun p ≡ₑ p.
  Proof.
    Hint Rewrite envunion_select_distr : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite envunion_select_distr_fun_correctness : optim_correct.

  Definition envmap_singleton_fun (p: algenv) :=
    match p with
        ANMap (p1) (ANUnop AColl p2) => ANUnop AColl (ANApp p1 p2)
      | _ => p
    end.

  Lemma envmap_singleton_fun_correctness p:
    envmap_singleton_fun p ≡ₑ p.
  Proof.
    Hint Rewrite envmap_singleton : envmap_eqs.
    prove_correctness p.
  Qed.


  Hint Rewrite envmap_singleton_fun_correctness : optim_correct.

  (* χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ≡ χ⟨ P1 ◯ P2 ⟩( P3 ) *)
  Definition envmap_map_compose_fun (p: algenv) :=
    match p with
        ANMap (p1) (ANMap (p2) (p3)) => ANMap (ANApp p1 p2) (p3)
      | _ => p
    end.

  Lemma envmap_map_compose_fun_correctness p:
    envmap_map_compose_fun p ≡ₑ p.
  Proof.
    Hint Rewrite envmap_map_compose : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite envmap_map_compose_fun_correctness : optim_correct.

  (* (p1 ◯ p2) ◯ p3 ≡ p1 ◯ (p2 ◯ p3) *)
  Definition app_over_app_fun (p: algenv) :=
    match p with
        ANApp (ANApp p1 p2) p3 => ANApp p1 (ANApp p2 p3)
      | _ => p
    end.

  Lemma app_over_app_fun_correctness p:
    app_over_app_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_app : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_app_fun_correctness : optim_correct.

  (* [ a : P1 ] ◯ P2 ≡ [ a : P1 ◯ P2 ] *)
  Definition app_over_rec_fun (p: algenv) :=
    match p with
        ANApp (ANUnop (ARec s) p1) p2 => ANUnop (ARec s) (ANApp p1 p2)
      | _ => p
    end.

  Lemma app_over_rec_fun_correctness p:
    app_over_rec_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_rec : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_rec_fun_correctness : optim_correct.

  (* ♯flatten({ ♯flatten( p ) }) ≡ ♯flatten( p ) *)
  (* ♯flatten({ ‵{| p |} }) ≡ ♯flatten( p ) *)
  (* ♯flatten({ χ⟨ p1 ⟩( p2 ) }) ≡ χ⟨ p1 ⟩( p2 ) *)
  (* ♯flatten( ‵{| p1 ⊗ p2 |} ) ≡ₑ p1 ⊗ p2 *)
  Definition envflatten_coll_fun (p: algenv) :=
    match p with
        ANUnop AFlatten (ANUnop AColl p') =>
        match p' with
            ANUnop AFlatten _ => p'
          | ANUnop AColl _ => p'
          | ANMap _ _ => p'
          | ANBinop AMergeConcat _ _ => p'
          | _ => p
        end
      | _ => p
    end.

  Lemma envflatten_coll_fun_correctness p:
    envflatten_coll_fun (p) ≡ₑ p.
  Proof.
    Hint Rewrite envflatten_coll_mergeconcat envflatten_coll_coll envflatten_coll_flatten envflatten_coll_map : envmap_eqs.

    prove_correctness p.
  Qed.

  Hint Rewrite envflatten_coll_fun_correctness : optim_correct.

  (* ♯flatten(χ⟨ χ⟨ ‵{| ID |} ⟩( ♯flatten( p1 ) ) ⟩( p2 ))
         ≡ₑ χ⟨ ‵{| ID |} ⟩(♯flatten(χ⟨ ♯flatten( p1 ) ⟩( p2 ))) *)
  Definition double_flatten_map_coll_fun (p: algenv) :=
    match p with
        ANUnop AFlatten (ANMap (ANMap (ANUnop AColl ANID) (ANUnop AFlatten p1)) (p2)) =>
        ANMap (ANUnop AColl ANID) (ANUnop AFlatten (ANMap (ANUnop AFlatten p1) (p2)))
      | _ => p
    end.

  Lemma double_flatten_map_coll_fun_correctness p:
    double_flatten_map_coll_fun (p) ≡ₑ p.
  Proof.
    Hint Rewrite double_flatten_map_coll : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite double_flatten_map_coll_fun_correctness : optim_correct.

  (* ♯flatten(χ⟨ { p1 } ⟩( p2 )) ≡ χ⟨ p1 ⟩( p2 ) *)
  Definition envflatten_map_coll_fun (p: algenv) :=
    match p with
        ANUnop AFlatten (ANMap (ANUnop AColl p1) (p2)) =>
        ANMap p1 p2
      | _ => p
    end.

  Lemma envflatten_map_coll_fun_correctness p:
    envflatten_map_coll_fun (p) ≡ₑ p.
  Proof.
    Hint Rewrite  envflatten_map_coll : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite envflatten_map_coll_fun_correctness : optim_correct.

  (* [ a1 : p1; a2 : p1 ].a2 ≡ₐ p1 *)
  Definition envdot_from_duplicate_r_fun (p: algenv) :=
    match p with
        ANUnop (ADot s) (ANBinop AConcat (ANUnop (ARec s1) p1) (ANUnop (ARec s2) p2)) =>
        if s == s2 then
          if p1 == p2 then
            p2
          else p
        else p
      | _ => p
    end.

  Lemma envdot_from_duplicate_r_fun_correctness p:
    envdot_from_duplicate_r_fun p ≡ₑ p.
  Proof.

    Hint Rewrite envdot_from_duplicate_r : envmap_eqs.

    prove_correctness p.
  Qed.

  Hint Rewrite envdot_from_duplicate_r_fun_correctness : optim_correct.

  (* [ a1 : p1; a2 : p1 ].a1 ≡ₐ p1 *)
  Definition envdot_from_duplicate_l_fun (p: algenv) :=
    match p with
        ANUnop (ADot s) (ANBinop AConcat (ANUnop (ARec s1) p1) (ANUnop (ARec s2) p2)) =>
        if s == s1 then
          if p1 == p2 then
            p1
          else p
        else p
      | _ => p
    end.

  Lemma envdot_from_duplicate_l_fun_correctness p:
    envdot_from_duplicate_l_fun p ≡ₑ p.
  Proof.

    Hint Rewrite envdot_from_duplicate_l : envmap_eqs.

    prove_correctness p.
  Qed.

  Hint Rewrite envdot_from_duplicate_l_fun_correctness : optim_correct.

  (* χ⟨ ID ⟩( { P } ) ≡ { P } *)
  (* χ⟨ ID ⟩( ♯flatten(P) ) ≡ ♯flatten(P) *)
  Definition envmap_into_id_fun (p: algenv) :=
    match p with
        ANMap ANID (ANUnop AColl p) => ANUnop AColl p
      | ANMap ANID (ANUnop AFlatten p) => ANUnop AFlatten p
      | _ => p
    end.
  Lemma envmap_into_id_fun_correctness p:
    envmap_into_id_fun p ≡ₑ p.
  Proof.
    Hint Rewrite envmap_into_id envmap_into_id_flatten : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite envmap_into_id_fun_correctness : optim_correct.

  (* { [ s1 : p1 ] } × { [ s2 : p2 ] } ≡ { [ s1 : p1; s2 : p2 ] } *)
  Definition product_singletons_fun (p: algenv) :=
    match p with
        ANProduct (ANUnop AColl (ANUnop (ARec s1) p1))
                  (ANUnop AColl (ANUnop (ARec s2) p2)) =>
        ANUnop AColl
               (ANBinop AConcat (ANUnop (ARec s1) p1) (ANUnop (ARec s2) p2))
      | _ => p
    end.

  Lemma product_singletons_fun_correctness p:
    product_singletons_fun p ≡ₑ p.
  Proof.
    Hint Rewrite product_singletons : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite product_singletons_fun_correctness : optim_correct.

  (* p ◯ ID ≡ p *)
  Definition app_over_id_fun (p: algenv):=
    match p with
        ANApp p' ANID => p'
      | _ => p
    end.

  Lemma app_over_id_fun_correctness p:
    app_over_id_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_id : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_id_fun_correctness : optim_correct.

  (* ID ◯ p ≡ p *)
  Definition app_over_id_l_fun (p: algenv):=
    match p with
        ANApp ANID p' => p'
      | _ => p
    end.
  Lemma app_over_id_l_fun_correctness p:
    app_over_id_l_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_id_l : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_id_l_fun_correctness : optim_correct.

  (* (ANUnop u p1) ◯ p2 ≡ₑ (ANUnop u (p1 ◯ p2)) *)
  Definition app_over_unop_fun (p: algenv) :=
    match p with
        ANApp (ANUnop u p1) p2 => ANUnop u (ANApp p1 p2)
      | _ => p
    end.

  Lemma app_over_unop_fun_correctness p:
    app_over_unop_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_unop : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_unop_fun_correctness : optim_correct.

  (* (ENV ⊗ ID) ◯ p ≡ₑ ENV ⊗ p *)
  Definition app_over_merge_fun (p: algenv) :=
    match p with
        ANApp (ANBinop AMergeConcat ANEnv ANID) p =>
        ANBinop AMergeConcat ANEnv p
      | _ => p
    end.

  Lemma app_over_merge_fun_correctness p:
    app_over_merge_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_merge : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_merge_fun_correctness : optim_correct.

  (* (ANBinop b p2 (ANConst d) ◯ p1) ≡ (ANBinop b (p2 ◯ p1) (ANConst d)) *)
  Definition app_over_binop_l_fun p :=
    match p with
        ANApp (ANBinop b p2 (ANConst d)) p1 =>
        ANBinop b (ANApp p2 p1) (ANConst d)
      | _ => p
    end.

  Lemma app_over_binop_l_fun_correctness p:
    app_over_binop_l_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_binop_l : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_binop_l_fun_correctness : optim_correct.

  (* σ⟨ p1 ⟩( p2 ) ◯ p0 ≡ σ⟨ p1 ⟩( p2 ◯ p0 ) *)
  Definition app_over_select_fun p :=
    match p with
        ANApp (ANSelect p1 p2) p0 =>
        ANSelect p1 (ANApp p2 p0)
      | _ => p
    end.

  Lemma app_over_select_fun_correctness p:
    app_over_select_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_select : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_select_fun_correctness : optim_correct.

  (* χ⟨ p1 ⟩( p2 ) ◯ p0 ≡ χ⟨ p1 ⟩( p2 ◯ p0 ) *)
  Definition app_over_map_fun p :=
    match p with
        ANApp (ANMap p1 p2) p0 =>
        ANMap p1 (ANApp p2 p0)
      | _ => p
    end.

  Lemma app_over_map_fun_correctness p:
    app_over_map_fun p ≡ₑ p.
  Proof.
    Hint Rewrite app_over_map : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite app_over_map_fun_correctness : optim_correct.

  (* χᵉ⟨ { ENV } ⟩ ◯ₑ ♯flatten(p) ≡ χ⟨ { ID } ⟩(♯flatten(p)) *)
  Definition appenv_over_mapenv_fun p :=
    match p with
        ANAppEnv (ANMapEnv (ANUnop AColl ANEnv)) (ANUnop AFlatten p) =>
        ANMap (ANUnop AColl ANID) (ANUnop AFlatten p)
      | _ => p
    end.

  Lemma appenv_over_mapenv_fun_correctness p:
    appenv_over_mapenv_fun p ≡ₑ p.
  Proof.
    Hint Rewrite appenv_over_mapenv : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite  appenv_over_mapenv_fun_correctness : optim_correct.

  (* (χᵉ⟨ { { ENV } } ⟩(ID) ◯ₑ ♯flatten(p)) ≡ χ⟨ { { ID } } ⟩(♯flatten(p)) *)
  Definition appenv_over_mapenv_coll_fun p :=
    match p with
        ANAppEnv (ANMapEnv (ANUnop AColl (ANUnop AColl ANEnv))) (ANUnop AFlatten p) =>
        ANMap (ANUnop AColl (ANUnop AColl ANID)) (ANUnop AFlatten p)
      | _ => p
    end.

  Lemma appenv_over_mapenv_coll_fun_correctness p:
    appenv_over_mapenv_coll_fun p ≡ₑ p.
  Proof.
    Hint Rewrite appenv_over_mapenv_coll : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite appenv_over_mapenv_coll_fun_correctness : optim_correct.

  (* χᵉ⟨ { ENV.e } ⟩ ◯ₑ (ENV ⊗ ID) ≡ₑ χ⟨ { ID.e } ⟩(ENV ⊗ ID) *)
  Definition appenv_over_mapenv_merge_fun (p: algenv) :=
    match p with
        ANAppEnv
          (ANMapEnv (ANUnop AColl (ANUnop (ADot s) ANEnv)))
          (ANBinop AMergeConcat ANEnv ANID) =>
        ANMap (ANUnop AColl (ANUnop (ADot s) ANID)) (ANBinop AMergeConcat ANEnv ANID)
      | _ => p
    end.

  Lemma appenv_over_mapenv_merge_fun_correction p:
    appenv_over_mapenv_merge_fun p ≡ₑ p.
  Proof.
    Hint Rewrite appenv_over_mapenv_merge : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite appenv_over_mapenv_merge_fun_correction : optim_correct.

  (* (ANBinop ID.a1 ID.a2) ◯ ([ a1 : p1; a2 : p2 ]) ≡ (ANBinop b p1 p2) *)
  Definition binop_over_rec_pair_fun (p: algenv) :=
    match p with
        ANApp
          (ANBinop b
                   (ANUnop (ADot a1) ANID)
                   (ANUnop (ADot a2) ANID))
          (ANBinop AConcat
                   (ANUnop (ARec a1') p1)
                   (ANUnop (ARec a2') p2)) =>
        if a1 == a1' then
          if a2 == a2' then
            if a1 == a2 then
              p
            else
              ANBinop b p1 p2
          else
            p
        else
          p
        (* if andb (andb (a1 == a1') (a2 == a2')) (a1 <> a2) then p *)
        (* else ANUnop AColl (ANBinop AEq p1 p2) *)
      | _ => p
    end.

  Lemma binop_over_rec_pair_fun_correctness p:
    binop_over_rec_pair_fun p ≡ₑ p.
  Proof.
    Hint Rewrite binop_over_rec_pair : envmap_eqs.
    prove_correctness p.
    unfold complement in c.
    unfold not.
    apply c.
  Qed.

  Hint Rewrite binop_over_rec_pair_fun_correctness : optim_correct.

  (* ([ a1 : p1; a2 : d ]) ◯ p2 ≡ [ a1 : p1 ◯ p2; a2 : d ] *)
  Definition concat_id_left_fun (p: algenv) :=
    match p with
        ANApp
          (ANBinop AConcat (ANUnop (ARec s1) p1)
                   (ANUnop (ARec s2) (ANConst d))) p2 =>
        ANBinop AConcat (ANUnop (ARec s1) (ANApp p1 p2))
                (ANUnop (ARec s2) (ANConst d))
      | _ => p
    end.

  Lemma concat_id_left_fun_correctness p:
    concat_id_left_fun p ≡ₑ p.
  Proof.
    Hint Rewrite concat_id_left : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite concat_id_left_fun_correctness : optim_correct.

  (* optimizations for either *)
  Definition either_app_over_dleft_fun (p:algenv) :=
    match p with
      | ANApp
          (ANEither p₁ p₂)
          (ANConst (dleft d))
        => ANApp p₁ (ANConst d)
      | _ => p
    end.

  Definition either_app_over_dleft_fun_correctness p :
    either_app_over_dleft_fun p ≡ₑ p.
  Proof.
    Hint Rewrite either_app_over_dleft : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite either_app_over_dleft_fun_correctness : optim_correct.

  Definition either_app_over_dright_fun (p:algenv) :=
    match p with
      | ANApp
          (ANEither p₁ p₂)
          (ANConst (dright d))
        => ANApp p₂ (ANConst d)
      | _ => p
    end.

  Definition either_app_over_dright_fun_correctness p :
    either_app_over_dright_fun p ≡ₑ p.
  Proof.
    Hint Rewrite either_app_over_dright : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite either_app_over_dright_fun_correctness : optim_correct.

  Definition either_app_over_aleft_fun (p:algenv) :=
    match p with
      | ANApp
          (ANEither p₁ p₂)
          (ANUnop ALeft p)
        => ANApp p₁ p
      | _ => p
    end.

  Definition either_app_over_aleft_fun_correctness p :
    either_app_over_aleft_fun p ≡ₑ p.
  Proof.
    Hint Rewrite either_app_over_aleft : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite either_app_over_aleft_fun_correctness : optim_correct.

  Definition either_app_over_aright_fun (p:algenv) :=
    match p with
      | ANApp
          (ANEither p₁ p₂)
          (ANUnop ARight p)
        => ANApp p₂ p
      | _ => p
    end.

  Definition either_app_over_aright_fun_correctness p :
    either_app_over_aright_fun p ≡ₑ p.
  Proof.
    Hint Rewrite either_app_over_aright : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite either_app_over_aright_fun_correctness : optim_correct.

  (* optimizations for rproject *)
    Definition rproject_over_concat_fun (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
          (ANBinop AConcat p₁ p₂)
        => ANBinop AConcat (ANUnop (ARecProject sl) p₁) (ANUnop (ARecProject sl) p₂)
      | _ => p
    end.

  Definition rproject_over_concat_fun_correctness p :
    rproject_over_concat_fun p ≡ₑ p.
  Proof.
    Hint Rewrite rproject_over_concat : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite rproject_over_concat_fun_correctness : optim_correct.

  Definition rproject_over_const_fun (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
          (ANConst (drec l))
        => ANConst (drec (rproject l sl))
      | _ => p
    end.

  Definition rproject_over_const_fun_correctness p :
    rproject_over_const_fun p ≡ₑ p.
  Proof.
    Hint Rewrite rproject_over_const : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite rproject_over_const_fun_correctness : optim_correct.
  
  Definition rproject_over_rec_fun (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
          (ANUnop (ARec s) p₁)
        => if in_dec string_dec s sl
           then ANUnop (ARec s) p₁
           else ‵[||] ◯ p₁ 
      | _ => p
    end.

  Definition rproject_over_rec_fun_correctness p :
    rproject_over_rec_fun p ≡ₑ p.
  Proof.
    Hint Rewrite rproject_over_rec_in using solve[auto] : envmap_eqs.
    Hint Rewrite rproject_over_rec_nin using solve[auto] : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite rproject_over_rec_fun_correctness : optim_correct.
  
    Definition rproject_over_rproject_fun (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl1)
          (ANUnop (ARecProject sl2) p1)
        => ANUnop (ARecProject (set_inter string_dec sl2 sl1)) p1
      | _ => p
    end.

  Definition rproject_over_rproject_fun_correctness p :
    rproject_over_rproject_fun p ≡ₑ p.
  Proof.
    Hint Rewrite rproject_over_rproject : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite rproject_over_rproject_fun_correctness : optim_correct.

   Definition rproject_over_either_fun (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
          (ANEither p₁ p₂)
        => ANEither (ANUnop (ARecProject sl) p₁) (ANUnop (ARecProject sl) p₂)
      | _ => p
    end.

  Definition rproject_over_either_fun_correctness p :
    rproject_over_either_fun p ≡ₑ p.
  Proof.
    Hint Rewrite rproject_over_either : envmap_eqs.
    prove_correctness p.
  Qed.

  Hint Rewrite rproject_over_either_fun_correctness : optim_correct.

  
  (* *************************** *)
  Definition head_optim (p: algenv) :=
    (app_over_app_fun
       (envmap_into_id_fun
          (product_singletons_fun
             (envmap_singleton_fun
                (envmap_map_compose_fun
                   (app_over_rec_fun
                      (envflatten_coll_fun
                         (double_flatten_map_coll_fun
                            (envflatten_map_coll_fun
                               (app_over_id_fun
                                  (app_over_id_l_fun
                                     (app_over_unop_fun
                                        (app_over_merge_fun
                                           (app_over_binop_l_fun
                                              (app_over_select_fun
                                                 (app_over_map_fun
                                                    (appenv_over_mapenv_fun
                                                       (appenv_over_mapenv_coll_fun
                                                          (appenv_over_mapenv_merge_fun
                                                             (binop_over_rec_pair_fun
                                                                (concat_id_left_fun
                                                                   (either_app_over_dleft_fun
                                                                      (either_app_over_dright_fun
                                                                         (either_app_over_aleft_fun
                                                                            (either_app_over_aright_fun
                                                                               (rproject_over_concat_fun
                                                                                  (rproject_over_const_fun
                                                                                     (rproject_over_rec_fun
                                                                                        (rproject_over_rproject_fun
                                                                                           (rproject_over_either_fun
                                                                                              p)))))))))))))))))))))))))))))).

  Lemma head_optim_correctness p:
    head_optim (p) ≡ₑ p.
  Proof.
    unfold head_optim.
    autorewrite with optim_correct.
    reflexivity.
  Qed.

  Hint Rewrite head_optim_correctness : optim_correct.

  Definition optim1 (p: algenv) :=
    algenv_map_deep head_optim p.

  Lemma optim1_correctness p:
    optim1 (p) ≡ₑ p.
  Proof.
    unfold optim1.
    apply algenv_map_deep_correctness.
    intro p'.
    rewrite head_optim_correctness.
    reflexivity.
  Qed.

  Hint Rewrite optim1_correctness : optim_correct.

  Definition optim := optim_size (optim_iter optim1 5).

  Lemma optim_correctness p:
    optim p ≡ₑ p.
  Proof.
    unfold optim.
    rewrite optim_size_correctness; try reflexivity.
    intros p1.
    rewrite optim_iter_correctness; try reflexivity.
    intros p2.
    rewrite optim1_correctness; try reflexivity.
  Qed.

End ROptimEnvFunc.

(* begin hide *)
Hint Rewrite @envunion_select_distr_fun_correctness : optim_correct.
Hint Rewrite @envunion_select_distr_fun_correctness : optim_correct.
Hint Rewrite @envmap_singleton_fun_correctness : optim_correct.
Hint Rewrite @envmap_map_compose_fun_correctness : optim_correct.
Hint Rewrite @envflatten_coll_fun_correctness : optim_correct.
Hint Rewrite @double_flatten_map_coll_fun_correctness : optim_correct.
Hint Rewrite @envdot_from_duplicate_r_fun_correctness : optim_correct.
Hint Rewrite @envdot_from_duplicate_l_fun_correctness : optim_correct.
Hint Rewrite @envmap_into_id_fun_correctness : optim_correct.
Hint Rewrite @product_singletons_fun_correctness : optim_correct.
Hint Rewrite @app_over_id_fun_correctness : optim_correct.
Hint Rewrite @app_over_id_l_fun_correctness : optim_correct.
Hint Rewrite @app_over_unop_fun_correctness : optim_correct.
Hint Rewrite @app_over_merge_fun_correctness : optim_correct.
Hint Rewrite @app_over_binop_l_fun_correctness : optim_correct.
Hint Rewrite @app_over_select_fun_correctness : optim_correct.
Hint Rewrite @app_over_map_fun_correctness : optim_correct.
Hint Rewrite @appenv_over_mapenv_fun_correctness : optim_correct.
Hint Rewrite @appenv_over_mapenv_coll_fun_correctness : optim_correct.

Hint Rewrite @head_optim_correctness : optim_correct.
Hint Rewrite @optim_correctness : optim_correct.

(* end hide *)

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
