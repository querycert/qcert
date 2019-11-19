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

Require Import List.
Require Import String.
Require Import ListSet.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRARuntime.
Require Import NRAOptim.
Require Import cNRAEnvRuntime.

Section ROptimEnv.

  (* Some of algebraic equivalences for NRA with environment *)
  (* Those are valid without type *)

  Local Open Scope nra_scope.
  Local Open Scope nraenv_core_scope.

  Context {fruntime:foreign_runtime}.

  (* Pulls equivalences from core algebra *)

  Hint Resolve dnrec_sort_content.
  Lemma pull_nra_opt (p1 p2:nraenv_core) :
    (nra_of_nraenv_core p1) ≡ₐ (nra_of_nraenv_core p2) ->
    p1 ≡ₑ p2.
  Proof.
    unfold nra_eq, nraenv_core_eq; intros.
    repeat rewrite unfold_env_nra_sort.
    rewrite H; eauto.
  Qed.

  (* P1 ∧ P2 ≡ P2 ∧ P1 *)

  Lemma envand_comm (p1 p2: nraenv_core) :
    p2 ∧ p1 ≡ₑ p1 ∧ p2.
  Proof.
    apply pull_nra_opt.
    unfold nra_of_nraenv_core.
    rewrite and_comm; reflexivity.
  Qed.

  (* (P1 ⋃ P2) ⋃ P3 ≡ P1 ⋃ (P2 ⋃ P3) *)

  Lemma envunion_assoc (p1 p2 p3: nraenv_core):
    (p1 ⋃ p2) ⋃ p3 ≡ₑ p1 ⋃ (p2 ⋃ p3).
  Proof.
    apply pull_nra_opt.
    unfold nra_of_nraenv_core.
    rewrite union_assoc; reflexivity.
  Qed.
  
  (* σ⟨ P ⟩(P1 ⋃ P2) ≡ σ⟨ P ⟩(P1) ⋃ σ⟨ P ⟩(P2) *)
  Lemma select_union_distr (q q₁ q₂: nraenv_core) :
    σ⟨ q ⟩(q₁ ⋃ q₂) ≡ₑ σ⟨ q ⟩(q₁) ⋃ σ⟨ q ⟩(q₂).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _.
    simpl.
    generalize (h ⊢ₑ q₁ @ₑ x  ⊣ c;env) as d1.
    generalize (h ⊢ₑ q₂ @ₑ x  ⊣ c;env) as d2.
    intros.
    destruct d1; destruct d2; try (autorewrite with alg; reflexivity); simpl.
    destruct d; try reflexivity.
    destruct d0; simpl;
    try (destruct (lift_filter
                     (fun x' : data =>
                        match h ⊢ₑ q @ₑ x' ⊣ c;env with
                          | Some (dbool b) => Some b
                          | _ => None
                        end) l); simpl; reflexivity).
    induction l; simpl.
      destruct (lift_filter
         (fun x' : data =>
          match h ⊢ₑ q @ₑ x' ⊣ c;env with
          | Some (dbool b) => Some b
          | _ => None
          end) l0); reflexivity.
      generalize(h ⊢ₑ q @ₑ a ⊣ c;env); intros.
      unfold bunion.
      rewrite lift_app_filter.
      destruct o; try reflexivity.
      destruct d; try reflexivity.
      revert IHl.
      generalize ((lift_filter
            (fun x' : data =>
             match h ⊢ₑ q @ₑ x' ⊣ c;env with
             | Some (dbool b0) => Some b0
             | _ => None
             end) l)).
      generalize (lift_filter
             (fun x' : data =>
              match h ⊢ₑ q @ₑ x' ⊣ c;env with
              | Some (dbool b0) => Some b0
              | _ => None
              end) l0).
      intros.
      destruct o0; try reflexivity. simpl.
      destruct o; try reflexivity.
      + destruct b; autorewrite with alg; reflexivity.
      + autorewrite with alg. reflexivity. 
  Qed.

  (* χ⟨ P1 ⟩( { P2 } ) ≡ { P1 ◯ P2 } *)

  Lemma envmap_singleton (p1 p2:nraenv_core) :
    χ⟨ p1 ⟩( ‵{| p2 |} ) ≡ₑ ‵{| p1 ◯ p2 |}.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    generalize (h ⊢ₑ p1 @ₑ d ⊣ c;env); intros; simpl.
    destruct o; reflexivity.
  Qed.

  (* χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ≡ χ⟨ P1 ◯ P2 ⟩( P3 ) *)

  Lemma envmap_map_compose (p1 p2 p3:nraenv_core) :
    χ⟨ p1 ⟩( χ⟨ p2 ⟩( p3 ) ) ≡ₑ χ⟨ p1 ◯ p2 ⟩( p3 ).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p3 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    unfold olift, lift; simpl.
    induction l; try reflexivity; simpl.
    generalize (h ⊢ₑ p2 @ₑ a ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    revert IHl; generalize (lift_map (nraenv_core_eval h c p2 env) l); intros.
    destruct o; try reflexivity; simpl.
    destruct (h ⊢ₑ p1 @ₑ d ⊣ c;env); try reflexivity; simpl.
    revert IHl; generalize (lift_map
              (fun x0 : data =>
               match h ⊢ₑ p2 @ₑ x0 ⊣ c;env with
               | Some x'0 => h ⊢ₑ p1 @ₑ x'0 ⊣ c;env
               | None => None
               end) l); intros.
    destruct o; try reflexivity; simpl in *.
    destruct (lift_map (nraenv_core_eval h c p1 env) l0).
    inversion IHl; reflexivity.
    congruence.
    destruct (lift_map (nraenv_core_eval h c p1 env) l0).
    congruence.
    reflexivity.
    revert IHl; generalize (lift_map
              (fun x0 : data =>
               match h ⊢ₑ p2 @ₑ x0 ⊣ c;env with
               | Some x'0 => h ⊢ₑ p1 @ₑ x'0 ⊣ c;env
               | None => None
               end) l); intros.
    destruct o; try congruence.
    destruct (h ⊢ₑ p1 @ₑ d ⊣ c;env); reflexivity.
  Qed.

  (* [ a : P1 ] ◯ P2 ≡ [ a : P1 ◯ P2 ] *)

  Lemma app_over_rec s p1 p2:
    ‵[| (s, p1) |] ◯ p2 ≡ₑ ‵[| (s, p1 ◯ p2) |].
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* ♯flatten({ ♯flatten( p ) }) ≡ ♯flatten( p ) *)
  
  Lemma envflatten_coll_flatten p:
    ♯flatten(‵{| ♯flatten( p ) |}) ≡ₑ ♯flatten( p ).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; try reflexivity; simpl.
    unfold olift; simpl.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    unfold lift, oflatten in *; simpl in *.
    destruct a; try reflexivity.
    revert IHl; generalize (lift_flat_map
                (fun x : data =>
                 match x with
                 | dcoll y => Some y
                 | _ => None
                 end) l); intros.
    destruct o; try reflexivity; simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.
  
  (* ♯flatten({ { p } }) ≡ ♯flatten( p ) *)
  
  Lemma envflatten_coll_coll p:
    ♯flatten(‵{| ‵{| p |} |}) ≡ₑ ‵{| p |}.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; reflexivity.
  Qed.

  Lemma envflatten_nil :
    ♯flatten(‵{||}) ≡ₑ ‵{||}.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    trivial.
  Qed.

  (* ♯flatten({ χ⟨ p1 ⟩( p2 ) }) ≡ χ⟨ p1 ⟩( p2 ) *)
  
  Lemma envflatten_coll_map p1 p2 :
    ♯flatten(‵{| χ⟨ p1 ⟩( p2 ) |}) ≡ₑ χ⟨ p1 ⟩( p2 ).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    unfold olift in *; simpl in *.
    generalize (h ⊢ₑ p1 @ₑ a ⊣ c;env); clear a; intros.
    destruct o; try reflexivity; simpl.
    unfold lift in *; simpl in *.
    revert IHl; generalize (lift_map (nraenv_core_eval h c p1 env) l); intros.
    destruct o; try reflexivity; try congruence.
    unfold lift_oncoll in *; simpl in *.
    rewrite app_nil_r.
    rewrite app_nil_r in IHl.
    inversion IHl; reflexivity.
  Qed.

  Lemma flatten_flatten_map_either_nil p₁ p₂ p₃ :
    ♯flatten( ♯flatten(χ⟨cNRAEnvEither p₁ ‵{||} ◯ p₂⟩(p₃))) ≡ₑ 
     ♯flatten( χ⟨cNRAEnvEither( ♯flatten(p₁)) ‵{||} ◯ p₂⟩(p₃)).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p₃ @ₑ x ⊣ c; env); simpl; trivial.
    unfold olift.
    destruct d; simpl; trivial.
    induction l; simpl; trivial.
    unfold lift in *.
    destruct ( lift_map
                (fun x0 : data =>
                 match h ⊢ₑ p₂ @ₑ x0 ⊣ c; env with
                 | Some (dleft dl) => h ⊢ₑ p₁ @ₑ dl ⊣ c; env
                 | Some (dright _) => Some (dcoll nil)
                 | Some _ => None
                 | None => None
                 end) l); simpl in *;
    destruct (lift_map
              (fun x0 : data =>
               match h ⊢ₑ p₂ @ₑ x0 ⊣ c; env with
               | Some (dleft dl) =>
                   match h ⊢ₑ p₁ @ₑ dl ⊣ c; env with
                   | Some x'0 =>
                       lift_oncoll
                         (fun l1 : list data =>
                          match oflatten l1 with
                          | Some a' => Some (dcoll a')
                          | None => None
                          end) x'0
                   | None => None
                   end
               | Some (dright _) => Some (dcoll nil)
               | Some _ => None
               | None => None
               end) l); simpl in * .
    - destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
      case_eq (oflatten l0);
        [intros ? eqq0 | intros eqq0]; rewrite eqq0 in *;
        (case_eq (oflatten l1);
         [intros ? eqq1 | intros eqq1]; rewrite eqq1 in *;
           simpl in IHl); try discriminate.
      + case_eq (oflatten l2);
        [intros ? eqq2 | intros eqq2]; try rewrite eqq2 in *;
        try discriminate.
        inversion IHl; clear IHl; subst.
        destruct d; simpl; trivial.
        * destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
          destruct d0; simpl; trivial.
          rewrite (oflatten_cons _ _ _ eqq0).
          simpl.
          { case_eq (oflatten l4);
            [intros ? eqq4 | intros eqq4]; simpl.
            - rewrite (oflatten_cons _ _ _ eqq1).
              rewrite (oflatten_app _ _ _ _ eqq4 eqq2).
              trivial.
            -  rewrite (oflatten_app_none1 _ _ eqq4).
               trivial.
          } 
        * rewrite (oflatten_cons _ _ _ eqq0).
          rewrite (oflatten_cons _ _ _ eqq1).
          simpl.
          rewrite eqq2.
          trivial.
      +  case_eq (oflatten l2);
        [intros ? eqq2 | intros eqq2]; try rewrite eqq2 in *;
        try discriminate.
         destruct d; simpl; trivial.
        * destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
          destruct d0; simpl; trivial.
          rewrite (oflatten_cons _ _ _ eqq0).
          simpl.
          rewrite (oflatten_app_none2 _ _ eqq2).
          destruct (oflatten l3); simpl; trivial.
          rewrite (oflatten_cons_none _ _ eqq1).
          trivial.
        * rewrite (oflatten_cons _ _ _ eqq0).
          simpl.
          rewrite (oflatten_cons_none _ _ eqq1).
          rewrite eqq2.
          trivial.
      + destruct d; simpl; trivial.
        * destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
          rewrite (oflatten_cons_none _ _ eqq0).
          destruct d0; simpl; trivial.
          destruct (oflatten l2); simpl; trivial.
          rewrite (oflatten_cons_none _ _ eqq1).
          trivial.
        * rewrite (oflatten_cons_none _ _ eqq0).
          rewrite (oflatten_cons_none _ _ eqq1).
          trivial.
    - destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
      destruct d; simpl; trivial.
      + destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
        destruct d0; simpl; trivial.
        case_eq (oflatten l0);
          [intros ? eqq0 | intros eqq0]; rewrite eqq0 in *; simpl in *.
        * case_eq (oflatten l2);
          [intros ? eqq2 | intros eqq2]; rewrite eqq2 in *; try discriminate.
          rewrite (oflatten_cons _ _ _ eqq0); simpl.
          rewrite (oflatten_app_none2 _ _ eqq2).
          destruct (oflatten l1); trivial.
        * rewrite (oflatten_cons_none _ _ eqq0).
          destruct (oflatten l1); trivial.
      + case_eq (oflatten l0);
            [intros ? eqq0 | intros eqq0]; rewrite eqq0 in *; simpl in *.
        * case_eq (oflatten l1);
          [intros ? eqq1 | intros eqq1]; rewrite eqq1 in *; try discriminate.
          rewrite (oflatten_cons _ _ _ eqq0); simpl.
          rewrite eqq1.
          trivial.
        * rewrite (oflatten_cons_none _ _ eqq0).
          trivial.
    - case_eq (oflatten l0);
      [intros ? eqq0 | intros eqq0];
       rewrite eqq0 in *; simpl in *; try discriminate.
      destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
      destruct d; simpl; trivial.
      + destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
        destruct d0; simpl; trivial.
        destruct (oflatten l1); simpl; trivial.
        rewrite (oflatten_cons_none _ _ eqq0).
        trivial.
      + rewrite (oflatten_cons_none _ _ eqq0).
        trivial.
    - destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
      destruct d; simpl; trivial.
      destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
      destruct d0; simpl; trivial.
      destruct (oflatten l0); simpl; trivial.
  Qed.
      
  (* ♯flatten( ‵{| p1 ⊗ p2 |} ) ≡ p1 ⊗ p2 *)

  Lemma envflatten_coll_mergeconcat p1 p2:
    ♯flatten( ‵{| p1 ⊗ p2 |} ) ≡ₑ p1 ⊗ p2.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); clear p1; intros.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; destruct o0; try reflexivity; simpl.
    destruct d; destruct d0; try reflexivity; simpl.
    destruct (merge_bindings l l0); reflexivity.
  Qed.

  (* ♯flatten(χ⟨ χ⟨ { ID } ⟩( ♯flatten( p1 ) ) ⟩( p2 ))
            ≡ χ⟨ { ID } ⟩(♯flatten(χ⟨ ♯flatten( p1 ) ⟩( p2 ))) *)

  Lemma lift_map_to_map l :
    lift_map (fun x : data => Some (dcoll (x :: nil))) l =
    Some (map (fun x : data => (dcoll (x :: nil))) l).
  Proof.
    induction l; [reflexivity|simpl; rewrite IHl; reflexivity].
  Qed.

  Lemma double_flatten_map_coll p1 p2 :
    ♯flatten(χ⟨ χ⟨ ‵{| ID |} ⟩( ♯flatten( p1 ) ) ⟩( p2 ))
            ≡ₑ χ⟨ ‵{| ID |} ⟩(♯flatten(χ⟨ ♯flatten( p1 ) ⟩( p2 ))).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    unfold olift in *; simpl in *.
    induction l; try reflexivity; simpl.
    generalize (h ⊢ₑ p1 @ₑ a ⊣ c;env); clear a; intros.
    destruct o; try reflexivity; simpl.
    destruct (lift_oncoll (fun l0 : list data => lift dcoll (oflatten l0)) d); try reflexivity; simpl.
    unfold lift in *; simpl in *.
    destruct (         lift_map
           (fun x : data =>
            match h ⊢ₑ p1 @ₑ x ⊣ c;env with
            | Some x' =>
                lift_oncoll
                  (fun l0 : list data =>
                   match oflatten l0 with
                   | Some a' => Some (dcoll a')
                   | None => None
                   end) x'
            | None => None
            end) l); try reflexivity; try congruence; simpl in *.
    - unfold oflatten, lift_oncoll in *; simpl in *.
      destruct d0; try reflexivity; try congruence; simpl in *.
      generalize (lift_map_to_map l1); intros.
      rewrite H; clear H; simpl.
      destruct (            lift_map
              (fun x : data =>
               match
                 match h ⊢ₑ p1 @ₑ x ⊣ c;env with
                 | Some (dcoll l1) =>
                     match
                       lift_flat_map
                         (fun x0 : data =>
                          match x0 with
                          | dcoll y => Some y
                          | _ => None
                          end) l1
                     with
                     | Some a' => Some (dcoll a')
                     | None => None
                     end
                 | _ => None
                 end
               with
               | Some (dcoll l1) =>
                   match
                     lift_map (fun x0 : data => Some (dcoll (x0 :: nil))) l1
                   with
                   | Some a' => Some (dcoll a')
                   | None => None
                   end
               | _ => None
               end) l
               ); try reflexivity; try congruence; simpl in *.
      destruct ((lift_flat_map
          (fun x : data =>
           match x with
           | dcoll y => Some y
           | _ => None
           end) l2)); try reflexivity; try congruence; simpl in *.
      destruct (       (lift_flat_map
          (fun x : data =>
           match x with
           | dcoll y => Some y
           | _ => None
           end) l0)); try reflexivity; try congruence; simpl in *.
      generalize (lift_map_to_map l4); intros.
      rewrite H in *; clear H.
      generalize (lift_map_to_map (l1++l4)); intros.
      rewrite H in *; clear H.
      inversion IHl; clear IHl H0.
      * rewrite map_app; simpl; reflexivity.
      * destruct ((lift_flat_map
                   (fun x : data =>
                      match x with
                        | dcoll y => Some y
                        | _ => None
                      end) l0)); try reflexivity; try congruence; simpl in *.
        generalize (lift_map_to_map l3); intros.
        rewrite H in *; clear H; congruence.
      * destruct ((lift_flat_map
                     (fun x : data =>
                        match x with
                          | dcoll y => Some y
                          | _ => None
                        end) l0)); try reflexivity; try congruence; simpl in *.
        generalize (lift_map_to_map l2); intros.
        rewrite H in *; clear H; congruence.
    - destruct d0; try reflexivity; try congruence; simpl in *.
      destruct (lift_map (fun x : data => Some (dcoll (x :: nil))) l0); try reflexivity; try congruence; simpl.
      destruct (            lift_map
              (fun x : data =>
               match
                 match h ⊢ₑ p1 @ₑ x ⊣ c;env with
                 | Some x' =>
                     lift_oncoll
                       (fun l0 : list data =>
                        match oflatten l0 with
                        | Some a' => Some (dcoll a')
                        | None => None
                        end) x'
                 | None => None
                 end
               with
               | Some x' =>
                   lift_oncoll
                     (fun c1 : list data =>
                      match
                        lift_map (fun x0 : data => Some (dcoll (x0 :: nil))) c1
                      with
                      | Some a' => Some (dcoll a')
                      | None => None
                      end) x'
               | None => None
               end) l); try reflexivity; try congruence; simpl in *.
      unfold oflatten in *; simpl.
      destruct (lift_flat_map
            (fun x : data =>
             match x with
             | dcoll y => Some y
             | _ => None
             end) l2); try reflexivity; try congruence; simpl in *.
  Qed.

  (* ♯flatten(χ⟨ { p1 } ⟩( p2 )) ≡ χ⟨ p1 ⟩( p2 ) *)
  
  Lemma envflatten_map_coll p1 p2 :
    ♯flatten(χ⟨ ‵{| p1 |} ⟩( p2 )) ≡ₑ χ⟨ p1 ⟩( p2 ).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; try reflexivity.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    generalize (h ⊢ₑ p1 @ₑ a ⊣ c;env); clear a; intros; simpl.
    destruct o; try reflexivity; simpl.
    unfold olift in *.
    revert IHl.
    generalize (lift_map
             (fun x : data =>
              match h ⊢ₑ p1 @ₑ x ⊣ c;env with
              | Some x' => Some (dcoll (x' :: nil))
              | None => None
              end) l); generalize (lift_map (nraenv_core_eval h c p1 env) l); intros.
    unfold lift in *; simpl.
    destruct o; destruct o0; simpl; try reflexivity; try congruence.
    - simpl in *.
      unfold oflatten in *; simpl in *.
      revert IHl.
      generalize ((lift_flat_map
                     (fun x : data =>
                        match x with
                          | dcoll y => Some y
                          | _ => None
                        end) l1)); intros; simpl in *.
      destruct o; try congruence.
      inversion IHl; clear IHl H0; reflexivity.
    - simpl in *.
      unfold oflatten in *; simpl.
      revert IHl.
      generalize ((lift_flat_map
                     (fun x : data =>
                        match x with
                          | dcoll y => Some y
                          | _ => None
                        end) l0)); intros; simpl in *.
      destruct o; try congruence; reflexivity.
  Qed.

  Lemma select_over_nil p₁ :
    σ⟨p₁⟩(cNRAEnvConst (dcoll nil)) ≡ₑ cNRAEnvConst (dcoll nil).
  Proof.
    red; intros br env dn_env d dn_d.
    simpl; trivial.
  Qed.

  Lemma map_over_nil p₁ :
    χ⟨p₁⟩(cNRAEnvConst (dcoll nil)) ≡ₑ cNRAEnvConst (dcoll nil).
  Proof.
    red; intros br env dn_env d dn_d.
    simpl; trivial.
  Qed.

  Lemma map_over_flatten p₁ p₂ :
    χ⟨p₁⟩(♯flatten(p₂)) ≡ₑ (♯flatten(χ⟨χ⟨p₁⟩(ID)⟩(p₂))).
  Proof.
    red; intros br c dn_c env dn_env d dn_d.
    simpl.
    destruct (br ⊢ₑ p₂ @ₑ d ⊣ c;env); simpl; trivial.
    destruct d0; simpl; trivial.
    clear d dn_d.
    induction l; simpl; trivial.
    destruct a; simpl; trivial.
    case_eq (oflatten l); [intros ? eqq1 | intros eqq1];
    rewrite eqq1 in IHl; simpl in *;
    [rewrite (oflatten_cons _ _ _ eqq1) | rewrite (oflatten_cons_none _ _ eqq1)]
    ; (case_eq (lift_map
                 (fun x : data =>
                  lift_oncoll
                    (fun c1 : list data =>
                     lift dcoll (lift_map (nraenv_core_eval br c p₁ env) c1)) x) l);  [intros ? eqq2 | intros eqq2];
     rewrite eqq2 in IHl; simpl in * ).
    - apply lift_injective in IHl; [ | inversion 1; trivial].
      rewrite lift_map_over_app.
      rewrite IHl.
      destruct (lift_map (nraenv_core_eval br c p₁ env) l0); simpl; trivial.
    - apply none_lift in IHl.
      rewrite lift_map_over_app.
      rewrite IHl; simpl.
      destruct (lift_map (nraenv_core_eval br c p₁ env) l0); simpl; trivial.
    - clear IHl.
      cut False; [intuition | ].
      revert eqq1 l1 eqq2.
      induction l; simpl in *; try discriminate.
      destruct a; simpl in *; try discriminate.
      intros.
      unfold oflatten in *.
      simpl in *.
      apply none_lift in eqq1.
      specialize (IHl eqq1); clear eqq1.
      match_destr_in eqq2.
      apply some_lift in eqq2.
      destruct eqq2 as [? eqq2 ?]; subst.
      apply (IHl _ eqq2).
    - match_destr.
  Qed.
  
  Lemma select_over_flatten p₁ p₂ :
    σ⟨p₁⟩(♯flatten(p₂)) ≡ₑ (♯flatten(χ⟨σ⟨p₁⟩(ID)⟩(p₂))).
  Proof.
    red; intros br c dn_c env dn_env d dn_d.
    simpl.
    destruct (br ⊢ₑ p₂ @ₑ d ⊣ c;env); simpl; trivial.
    destruct d0; simpl; trivial.
    clear d dn_d.
    induction l; simpl; trivial.
    simpl.
    destruct a; simpl; trivial.
    case_eq (oflatten l); [intros ? eqq1 | intros eqq1];
    rewrite eqq1 in IHl; simpl in *;
    [rewrite (oflatten_cons _ _ _ eqq1) | rewrite (oflatten_cons_none _ _ eqq1)];
    (case_eq (lift_map
                (fun x : data =>
                 lift_oncoll
                   (fun c1 : list data =>
                    lift dcoll
                      (lift_filter
                         (fun x' : data =>
                          match br ⊢ₑ p₁ @ₑ x' ⊣ c;env with
                          | Some (dbool b) => Some b
                          | Some _ => None
                          | None => None
                          end) c1)) x) l);  [intros ? eqq2 | intros eqq2];
     rewrite eqq2 in IHl; simpl in * ).
    - apply lift_injective in IHl; [ | inversion 1; trivial].
      rewrite lift_app_filter.
      rewrite IHl.
      destruct ( (lift_filter
           (fun x' : data =>
            match br ⊢ₑ p₁ @ₑ x' ⊣ c;env with
            | Some (dbool b) => Some b
            | Some _ => None
            | None => None
            end) l0)); simpl; trivial.
    - apply none_lift in IHl.
      rewrite lift_app_filter.
      rewrite IHl; simpl.
      destruct (lift_filter
           (fun x' : data =>
            match br ⊢ₑ p₁ @ₑ x' ⊣ c;env with
            | Some (dbool b) => Some b
            | Some _ => None
            | None => None
            end) l0); simpl; trivial.
    - clear IHl.
      cut False; [intuition | ].
      revert eqq1 l1 eqq2.
      induction l; simpl in *; try discriminate.
      destruct a; simpl in *; try discriminate.
      intros.
      unfold oflatten in *.
      simpl in *.
      apply none_lift in eqq1.
      specialize (IHl eqq1); clear eqq1.
      match_destr_in eqq2.
      apply some_lift in eqq2.
      destruct eqq2 as [? eqq2 ?]; subst.
      apply (IHl _ eqq2).
    - match_destr.
  Qed.

  Lemma select_over_either p₁ p₂ p₃ :
    σ⟨p₁⟩( cNRAEnvEither p₂ p₃) ≡ₑ cNRAEnvEither (σ⟨p₁⟩(p₂)) (σ⟨p₁⟩(p₃)).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    match_destr.
  Qed.

  (* [ a1 : p1; a2 : p1 ].a2 ≡ p1 *)
  (** Now has a (better) typed variant for arbitrary p1/p2, see TOptimEnv *)

  Lemma envdot_from_duplicate_r s1 s2 p1 :
    (‵[| (s1, p1) |] ⊕ ‵[| (s2, p1) |])·s2 ≡ₑ p1.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); clear p1 x; intros.
    destruct o; try reflexivity.
    unfold olift; simpl.
    destruct (StringOrder.lt_dec s1 s2); try reflexivity; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s2 s2); try congruence; simpl.
    destruct (StringOrder.lt_dec s1 s2); try congruence; simpl.
    destruct (StringOrder.lt_dec s2 s1); try congruence; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s2 s1); try congruence; simpl.
    destruct (string_eqdec s2 s2); try congruence; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s2 s2); congruence.
  Qed.

  (* [ a1 : p1; a2 : p1 ].a1 ≡ p1 *)

  Lemma envdot_from_duplicate_l s1 s2 p1 :
    (‵[| (s1, p1) |] ⊕ ‵[| (s2, p1) |])·s1 ≡ₑ p1.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); clear p1 x; intros.
    destruct o; try reflexivity.
    unfold olift; simpl.
    destruct (StringOrder.lt_dec s1 s2); try reflexivity; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s1 s1); try congruence; simpl.
    destruct (string_eqdec s1 s2); try congruence; simpl.
    destruct (StringOrder.lt_dec s2 s1); try congruence; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s1 s1); try congruence; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s1 s2); try congruence; simpl.
    assert (StringOrder.eq s1 s2) by (apply lt_contr1; assumption).
    contradiction.
  Qed.

  Lemma envmap_over_either p₁ p₂ p₃ :
    χ⟨p₁⟩( cNRAEnvEither p₂ p₃) ≡ₑ cNRAEnvEither (χ⟨p₁⟩(p₂)) (χ⟨p₁⟩(p₃)).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    match_destr.
  Qed.

  Lemma envmap_over_either_app p₁ p₂ p₃ p₄:
    χ⟨p₁⟩( cNRAEnvEither p₂ p₃ ◯ p₄) ≡ₑ cNRAEnvEither (χ⟨p₁⟩(p₂)) (χ⟨p₁⟩(p₃)) ◯ p₄.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    unfold olift.
    destruct (h ⊢ₑ p₄ @ₑ x ⊣ c; env); simpl; trivial.
    destruct d; simpl; trivial.
  Qed.

  (* χ⟨ ID ⟩( { P } ) ≡ { P } *)
  
  Lemma envmap_into_id p :
    χ⟨ ID ⟩(‵{| p |}) ≡ₑ ‵{| p |}.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; reflexivity.
  Qed.

  

  (* χ⟨ ID ⟩( ♯flatten(P) ) ≡ ♯flatten(P) *)
  
  Lemma envmap_into_id_flatten p :
    χ⟨ ID ⟩( ♯flatten(p) ) ≡ₑ ♯flatten(p).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; try reflexivity; simpl.
    unfold lift_oncoll; simpl.
    destruct d; try reflexivity; simpl.
    unfold olift, lift; simpl.
    destruct (oflatten l); try reflexivity; clear l; simpl.
    induction l0; try reflexivity; simpl.
    unfold lift; simpl.
    revert IHl0; destruct (lift_map (fun x: data => Some x) l0); congruence.
  Qed.

  (* { [ s1 : p1 ] } × { [ s2 : p2 ] } ≡ { [ s1 : p1; s2 : p2 ] } *)

  Lemma product_singletons s1 s2 p1 p2:
    ‵{|‵[| (s1, p1) |] |} × ‵{| ‵[| (s2, p2) |] |} ≡ₑ
     ‵{|‵[| (s1, p1) |] ⊕ ‵[| (s2, p2) |] |}.
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; destruct o0; reflexivity.
  Qed.

  (* p ◯ ID ≡ p *)
  
  Lemma app_over_id p:
    p ◯ ID ≡ₑ p.
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; reflexivity.
  Qed.    

  (* ENV ◯ₑ p ≡ p *)
  
  Lemma appenv_over_env p:
    ENV ◯ₑ p ≡ₑ p.
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); reflexivity.
  Qed.

  (* ID ◯ p ≡ p *)
  
  Lemma app_over_id_l p:
    ID ◯ p ≡ₑ p.
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (p1 ◯ p2) ◯ p3 ≡ p1 ◯ (p2 ◯ p3) *)
  
  Lemma app_over_app p1 p2 p3:
    (p1 ◯ p2) ◯ p3  ≡ₑ p1 ◯ (p2 ◯ p3).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p3 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (cNRAEnvUnop u p1) ◯ p2 ≡ (cNRAEnvUnop u (p1 ◯ p2)) *)

  Lemma app_over_unop u p1 p2:
    (cNRAEnvUnop u p1) ◯ p2 ≡ₑ (cNRAEnvUnop u (p1 ◯ p2)).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (cNRAEnvUnop u p1) ◯ p2 ≡ (cNRAEnvUnop u (p1 ◯ p2)) *)

  Lemma appenv_over_unop u p1 p2:
    (cNRAEnvUnop u p1) ◯ₑ p2 ≡ₑ (cNRAEnvUnop u (p1 ◯ₑ p2)).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  Lemma unop_over_either u p₁ p₂ :
    cNRAEnvUnop u (cNRAEnvEither p₁ p₂) ≡ₑ cNRAEnvEither (cNRAEnvUnop u p₁)(cNRAEnvUnop u p₂).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    match_destr.
  Qed.

  Lemma unop_over_either_app u p₁ p₂ p₃ :
    cNRAEnvUnop u (cNRAEnvEither p₁ p₂ ◯ p₃)  ≡ₑ cNRAEnvEither (cNRAEnvUnop u p₁)(cNRAEnvUnop u p₂) ◯ p₃.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    unfold olift.
    destruct (h ⊢ₑ p₃ @ₑ x ⊣ c; env); simpl; trivial.
    destruct d; simpl; trivial.
  Qed.

  (* (ENV ⊗ p1) ◯ p2 ≡ ENV ⊗ (p1 ◯ p2) *)

  Lemma app_over_merge p1 p2:
    (cNRAEnvEnv ⊗ p1) ◯ p2 ≡ₑ cNRAEnvEnv ⊗ (p1 ◯ p2).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (cNRAEnvBinop b p2 (cNRAEnvConst d) ◯ p1) ≡ (cNRAEnvBinop b (p2 ◯ p1) (cNRAEnvConst d)) *)
  
  Lemma app_over_binop_l b d p1 p2:
    (cNRAEnvBinop b p2 (cNRAEnvConst d) ◯ p1)
      ≡ₑ (cNRAEnvBinop b (p2 ◯ p1) (cNRAEnvConst d)).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.
 
  (* (cNRAEnvBinop b p1 p2 ◯ (p3 ⊕ p4)) ≡ (cNRAEnvBinop b (p1 ◯ (p3 ⊕ p4)) (p2 ◯ (p3 ⊕ p4))) *)
  
  Lemma app_concat_over_binop b p1 p2 p3 p4:
    (cNRAEnvBinop b p1 p2 ◯ (p3 ⊕ p4) )
      ≡ₑ (cNRAEnvBinop b (p1 ◯ (p3 ⊕ p4)) (p2 ◯ (p3 ⊕ p4))).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    destruct (h ⊢ₑ p3 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct (h ⊢ₑ p4 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct d0; reflexivity.
  Qed.

  (* (cNRAEnvBinop b p2 (cNRAEnvConst d) ◯ p1) ≡ (cNRAEnvBinop b (p2 ◯ p1) (cNRAEnvConst d)) *)
  
  Lemma app_over_binop_env b p1 p2 s:
    (cNRAEnvBinop b p1 p2 ◯ (cNRAEnvUnop (OpDot s) cNRAEnvEnv))
      ≡ₑ (cNRAEnvBinop b (p1 ◯ (cNRAEnvUnop (OpDot s) cNRAEnvEnv)) (p2 ◯ (cNRAEnvUnop (OpDot s) cNRAEnvEnv))).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    destruct env; try reflexivity; simpl.
    destruct (edot l s); reflexivity.
  Qed.

  (* σ⟨ p1 ⟩( p2 ) ◯ p0 ≡ σ⟨ p1 ⟩( p2 ◯ p0 ) *)
  
  Lemma app_over_select p0 p1 p2:
    σ⟨ p1 ⟩( p2 ) ◯ p0 ≡ₑ σ⟨ p1 ⟩( p2 ◯ p0 ).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    

  (* χ⟨ p1 ⟩( p2 ) ◯ p0 ≡ χ⟨ p1 ⟩( p2 ◯ p0 ) *)
  
  Lemma app_over_map p0 p1 p2:
    χ⟨ p1 ⟩( p2 ) ◯ p0 ≡ₑ χ⟨ p1 ⟩( p2 ◯ p0 ).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    
  
  (* ⋈ᵈ⟨ p1 ⟩( p2 ) ◯ p0 ≡ ⋈ᵈ⟨ p1 ⟩( p2 ◯ p0 ) *)
  
  Lemma app_over_mapconcat p0 p1 p2:
    ⋈ᵈ⟨ p1 ⟩( p2 ) ◯ p0 ≡ₑ ⋈ᵈ⟨ p1 ⟩( p2 ◯ p0 ).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    
  
  (* (p1 × p2) ◯ p0 ≡ (p1  ◯ p0) × (p2 ◯ p0) *)
  
  Lemma app_over_product p0 p1 p2:
    (p1 × p2) ◯ p0 ≡ₑ (p1  ◯ p0) × (p2 ◯ p0).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    
  
  (* χ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ χ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)
  
  Lemma appenv_over_map p0 p1 p2:
    nraenv_core_ignores_id p0 ->
    χ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ₑ χ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros ? ? ? _ ? _ ? _; simpl.
    case_eq (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros; try reflexivity; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;d); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    rewrite (nraenv_core_ignores_id_swap p0 H h c env a x).
    rewrite H0; simpl.
    destruct (h ⊢ₑ p1 @ₑ a ⊣ c;d); try reflexivity; simpl.
    f_equal; unfold lift in *; simpl in *.
    destruct (lift_map (nraenv_core_eval h c p1 d) l);
      destruct (lift_map
            (fun x0 : data =>
             olift (fun env' : data => h ⊢ₑ p1 @ₑ x0 ⊣ c;env') (h ⊢ₑ p0 @ₑ x0 ⊣ c;env)) l); congruence.
  Qed.    

  (* σ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ σ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)
  
  Lemma appenv_over_select p0 p1 p2:
    nraenv_core_ignores_id p0 ->
    σ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ₑ σ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros ? ? ? _ ? _ ? _; simpl.
    case_eq (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros; try reflexivity; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;d); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    rewrite (nraenv_core_ignores_id_swap p0 H h c env a x).
    rewrite H0; simpl.
    destruct (h ⊢ₑ p1 @ₑ a ⊣ c;d); try reflexivity; simpl.
    destruct d0; try reflexivity.
    destruct b; try reflexivity.
    f_equal; unfold lift in *; simpl in *.
    destruct (lift_filter
       (fun x' : data =>
        match h ⊢ₑ p1 @ₑ x' ⊣ c;d with
        | Some (dbool b) => Some b
        | _ => None
        end) l); destruct (lift_filter
       (fun x' : data =>
        match
          olift (fun env' : data => h ⊢ₑ p1 @ₑ x' ⊣ c;env') (h ⊢ₑ p0 @ₑ x' ⊣ c;env)
        with
        | Some (dbool b) => Some b
        | _ => None
        end) l); simpl in *; try congruence.
    f_equal; unfold lift in *; simpl in *.
    destruct (lift_filter
       (fun x' : data =>
        match h ⊢ₑ p1 @ₑ x' ⊣ c;d with
        | Some (dbool b) => Some b
        | _ => None
        end) l); destruct (lift_filter
       (fun x' : data =>
        match
          olift (fun env' : data => h ⊢ₑ p1 @ₑ x' ⊣ c;env') (h ⊢ₑ p0 @ₑ x' ⊣ c;env)
        with
        | Some (dbool b) => Some b
        | _ => None
        end) l); simpl in *; try congruence.
  Qed.    

  (* χᵉ⟨ { ENV } ⟩ ◯ₑ ♯flatten(p) ≡ χ⟨ { ID } ⟩(♯flatten(p)) *)
  
  Lemma appenv_over_mapenv p:
    cNRAEnvAppEnv (cNRAEnvMapEnv (cNRAEnvUnop OpBag cNRAEnvEnv)) (cNRAEnvUnop OpFlatten p) ≡ₑ (cNRAEnvMap (cNRAEnvUnop OpBag cNRAEnvID) (cNRAEnvUnop OpFlatten p)).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

   (* (χᵉ⟨ { { ENV } } ⟩ ◯ₑ ♯flatten(p)) ≡ χ⟨ { { ID } } ⟩(♯flatten(p)) *)

  Lemma appenv_over_mapenv_coll p:
    cNRAEnvAppEnv (cNRAEnvMapEnv (cNRAEnvUnop OpBag (cNRAEnvUnop OpBag cNRAEnvEnv))) (cNRAEnvUnop OpFlatten p) ≡ₑ (cNRAEnvMap (cNRAEnvUnop OpBag (cNRAEnvUnop OpBag cNRAEnvID)) (cNRAEnvUnop OpFlatten p)).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    

  (* χᵉ⟨ { ENV.e } ⟩ ◯ₑ (ENV ⊗ ID) ≡ χ⟨ { ID.e } ⟩(ENV ⊗ ID) *)
  
  Lemma appenv_over_mapenv_merge s:
    cNRAEnvAppEnv (cNRAEnvMapEnv (cNRAEnvUnop OpBag ((ENV) · s))) (ENV ⊗ ID)
             ≡ₑ cNRAEnvMap (cNRAEnvUnop OpBag ((ID) · s)) (ENV ⊗ ID).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    destruct x; reflexivity.
  Qed.

  (* nraenv_core_ignores_env p1 -> (ENV ⊗ p1) ◯ₑ p2 ≡ p2 ⊗ p1 *)
  
  Lemma appenv_over_env_merge_l p1 p2:
    nraenv_core_ignores_env p1 ->
    cNRAEnvAppEnv (ENV ⊗ p1) p2 ≡ₑ p2 ⊗ p1.
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity; simpl.
    rewrite (nraenv_core_ignores_env_swap p1 H h c d env x).
    destruct (h ⊢ₑ p1 @ₑ x ⊣ c;env); reflexivity.
  Qed.

  (* χᵉ⟨ ENV.e ⟩ ◯ₑ (ENV ⊗ ID) ≡ χ⟨ ID.e ⟩(ENV ⊗ ID) *)
  
  Lemma appenv_over_mapenv_merge2 s:
    cNRAEnvAppEnv (cNRAEnvMapEnv ((ENV) · s)) (ENV ⊗ ID)
             ≡ₑ cNRAEnvMap ((ID) · s) (ENV ⊗ ID).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    destruct x; reflexivity.
  Qed.    

  (* ENV ◯ₑ p ≡ p *)

  Lemma env_appenv p:
    (ENV) ◯ₑ p ≡ₑ p.
  Proof.
    unfold nra_eq, nraenv_core_eq; intros; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); reflexivity.
  Qed.

  (*****************)
  (* Rules Section *)
  (*****************)
  
  (* Composite/specialized rewrites, useful for rules optimization *)
  
  Lemma envmap_singleton_rec s1 s2 :
    χ⟨‵[| (s1, ID) |] ⟩( ‵{|(ID) · s2 |}) ≡ₑ ‵{|‵[| (s1, (ID) · s2) |] |}.
  Proof.
    apply envmap_singleton.
  Qed.

  (* χ⟨ ID.a ⟩( { P } ) ≡ { P.a } *)
  
  Lemma envmap_dot_singleton a p :
    χ⟨ ID·a ⟩( ‵{| p |} ) ≡ₑ ‵{| p·a |}.
  Proof.
    apply envmap_singleton.
  Qed.

  (*
     a1, a2, a3 are distinct field names
     ============================================================================
     χ⟨ ¬π[a1](ID) ⟩ ( ⋈ᵈ⟨ χ⟨ [ a2 : ID ] ⟩(ID.a1) ⟩( { [ a3 : p1; a1: { p2 } ] } )
     ≡ { [ (a3 : p1; a2 : p2 ] } *)
  
  Lemma envunnest_singleton s1 s2 s3 p1 p2 :
    s1 <> s2 /\ s2 <> s3 /\ s3 <> s1 ->
    χ⟨ ¬π[s1](ID) ⟩(
       ⋈ᵈ⟨ χ⟨‵[| (s2,ID) |] ⟩((ID)·s1) ⟩( ‵{|‵[| (s3,p1) |] ⊕ ‵[| (s1,‵{| p2 |}) |]|} )
     )
     ≡ₑ ‵{|‵[| (s3, p1) |] ⊕ ‵[| (s2, p2) |]|}.
  Proof.
    intros.
    elim H; clear H; intros.
    elim H0; clear H0; intros.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); generalize(h ⊢ₑ p2 @ₑ x ⊣ c;env); clear p1 p2 x; intros.
    destruct o; try reflexivity; simpl.
    - unfold olift, olift2; simpl.
      destruct o0; try reflexivity; simpl.
      destruct (StringOrder.lt_dec s3 s1); try reflexivity; simpl.
      unfold lift; simpl.
      unfold omap_product, oncoll_map_concat; simpl.
      unfold edot; simpl.
      unfold string_eqdec.
      destruct (string_dec s1 s1); try reflexivity; simpl.
      unfold rremove; simpl.
      unfold rec_concat_sort; simpl.
      unfold string_eqdec.
      destruct (StringOrder.lt_dec s1 s2); try reflexivity; simpl.
      destruct (StringOrder.lt_dec s3 s1); simpl.
      destruct (string_dec s1 s3); simpl.
      congruence.
      destruct (string_dec s1 s1); simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; simpl.
      destruct (string_dec s1 s2); try congruence.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; simpl.
      destruct (string_dec s1 s2); try congruence.
      assert (StringOrder.lt s3 s2).
      apply RelationClasses.transitivity with (y := s1); assumption.
      contradiction.
      destruct (string_dec s1 s2); simpl.
      assert False; auto; contradiction.
      assert (StringOrder.lt s3 s2).
      apply RelationClasses.transitivity with (y := s1); assumption.
      contradiction.
      congruence.
      congruence.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s1); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s1); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s1); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s1); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s1 s3); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s1); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s1 s3); try reflexivity; try congruence; simpl.
      unfold lift; simpl.
      unfold omap_product, oncoll_map_concat; simpl.
      unfold edot; simpl.
      unfold string_eqdec.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      unfold rremove; simpl.
      unfold rec_concat_sort; simpl.
      unfold string_eqdec.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s1 s3); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      unfold lift; simpl.
      unfold omap_product, oncoll_map_concat; simpl.
      unfold edot; simpl.
      unfold string_eqdec.
      destruct (string_dec s1 s1); try congruence; simpl.
      unfold rremove; simpl.
      unfold rec_concat_sort; simpl.
      unfold string_eqdec.
      destruct (StringOrder.lt_dec s1 s2); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      assert (StringOrder.eq s1 s3) by (apply lt_contr1; assumption).
      congruence.
      assert (StringOrder.eq s1 s3) by (apply lt_contr1; assumption).
      congruence.
      unfold lift; simpl.
      unfold omap_product, oncoll_map_concat; simpl.
      unfold edot; simpl.
      unfold string_eqdec.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s1 s3); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      unfold rremove; simpl.
      unfold rec_concat_sort; simpl.
      unfold string_eqdec.
      destruct (StringOrder.lt_dec s3 s2); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s3); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s2 s1); try reflexivity; try congruence; simpl.
      destruct (StringOrder.lt_dec s1 s2); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (StringOrder.lt_dec s1 s3); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (StringOrder.lt_dec s1 s2); try reflexivity; try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s2); try congruence; simpl.
      destruct (string_dec s1 s3); try congruence; simpl.
      destruct (string_dec s1 s1); try congruence; simpl.
      assert (StringOrder.eq s1 s3) by (apply lt_contr1; assumption).
      congruence.
      assert (StringOrder.eq s2 s3) by (apply lt_contr1; assumption).
      congruence.
    - destruct o0; simpl; reflexivity.
  Qed.

  (* (cNRAEnvBinop u ID.a1 ID.a2) ◯ ([ a1 : p1; a2 : p2 ]) ≡ (cNRAEnvBinop u p1 p2) *)

  Lemma binop_over_rec_pair b p1 p2 a1 a2:
    a1 <> a2 ->
    (cNRAEnvBinop b ((ID) · a1) ((ID) · a2))
      ◯ (‵[| (a1, p1) |] ⊕ ‵[| (a2, p2) |])
      ≡ₑ (cNRAEnvBinop b p1 p2).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros ? ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); intros.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; destruct o0; try reflexivity; simpl.
    destruct (StringOrder.lt_dec a1 a2); simpl.
    * unfold edot; simpl.
      destruct (string_eqdec a1 a2); try congruence; simpl.
      destruct (string_eqdec a2 a2); try congruence; simpl;
      destruct (string_eqdec a1 a1); try congruence; simpl; reflexivity.
    * destruct (StringOrder.lt_dec a2 a1); try congruence; simpl.
      + unfold edot; simpl.
        destruct (string_eqdec a1 a1); try congruence; simpl.
        destruct (string_eqdec a2 a1); try congruence; simpl.
        destruct (string_eqdec a2 a2); simpl; congruence.
      + unfold edot; simpl.
        destruct (string_eqdec a1 a2); try congruence; simpl.
        assert False.
        generalize (StringOrder.compare_spec a1 a2); intros.
        elim H0; intros; contradiction.
        contradiction.
  Qed.

  (* ([ a1 : p1; a2 : d ]) ◯ p2 ≡ [ a1 : p1 ◯ p2; a2 : d ] *)
  
  Lemma concat_id_left p1 p2 s1 s2 d:
    (‵[| (s1, p1) |] ⊕ ‵[| (s2, cNRAEnvConst d) |])
      ◯ p2
     ≡ₑ (‵[| (s1, p1 ◯ p2) |] ⊕ ‵[| (s2, cNRAEnvConst d) |]).
  Proof.
    unfold nra_eq, nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* This one should be generalized based on types
      (ENV ◯ (ENV.a)).a ≡ₑ ENV.a
   *)
  
  Lemma app_over_env_dot s:
    (ENV ◯ (ENV) · s) · s ≡ₑ (ENV) · s.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct env; try reflexivity; simpl.
    case_eq (edot l s); intros; try reflexivity; assumption.
  Qed.

  Lemma app_over_appenv p1 p2 p3:
    nraenv_core_ignores_id p3 ->
    ((p3 ◯ₑ p2) ◯ p1) ≡ₑ p3 ◯ₑ (p2 ◯ p1).
  Proof.
    unfold nraenv_core_eq; intros ? ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    generalize (h ⊢ₑ p2 @ₑ d ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    apply nraenv_core_ignores_id_swap; assumption.
  Qed.

  Lemma appenv_over_app_ie p1 p2 p3:
    nraenv_core_ignores_env p3 ->
    ((p3 ◯ p2) ◯ₑ p1) ≡ₑ p3 ◯ (p2 ◯ₑ p1).
  Proof.
    unfold nraenv_core_eq; intros ? ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;d); simpl; trivial.
    apply nraenv_core_ignores_env_swap; assumption.
  Qed.

  Lemma app_over_appenv_over_mapenv p1 p2:
    (((cNRAEnvMapEnv (‵{|ENV|})) ◯ₑ p1) ◯ p2) ≡ₑ
    (((cNRAEnvMapEnv (‵{|ENV|})) ◯ₑ (p1 ◯ p2) )).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  Lemma map_full_over_select_id p0 p1 p2:
    χ⟨ p0 ⟩(σ⟨ p1 ⟩(‵{| p2 |})) ≡ₑ χ⟨ p0 ◯ p2 ⟩(σ⟨ p1 ◯ p2 ⟩(‵{| ID |})).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    case_eq (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros; try reflexivity; simpl.
    destruct (h ⊢ₑ p1 @ₑ d ⊣ c;env); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    case_eq b; intros; try reflexivity; simpl.
    rewrite H; simpl. reflexivity.
  Qed.

  Lemma compose_selects_in_mapenv p1 p2 :
    (♯flatten(cNRAEnvMapEnv (χ⟨ENV⟩(σ⟨p1⟩( ‵{| ID |}))))) ◯ₑ (χ⟨ENV⟩(σ⟨p2⟩( ‵{| ID |})))
            ≡ₑ (χ⟨ENV⟩(σ⟨p1⟩(σ⟨p2⟩( ‵{| ID |})))).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    autorewrite with alg.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity.
    destruct d; try reflexivity.
    destruct b; try reflexivity.
    autorewrite with alg; simpl.
    destruct (h ⊢ₑ p1 @ₑ x ⊣ c;env); try reflexivity.
    destruct d; try reflexivity.
    destruct b; reflexivity.
  Qed.

  (* ♯flatten(p1 ◯ₑ p2) ≡ ♯flatten(p1) ◯ₑ p2 *)
  
  Lemma flatten_through_appenv p1 p2 :
    ♯flatten(p1 ◯ₑ p2) ≡ₑ ♯flatten(p1) ◯ₑ p2.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); reflexivity.
  Qed.

  Lemma appenv_through_either q₁ q₂ q₃:
    nraenv_core_ignores_id q₃ ->
    cNRAEnvEither q₁ q₂ ◯ₑ q₃ ≡ₑ cNRAEnvEither (q₁ ◯ₑ q₃) (q₂ ◯ₑ q₃).
  Proof.
    intros.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    unfold olift.
    generalize (nraenv_core_ignores_id_swap q₃ H h c env x); intros eqq.
    destruct (h ⊢ₑ q₃ @ₑ x ⊣ c;env); simpl in * ;
    destruct x; simpl; trivial;
    specialize (eqq x); rewrite <- eqq; trivial.
  Qed.


  (* ♯flatten(χᵉ⟨{ p1 }⟩) ≡ χᵉ⟨ p1 ⟩ *)
  
  Lemma flatten_mapenv_coll p1:
    ♯flatten(cNRAEnvMapEnv (‵{| p1 |})) ≡ₑ cNRAEnvMapEnv p1.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct env; try reflexivity; simpl.
    autorewrite with alg.
    induction l; try reflexivity; simpl in *.
    destruct (h ⊢ₑ p1 @ₑ x ⊣ c;a); try reflexivity; simpl.
    apply f_equal.
    revert IHl.
    destruct ((lift_map (fun env' : data => h ⊢ₑ p1 @ₑ x ⊣ c;env') l));
      destruct ((lift_map
                   (fun env' : data =>
                      olift (fun d1 : data => Some (dcoll (d1 :: nil)))
                            (h ⊢ₑ p1 @ₑ x ⊣ c;env')) l)); intros; simpl in *; try congruence.
    rewrite (oflatten_cons (d::nil) l1 l0).
    auto.
    destruct (oflatten l1); simpl in *; congruence.
    unfold lift in *.
    case_eq (oflatten l0); intros; simpl in *; try (rewrite H in *; congruence).
    unfold oflatten in *; simpl.
    rewrite H.
    reflexivity.
  Qed.

  Lemma flip_env1 p :
    χ⟨ENV⟩(σ⟨ p ⟩(‵{|ID|})) ◯ₑ ID ≡ₑ (σ⟨ p ⟩(‵{|ID|})) ◯ₑ ID.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;x); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct b; reflexivity.
  Qed.

  Lemma flip_env2 p :
    (σ⟨ p ⟩(‵{|ID|}) ◯ₑ ID) ≡ₑ σ⟨ p ◯ₑ ID ⟩(‵{|ID|}).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;x); reflexivity.
  Qed.

  Lemma flip_env3 b p1 p2 :
     (cNRAEnvBinop b p1 p2) ◯ₑ ID ≡ₑ (cNRAEnvBinop b (p1 ◯ₑ ID) (p2 ◯ₑ ID)).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; reflexivity.
  Qed.

  Lemma flip_env4 p1 p2 s :
     (cNRAEnvUnop (OpDot s) p1) ◯ₑ p2 ≡ₑ (cNRAEnvUnop (OpDot s) (p1 ◯ₑ p2)).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); reflexivity.
  Qed.

  Lemma flip_env5 p1 p2:
    ♯flatten(χ⟨σ⟨p1⟩(‵{|ID|})⟩(p2)) ≡ₑ σ⟨p1⟩(p2).
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    autorewrite with alg.
    induction l; try reflexivity; simpl.
    destruct (h ⊢ₑ p1 @ₑ a ⊣ c;env); try reflexivity; simpl.
    f_equal.
    destruct d; try reflexivity; simpl.
    destruct b; try reflexivity; simpl.
    - destruct ((lift_map
                (fun x0 : data =>
                 lift dcoll
                   match
                     match h ⊢ₑ p1 @ₑ x0 ⊣ c;env with
                     | Some (dbool b) => Some b
                     | _ => None
                     end
                   with
                   | Some true => Some (x0 :: nil)
                   | Some false => Some nil
                   | None => None
                   end) l)); destruct (lift_filter
         (fun x' : data =>
          match h ⊢ₑ p1 @ₑ x' ⊣ c;env with
          | Some (dbool b) => Some b
          | _ => None
          end) l); simpl in *.
      rewrite oflatten_cons with (r' := l1).
      simpl.
      reflexivity.
      unfold lift in IHl.
      destruct (oflatten l0); try congruence.
      unfold lift in IHl.
      unfold oflatten in *; simpl in *.
      destruct (lift_flat_map
            (fun x0 : data =>
             match x0 with
             | dcoll y => Some y
             | _ => None
             end) l0); try congruence; try reflexivity.
      congruence.
      reflexivity.
    - destruct ((lift_map
                (fun x0 : data =>
                 lift dcoll
                   match
                     match h ⊢ₑ p1 @ₑ x0 ⊣ c;env with
                     | Some (dbool b) => Some b
                     | _ => None
                     end
                   with
                   | Some true => Some (x0 :: nil)
                   | Some false => Some nil
                   | None => None
                   end) l)); destruct (lift_filter
         (fun x' : data =>
          match h ⊢ₑ p1 @ₑ x' ⊣ c;env with
          | Some (dbool b) => Some b
          | _ => None
          end) l); simpl in *.
      rewrite oflatten_cons with (r' := l1).
      reflexivity.
      unfold lift in *.
      destruct (oflatten l0); simpl in *.
      inversion IHl; reflexivity.
      congruence.
      unfold oflatten in *; simpl in *.
      destruct ((lift_flat_map
             (fun x0 : data =>
              match x0 with
              | dcoll y => Some y
              | _ => None
              end) l0)); simpl in *.
      congruence.
      reflexivity.
      congruence.
      reflexivity.
  Qed.

  Lemma flip_env7 p1 p2:
    nraenv_core_ignores_id p1 ->
    (cNRAEnvMapEnv (‵{| p1 |})) ◯ₑ p2 ≡ₑ χ⟨‵{| p1 ◯ₑ ID |}⟩(p2).
  Proof.
    unfold nraenv_core_eq; intros ? ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    rewrite (nraenv_core_ignores_id_swap p1 H h c a x a).
    destruct (h ⊢ₑ p1 @ₑ a ⊣ c;a); try reflexivity; simpl.
    destruct ((lift_map
             (fun env' : data =>
              olift (fun d1 : data => Some (dcoll (d1 :: nil)))
                    (h ⊢ₑ p1 @ₑ x ⊣ c;env')) l));
      destruct ((lift_map
           (fun x0 : data =>
            olift (fun d1 : data => Some (dcoll (d1 :: nil))) (h ⊢ₑ p1 @ₑ x0 ⊣ c;x0))
           l)); simpl in *; congruence.
  Qed.

  (* [ s1 : p1 ] ⊗ [ s2 : p2 ] ≡ { [ s1 : p1; s2 : p2 ] } *)
  
  Lemma merge_concat_to_concat s1 s2 p1 p2:
    s1 <> s2 ->
    ‵[| (s1, p1)|] ⊗ ‵[| (s2, p2)|] ≡ₑ ‵{|‵[| (s1, p1)|] ⊕ ‵[| (s2, p2)|]|}.
  Proof.
    intros.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p1 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity; simpl.
    unfold merge_bindings.
    simpl.
    unfold compatible_with; simpl.
    destruct (EquivDec.equiv_dec s1 s2); try congruence.
    simpl.
    reflexivity.
  Qed.

  (* [ s: p ].s ≡ p *)

  Lemma dot_over_rec s p :
    (‵[| (s, p)|]) · s ≡ₑ p.
  Proof.
    unfold nraenv_core_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); try reflexivity; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s s); congruence.
  Qed.

  (* optimizations for Either *)
  Lemma either_app_over_dleft p₁ p₂ d :
    (cNRAEnvEither p₁ p₂) ◯ (cNRAEnvConst (dleft d)) ≡ₑ p₁ ◯ (cNRAEnvConst d).
  Proof.
    red; simpl; intros; reflexivity.
  Qed.

  Lemma either_app_over_dright p₁ p₂ d :
    (cNRAEnvEither p₁ p₂) ◯ (cNRAEnvConst (dright d)) ≡ₑ p₂ ◯ (cNRAEnvConst d).
  Proof.
    red; simpl; intros; reflexivity.
  Qed.

  Lemma either_app_over_aleft p₁ p₂ p :
    (cNRAEnvEither p₁ p₂) ◯ (cNRAEnvUnop OpLeft p) ≡ₑ p₁ ◯ p.
  Proof.
    red; simpl; intros.
    unfold olift.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); trivial.
  Qed.
  
  Lemma either_app_over_aright p₁ p₂ p :
    (cNRAEnvEither p₁ p₂) ◯ (cNRAEnvUnop OpRight p) ≡ₑ p₂ ◯ p.
  Proof.
    red; simpl; intros.
    unfold olift.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); trivial.
  Qed.

  (** optimizations for record projection *)
  Lemma rproject_over_concat sl p1 p2 :
    π[sl](p1 ⊕ p2)
          ≡ₑ π[sl](p1) ⊕ π[sl](p2).
  Proof.
    red; simpl; intros.
    destruct (h ⊢ₑ p1 @ₑ x ⊣ c;env);
      destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env).
    - destruct d; destruct d0; simpl; trivial.
      rewrite rproject_rec_sort_commute, rproject_app.
      trivial.
    - destruct x; destruct d; simpl; trivial.
    - destruct x; destruct d; simpl; trivial.
    - destruct x; simpl; trivial.
  Qed.

  Lemma rproject_over_const sl l :
    π[sl](cNRAEnvConst (drec l)) ≡ₑ cNRAEnvConst (drec (Bindings.rproject l sl)).
  Proof.
    red; simpl; intros.
    rewrite rproject_rec_sort_commute.
    rewrite rproject_map_fst_same; intuition.
  Qed.
  
  Lemma rproject_over_rec_in sl s p :
    In s sl ->
    π[sl](‵[| (s, p) |]) ≡ₑ ‵[| (s, p) |].
  Proof.
    red; simpl; intros.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); simpl; trivial.
    destruct (in_dec string_dec s sl); intuition.
  Qed.

  Lemma rproject_over_rec_nin sl s p :
    ~ In s sl ->
    π[sl](‵[| (s, p) |]) ≡ₑ ‵[||] ◯ p .
  Proof.
    red; simpl; intros.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); simpl; trivial.
    destruct (in_dec string_dec s sl); intuition.
  Qed.
  
  Lemma rproject_over_rproject sl1 sl2 p :
    π[sl1](π[sl2](p)) ≡ₑ π[set_inter string_dec sl2 sl1](p).
  Proof.
    red; simpl; intros.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); simpl; trivial.
    destruct d; simpl; trivial.
    rewrite rproject_rproject.
    trivial.
  Qed.

  Lemma rproject_over_either sl p1 p2 :
    π[sl](cNRAEnvEither p1 p2) ≡ₑ cNRAEnvEither (π[sl](p1)) (π[sl](p2)).
  Proof.
    red; simpl; intros.
    destruct x; simpl; trivial.
  Qed.

  Lemma map_over_map_split p₁ p₂ p₃ :
    χ⟨χ⟨p₁ ⟩( p₂) ⟩( p₃) ≡ₑ χ⟨χ⟨p₁ ⟩( ID) ⟩(χ⟨p₂⟩(p₃)).
  Proof.
    red; simpl; intros.
    destruct (h ⊢ₑ p₃ @ₑ x ⊣ c; env); simpl; trivial.
    destruct d; simpl; trivial.
    unfold lift, olift.
    induction l; simpl; trivial.
    destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
    destruct (lift_map
              (fun x0 : data =>
               match h ⊢ₑ p₂ @ₑ x0 ⊣ c; env with
               | Some x'0 =>
                   lift_oncoll
                     (fun c1 : list data =>
                      match lift_map (nraenv_core_eval h c p₁ env) c1 with
                      | Some a' => Some (dcoll a')
                      | None => None
                      end) x'0
               | None => None
               end) l);
      destruct (lift_map (nraenv_core_eval h c p₂ env) l);
      simpl in * .
    - destruct (lift_map
            (fun x0 : data =>
             lift_oncoll
               (fun c1 : list data =>
                match lift_map (nraenv_core_eval h c p₁ env) c1 with
                | Some a' => Some (dcoll a')
                | None => None
                end) x0) l1); try discriminate.
      inversion IHl; clear IHl; subst.
      trivial.
    - discriminate.
    - destruct (lift_map
            (fun x0 : data =>
             lift_oncoll
               (fun c1 : list data =>
                match lift_map (nraenv_core_eval h c p₁ env) c1 with
                | Some a' => Some (dcoll a')
                | None => None
                end) x0) l0); try discriminate.
      trivial.
    - destruct ( lift_oncoll
         (fun c1 : list data =>
          match lift_map (nraenv_core_eval h c p₁ env) c1 with
          | Some a' => Some (dcoll a')
          | None => None
          end) d); trivial.
  Qed.
  
  (* optimization for distinct *)
  Definition nodupA : nraenv_core -> Prop :=
    nraenv_core_always_ensures
      (fun d => match d with
                | dcoll dl => NoDup dl
                | _ => False
                end).
  
  Lemma dup_elim (q:nraenv_core) :
    nodupA q -> cNRAEnvUnop OpDistinct q  ≡ₑ  q.
  Proof.
    intros nd.
    red; intros.
    simpl.
    case_eq (h ⊢ₑ q @ₑ x ⊣ c; env); simpl; trivial; intros.
    specialize (nd h c dn_c env dn_env x dn_x d H).
    simpl in nd.
    match_destr_in nd; try tauto.
    rewrite rondcoll_dcoll.
    rewrite NoDup_bdistinct; trivial.
  Qed.

  (** Some optimizations are best seen through outlining -- the 
       opposite of inlining.  This allows sharing of common sub-expressions.
       To enable this, we first define the "last" part of a computation.
  *)
  
  (* Find the last part of the computation and split it off.  
This is the first operation that
    would actually be done on input data. cNRAEnvID means that either it is cNRAEnvID     or none such can be found.  We don't bother trying to unify the 
    continuation of binops or cNRAEnvEIther
    since that would be done separately anyway *)
  (** returns: (last part of the computation, rest of it) *)
  Fixpoint nraenv_core_split_last (e:nraenv_core) : (nraenv_core*nraenv_core)
    := match e with
         | cNRAEnvID => (cNRAEnvID,cNRAEnvID)
         | cNRAEnvConst c =>  (cNRAEnvID,cNRAEnvConst c)
         | cNRAEnvBinop b e1 e2 => (cNRAEnvBinop b e1 e2,cNRAEnvID)
         | cNRAEnvUnop u e1 =>
           match nraenv_core_split_last e1 with
             | (cNRAEnvID, r) => (cNRAEnvUnop u r, cNRAEnvID)
             | (e1last, e1rest) => (e1last, cNRAEnvUnop u e1rest)
           end
         | cNRAEnvMap e1 e2 =>
           match nraenv_core_split_last e2 with
             | (cNRAEnvID, r) => (cNRAEnvMap e1 e2, cNRAEnvID)
             | (e2last, e2rest) => (e2last, cNRAEnvMap e1 e2rest)
           end
         | cNRAEnvMapProduct e1 e2 =>
           match nraenv_core_split_last e2 with
             | (cNRAEnvID, r) => (cNRAEnvMapProduct e1 e2, cNRAEnvID)
             | (e2last, e2rest) => (e2last, cNRAEnvMapProduct e1 e2rest)
           end
         | cNRAEnvProduct e1 e2 => (cNRAEnvProduct e1 e2,cNRAEnvID)
         | cNRAEnvSelect e1 e2 =>
           match nraenv_core_split_last e2 with
             | (cNRAEnvID, r) => (cNRAEnvSelect e1 e2, cNRAEnvID)
             | (e2last, e2rest) => (e2last, cNRAEnvSelect e1 e2rest)
           end         
         | cNRAEnvDefault e1 e2 => (cNRAEnvDefault e1 e2,cNRAEnvID)
         | cNRAEnvEither l r => (cNRAEnvEither l r, cNRAEnvID)
         | cNRAEnvEitherConcat l r =>
           (cNRAEnvEitherConcat l r, cNRAEnvID)
         | cNRAEnvApp e1 e2 =>
           match nraenv_core_split_last e2 with
             | (cNRAEnvID, r) => (e1, r)
             | (e2last, e2rest) => (e2last, cNRAEnvApp e1 e2rest)
           end         
         | cNRAEnvGetConstant s => (cNRAEnvID,cNRAEnvGetConstant s)
         | cNRAEnvEnv => (cNRAEnvID,cNRAEnvEnv)
         | cNRAEnvAppEnv e1 e2 => (cNRAEnvAppEnv e1 e2, cNRAEnvID)
         | cNRAEnvMapEnv e => (cNRAEnvMapEnv e, cNRAEnvID)
       end.

  
End ROptimEnv.

(* begin hide *)
(* Hints for optimization tactic

   Note: all of those are valid, indepently of typing
   Note: those marked with ** can be generalized with proper type
   information
*)

(*
       -- Those simplify over singleton collections
       envflatten_map_coll : ♯flatten(χ⟨ { p1 } ⟩( p2 )) ≡ χ⟨ p1 ⟩( p2 )
    ** envmap_into_id : χ⟨ ID ⟩( { P } ) ≡ { P }
    ** envmap_into_id_flatten : χ⟨ ID ⟩( ♯flatten( P ) ) ≡ ♯flatten( P )
    Generalized into: tenvmap_into_id
*)

Hint Rewrite @envflatten_map_coll : nraenv_core_optim.
Hint Rewrite @envmap_into_id : nraenv_core_optim.
Hint Rewrite @envmap_into_id_flatten : nraenv_core_optim.

(*
       -- Those introduce a ◯ , but remove a χ
       envmap_map_compose : χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ≡ χ⟨ P1 ◯ P2 ⟩( P3 )
       envmap_singleton : χ⟨ P1 ⟩( { P2 } ) ≡ { P1 ◯ P2 }
*)

Hint Rewrite @envmap_map_compose : nraenv_core_optim.
Hint Rewrite @envmap_singleton : nraenv_core_optim.

(*
       -- Those remove over flatten
    ** envflatten_coll_mergeconcat: ♯flatten( { cNRAEnvBinop AMergeConcat p1 p2 } ) ≡ (cNRAEnvBinop AMergeConcat p1 p2)
    ** envflatten_coll_map : ♯flatten( { χ⟨ p1 ⟩( p2 ) } ) ≡ χ⟨ p1 ⟩( p2 )
    ** envflatten_coll_flatten : ♯flatten({ ♯flatten( p ) }) ≡ ♯flatten( p )
    ** envflatten_coll_coll : ♯flatten({ { p } }) ≡ ♯flatten( p )
    Generalized into: tenvflatten_coll
*)

Hint Rewrite @envflatten_coll_mergeconcat : nraenv_core_optim.
Hint Rewrite @envflatten_coll_map : nraenv_core_optim.
Hint Rewrite @envflatten_coll_flatten : nraenv_core_optim.
Hint Rewrite @envflatten_coll_coll : nraenv_core_optim.

(*
       -- Those push-down or remove ◯
       app_over_id : p ◯ ID ≡ p
       app_over_id_l : ID ◯ p ≡ p
       app_over_app : o(p1 ◯ p2) ◯ p3 ≡ p1 ◯ (p2 ◯ p3)
       app_over_map : χ⟨ p1 ⟩( p2 ) ◯ p0 ≡ χ⟨ p1 ⟩( p2 ◯ p0 )
       app_over_select : σ⟨ p1 ⟩( p2 ) ◯ p0 ≡ σ⟨ p1 ⟩( p2 ◯ p0 )
       app_over_unop : (cNRAEnvUnop u p1) ◯ p2 ≡ₑ (cNRAEnvUnop u (p1 ◯ p2))
       app_over_binop_l : (cNRAEnvBinop b p2 (cNRAEnvConst d) ◯ p1) ≡ (cNRAEnvBinop b (p2 ◯ p1) (cNRAEnvConst d))
       app_over_merge : (ENV ⊗ p1) ◯ p2 ≡ₑ ENV ⊗ (p1 ◯ p2)
       app_over_rec : [ a : P1 ] ◯ P2 ≡ [ a : P1 ◯ P2 ]
       binop_over_rec_pair : (cNRAEnvBinop b ID.a1 ID.a2) ◯ ([ a1 : p1; a2 : p2 ]) ≡ cNRAEnvBinop b p1 p2
       concat_id_left : ([ a1 : p1; a2 : d ]) ◯ p2 ≡ [ a1 : p1 ◯ p2; a2 : d ]
       app_over_env_dot : (ENV ◯ (ENV.a)).a ≡ₑ ENV.a
       app_over_appenv_over_mapenv :
             ((χᵉ⟨‵{|ENV|} ⟩( ID)) ◯ₑ (χ⟨ENV ⟩( σ⟨p1 ⟩( ‵{|ID|})))) ◯ p2
          ≡ₑ (χᵉ⟨‵{|ENV|} ⟩( ID)) ◯ₑ (χ⟨ENV ⟩( σ⟨p1 ⟩( ‵{|ID|}))) ◯ p2
*)

Hint Rewrite @app_over_id : nraenv_core_optim.
Hint Rewrite @app_over_id_l : nraenv_core_optim.
Hint Rewrite @app_over_app : nraenv_core_optim.           (* Not in ROptimEnvFunc *)
Hint Rewrite @app_over_map : nraenv_core_optim.
Hint Rewrite @app_over_select : nraenv_core_optim.
Hint Rewrite @app_over_unop : nraenv_core_optim.
Hint Rewrite @app_over_binop_l : nraenv_core_optim.
Hint Rewrite @app_over_merge : nraenv_core_optim.
Hint Rewrite @app_over_rec : nraenv_core_optim.
Hint Rewrite @binop_over_rec_pair : nraenv_core_optim.
Hint Rewrite @concat_id_left : nraenv_core_optim.
Hint Rewrite @app_over_env_dot : nraenv_core_optim.
Hint Rewrite @app_over_appenv_over_mapenv : nraenv_core_optim.

(*
       -- Other misc rewrites
       product_singletons : { [ s1 : p1 ] } × { [ s2 : p2 ] } ≡ { [ s1 : p1; s2 : p2 ] }
       double_flatten_map_coll : ♯flatten(χ⟨ χ⟨ { ID } ⟩( ♯flatten( p1 ) ) ⟩( p2 ))
                                 ≡ χ⟨ { ID } ⟩(♯flatten(χ⟨ ♯flatten( p1 ) ⟩( p2 )))
*)

Hint Rewrite @product_singletons : nraenv_core_optim.
Hint Rewrite @double_flatten_map_coll : nraenv_core_optim.

(*
       -- Those handle operators on the environment
       appenv_over_mapenv : χᵉ⟨ { ENV } ⟩(ID) ◯ₑ ♯flatten(p) ≡ χ⟨ { ID } ⟩(♯flatten(p))
       appenv_over_mapenv_coll : (χᵉ⟨ { { ENV } } ⟩(ID) ◯ₑ ♯flatten(p)) ≡ χ⟨ { { ID } } ⟩(♯flatten(p))
       appenv_over_mapenv_merge : (χᵉ⟨ { ENV.e } ⟩(ID) ◯ₑ cNRAEnvBinop AMergeConcat ENV ID)
                                   ≡ₑ χ⟨ { ID.e } ⟩(cNRAEnvBinop AMergeConcat ENV ID)
*)

Hint Rewrite @env_appenv : nraenv_core_optim.
Hint Rewrite @appenv_over_mapenv : nraenv_core_optim.
Hint Rewrite @appenv_over_mapenv_coll : nraenv_core_optim.
Hint Rewrite @appenv_over_mapenv_merge : nraenv_core_optim.
Hint Rewrite @appenv_over_mapenv_merge2 : nraenv_core_optim.
Hint Rewrite @compose_selects_in_mapenv : nraenv_core_optim.
Hint Rewrite @flatten_through_appenv : nraenv_core_optim.
Hint Rewrite @flatten_mapenv_coll : nraenv_core_optim.

(* Simple optimizations for either *)
Hint Rewrite @either_app_over_dleft : nraenv_core_optim.
Hint Rewrite @either_app_over_dright : nraenv_core_optim.
Hint Rewrite @either_app_over_aleft : nraenv_core_optim.
Hint Rewrite @either_app_over_aright : nraenv_core_optim.

(* Optimizations for rproject *)
Hint Rewrite @rproject_over_concat : nraenv_core_optim.
Hint Rewrite @rproject_over_rec_in : nraenv_core_optim. 
Hint Rewrite @rproject_over_rec_nin : nraenv_core_optim. 
Hint Rewrite @rproject_over_rproject : nraenv_core_optim. 
Hint Rewrite @rproject_over_either  : nraenv_core_optim.
  
(* end hide *)

