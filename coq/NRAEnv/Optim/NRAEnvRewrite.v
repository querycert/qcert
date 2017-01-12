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

Section ROptimEnv.

  Require Import List String.
  Require Import ListSet.

  Require Import Utils BasicRuntime.

  Require Import NRARuntime NRAOptim.
  Require Import cNRAEnv cNRAEnvIgnore cNRAEnvEq.

  (* Some of algebraic equivalences for NRA with environment *)
  (* Those are valid without type *)

  Local Open Scope alg_scope.
  Local Open Scope cnraenv_scope.

  Context {fruntime:foreign_runtime}.

  (* Pulls equivalences from core algebra *)

  Hint Resolve dnrec_sort.
  Lemma pull_alg_opt (p1 p2:cnraenv) :
    (alg_of_cnraenv p1) ≡ₐ (alg_of_cnraenv p2) ->
    p1 ≡ₑ p2.
  Proof.
    unfold alg_eq, cnraenv_eq; intros.
    repeat rewrite unfold_env_alg_sort.
    rewrite H; eauto.
  Qed.

  (* P1 ∧ P2 ≡ P2 ∧ P1 *)

  Lemma envand_comm (p1 p2: cnraenv) :
    p2 ∧ p1 ≡ₑ p1 ∧ p2.
  Proof.
    apply pull_alg_opt.
    unfold alg_of_cnraenv.
    rewrite and_comm; reflexivity.
  Qed.

  (* (P1 ⋃ P2) ⋃ P3 ≡ P1 ⋃ (P2 ⋃ P3) *)

  Lemma envunion_assoc (p1 p2 p3: cnraenv):
    (p1 ⋃ p2) ⋃ p3 ≡ₑ p1 ⋃ (p2 ⋃ p3).
  Proof.
    apply pull_alg_opt.
    unfold alg_of_cnraenv.
    rewrite union_assoc; reflexivity.
  Qed.
  
  (* σ⟨ P ⟩(P1 ⋃ P2) ≡ σ⟨ P ⟩(P1) ⋃ σ⟨ P ⟩(P2) *)

  Lemma envunion_select_distr (p p1 p2: cnraenv) :
    σ⟨ p ⟩(p1 ⋃ p2) ≡ₑ σ⟨ p ⟩(p1) ⋃ σ⟨ p ⟩(p2).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _.
    simpl.
    generalize (h ⊢ₑ p1 @ₑ x  ⊣ c;env) as d1.
    generalize (h ⊢ₑ p2 @ₑ x  ⊣ c;env) as d2.
    intros.
    destruct d1; destruct d2; try (autorewrite with alg; reflexivity); simpl.
    destruct d; try reflexivity.
    destruct d0; simpl;
    try (destruct (lift_filter
                     (fun x' : data =>
                        match h ⊢ₑ p @ₑ x' ⊣ c;env with
                          | Some (dbool b) => Some b
                          | _ => None
                        end) l); simpl; reflexivity).
    induction l; simpl.
      destruct (lift_filter
         (fun x' : data =>
          match h ⊢ₑ p @ₑ x' ⊣ c;env with
          | Some (dbool b) => Some b
          | _ => None
          end) l0); reflexivity.
      generalize(h ⊢ₑ p @ₑ a ⊣ c;env); intros.
      unfold bunion.
      rewrite lift_app_filter.
      destruct o; try reflexivity.
      destruct d; try reflexivity.
      revert IHl.
      generalize ((lift_filter
            (fun x' : data =>
             match h ⊢ₑ p @ₑ x' ⊣ c;env with
             | Some (dbool b0) => Some b0
             | _ => None
             end) l)).
      generalize (lift_filter
             (fun x' : data =>
              match h ⊢ₑ p @ₑ x' ⊣ c;env with
              | Some (dbool b0) => Some b0
              | _ => None
              end) l0).
      intros.
      destruct o0; try reflexivity. simpl.
      destruct o; try reflexivity.
      + destruct b; autorewrite with alg; reflexivity.
      + autorewrite with alg. reflexivity. 
  Qed.

  (* this is the name we give it in the paper *)
    (* σ⟨ P ⟩(P1 ⋃ P2) ≡ σ⟨ P ⟩(P1) ⋃ σ⟨ P ⟩(P2) *)
  Lemma select_union_distr (q q₁ q₂: cnraenv) :
    σ⟨ q ⟩(q₁ ⋃ q₂) ≡ₑ σ⟨ q ⟩(q₁) ⋃ σ⟨ q ⟩(q₂).
  Proof.
    apply envunion_select_distr.
  Qed.

  (* χ⟨ P1 ⟩( { P2 } ) ≡ { P1 ◯ P2 } *)

  Lemma envmap_singleton (p1 p2:cnraenv) :
    χ⟨ p1 ⟩( ‵{| p2 |} ) ≡ₑ ‵{| p1 ◯ p2 |}.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    generalize (h ⊢ₑ p1 @ₑ d ⊣ c;env); intros; simpl.
    destruct o; reflexivity.
  Qed.

  (* χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ≡ χ⟨ P1 ◯ P2 ⟩( P3 ) *)

  Lemma envmap_map_compose (p1 p2 p3:cnraenv) :
    χ⟨ p1 ⟩( χ⟨ p2 ⟩( p3 ) ) ≡ₑ χ⟨ p1 ◯ p2 ⟩( p3 ).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p3 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    unfold olift, lift; simpl.
    induction l; try reflexivity; simpl.
    generalize (h ⊢ₑ p2 @ₑ a ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    revert IHl; generalize (rmap (cnraenv_eval h c p2 env) l); intros.
    destruct o; try reflexivity; simpl.
    destruct (h ⊢ₑ p1 @ₑ d ⊣ c;env); try reflexivity; simpl.
    revert IHl; generalize (rmap
              (fun x0 : data =>
               match h ⊢ₑ p2 @ₑ x0 ⊣ c;env with
               | Some x'0 => h ⊢ₑ p1 @ₑ x'0 ⊣ c;env
               | None => None
               end) l); intros.
    destruct o; try reflexivity; simpl in *.
    destruct (rmap (cnraenv_eval h c p1 env) l0).
    inversion IHl; reflexivity.
    congruence.
    destruct (rmap (cnraenv_eval h c p1 env) l0).
    congruence.
    reflexivity.
    revert IHl; generalize (rmap
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* ♯flatten({ ♯flatten( p ) }) ≡ ♯flatten( p ) *)
  
  Lemma envflatten_coll_flatten p:
    ♯flatten(‵{| ♯flatten( p ) |}) ≡ₑ ♯flatten( p ).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; try reflexivity; simpl.
    unfold olift; simpl.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    unfold lift, rflatten in *; simpl in *.
    destruct a; try reflexivity.
    revert IHl; generalize (oflat_map
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; reflexivity.
  Qed.

  Lemma envflatten_nil :
    ♯flatten(‵{||}) ≡ₑ ‵{||}.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    trivial.
  Qed.

  (* ♯flatten({ χ⟨ p1 ⟩( p2 ) }) ≡ χ⟨ p1 ⟩( p2 ) *)
  
  Lemma envflatten_coll_map p1 p2 :
    ♯flatten(‵{| χ⟨ p1 ⟩( p2 ) |}) ≡ₑ χ⟨ p1 ⟩( p2 ).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    unfold olift in *; simpl in *.
    generalize (h ⊢ₑ p1 @ₑ a ⊣ c;env); clear a; intros.
    destruct o; try reflexivity; simpl.
    unfold lift in *; simpl in *.
    revert IHl; generalize (rmap (cnraenv_eval h c p1 env) l); intros.
    destruct o; try reflexivity; try congruence.
    unfold lift_oncoll in *; simpl in *.
    rewrite app_nil_r.
    rewrite app_nil_r in IHl.
    inversion IHl; reflexivity.
  Qed.

  Lemma flatten_flatten_map_either_nil p₁ p₂ p₃ :
    ♯flatten( ♯flatten(χ⟨ANEither p₁ ‵{||} ◯ p₂⟩(p₃))) ≡ₑ 
     ♯flatten( χ⟨ANEither( ♯flatten(p₁)) ‵{||} ◯ p₂⟩(p₃)).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p₃ @ₑ x ⊣ c; env); simpl; trivial.
    unfold olift.
    destruct d; simpl; trivial.
    induction l; simpl; trivial.
    unfold lift in *.
    destruct ( rmap
                (fun x0 : data =>
                 match h ⊢ₑ p₂ @ₑ x0 ⊣ c; env with
                 | Some (dleft dl) => h ⊢ₑ p₁ @ₑ dl ⊣ c; env
                 | Some (dright _) => Some (dcoll nil)
                 | Some _ => None
                 | None => None
                 end) l); simpl in *;
    destruct (rmap
              (fun x0 : data =>
               match h ⊢ₑ p₂ @ₑ x0 ⊣ c; env with
               | Some (dleft dl) =>
                   match h ⊢ₑ p₁ @ₑ dl ⊣ c; env with
                   | Some x'0 =>
                       lift_oncoll
                         (fun l1 : list data =>
                          match rflatten l1 with
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
      case_eq (rflatten l0);
        [intros ? eqq0 | intros eqq0]; rewrite eqq0 in *;
        (case_eq (rflatten l1);
         [intros ? eqq1 | intros eqq1]; rewrite eqq1 in *;
           simpl in IHl); try discriminate.
      + case_eq (rflatten l2);
        [intros ? eqq2 | intros eqq2]; try rewrite eqq2 in *;
        try discriminate.
        inversion IHl; clear IHl; subst.
        destruct d; simpl; trivial.
        * destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
          destruct d0; simpl; trivial.
          rewrite (rflatten_cons _ _ _ eqq0).
          simpl.
          { case_eq (rflatten l4);
            [intros ? eqq4 | intros eqq4]; simpl.
            - rewrite (rflatten_cons _ _ _ eqq1).
              rewrite (rflatten_app _ _ _ _ eqq4 eqq2).
              trivial.
            -  rewrite (rflatten_app_none1 _ _ eqq4).
               trivial.
          } 
        * rewrite (rflatten_cons _ _ _ eqq0).
          rewrite (rflatten_cons _ _ _ eqq1).
          simpl.
          rewrite eqq2.
          trivial.
      +  case_eq (rflatten l2);
        [intros ? eqq2 | intros eqq2]; try rewrite eqq2 in *;
        try discriminate.
         destruct d; simpl; trivial.
        * destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
          destruct d0; simpl; trivial.
          rewrite (rflatten_cons _ _ _ eqq0).
          simpl.
          rewrite (rflatten_app_none2 _ _ eqq2).
          destruct (rflatten l3); simpl; trivial.
          rewrite (rflatten_cons_none _ _ eqq1).
          trivial.
        * rewrite (rflatten_cons _ _ _ eqq0).
          simpl.
          rewrite (rflatten_cons_none _ _ eqq1).
          rewrite eqq2.
          trivial.
      + destruct d; simpl; trivial.
        * destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
          rewrite (rflatten_cons_none _ _ eqq0).
          destruct d0; simpl; trivial.
          destruct (rflatten l2); simpl; trivial.
          rewrite (rflatten_cons_none _ _ eqq1).
          trivial.
        * rewrite (rflatten_cons_none _ _ eqq0).
          rewrite (rflatten_cons_none _ _ eqq1).
          trivial.
    - destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
      destruct d; simpl; trivial.
      + destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
        destruct d0; simpl; trivial.
        case_eq (rflatten l0);
          [intros ? eqq0 | intros eqq0]; rewrite eqq0 in *; simpl in *.
        * case_eq (rflatten l2);
          [intros ? eqq2 | intros eqq2]; rewrite eqq2 in *; try discriminate.
          rewrite (rflatten_cons _ _ _ eqq0); simpl.
          rewrite (rflatten_app_none2 _ _ eqq2).
          destruct (rflatten l1); trivial.
        * rewrite (rflatten_cons_none _ _ eqq0).
          destruct (rflatten l1); trivial.
      + case_eq (rflatten l0);
            [intros ? eqq0 | intros eqq0]; rewrite eqq0 in *; simpl in *.
        * case_eq (rflatten l1);
          [intros ? eqq1 | intros eqq1]; rewrite eqq1 in *; try discriminate.
          rewrite (rflatten_cons _ _ _ eqq0); simpl.
          rewrite eqq1.
          trivial.
        * rewrite (rflatten_cons_none _ _ eqq0).
          trivial.
    - case_eq (rflatten l0);
      [intros ? eqq0 | intros eqq0];
       rewrite eqq0 in *; simpl in *; try discriminate.
      destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
      destruct d; simpl; trivial.
      + destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
        destruct d0; simpl; trivial.
        destruct (rflatten l1); simpl; trivial.
        rewrite (rflatten_cons_none _ _ eqq0).
        trivial.
      + rewrite (rflatten_cons_none _ _ eqq0).
        trivial.
    - destruct (h ⊢ₑ p₂ @ₑ a ⊣ c; env); simpl; trivial.
      destruct d; simpl; trivial.
      destruct (h ⊢ₑ p₁ @ₑ d ⊣ c; env); simpl; trivial.
      destruct d0; simpl; trivial.
      destruct (rflatten l0); simpl; trivial.
  Qed.
      
  (* ♯flatten( ‵{| p1 ⊗ p2 |} ) ≡ p1 ⊗ p2 *)

  Lemma envflatten_coll_mergeconcat p1 p2:
    ♯flatten( ‵{| p1 ⊗ p2 |} ) ≡ₑ p1 ⊗ p2.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); clear p1; intros.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; destruct o0; try reflexivity; simpl.
    destruct d; destruct d0; try reflexivity; simpl.
    destruct (merge_bindings l l0); reflexivity.
  Qed.

  (* ♯flatten(χ⟨ χ⟨ { ID } ⟩( ♯flatten( p1 ) ) ⟩( p2 ))
            ≡ χ⟨ { ID } ⟩(♯flatten(χ⟨ ♯flatten( p1 ) ⟩( p2 ))) *)

  Lemma rmap_to_map l :
    rmap (fun x : data => Some (dcoll (x :: nil))) l =
    Some (map (fun x : data => (dcoll (x :: nil))) l).
  Proof.
    induction l; [reflexivity|simpl; rewrite IHl; reflexivity].
  Qed.

  Lemma double_flatten_map_coll p1 p2 :
    ♯flatten(χ⟨ χ⟨ ‵{| ID |} ⟩( ♯flatten( p1 ) ) ⟩( p2 ))
            ≡ₑ χ⟨ ‵{| ID |} ⟩(♯flatten(χ⟨ ♯flatten( p1 ) ⟩( p2 ))).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    unfold olift in *; simpl in *.
    induction l; try reflexivity; simpl.
    generalize (h ⊢ₑ p1 @ₑ a ⊣ c;env); clear a; intros.
    destruct o; try reflexivity; simpl.
    destruct (lift_oncoll (fun l0 : list data => lift dcoll (rflatten l0)) d); try reflexivity; simpl.
    unfold lift in *; simpl in *.
    destruct (         rmap
           (fun x : data =>
            match h ⊢ₑ p1 @ₑ x ⊣ c;env with
            | Some x' =>
                lift_oncoll
                  (fun l0 : list data =>
                   match rflatten l0 with
                   | Some a' => Some (dcoll a')
                   | None => None
                   end) x'
            | None => None
            end) l); try reflexivity; try congruence; simpl in *.
    - unfold rflatten, lift_oncoll in *; simpl in *.
      destruct d0; try reflexivity; try congruence; simpl in *.
      generalize (rmap_to_map l1); intros.
      rewrite H; clear H; simpl.
      destruct (            rmap
              (fun x : data =>
               match
                 match h ⊢ₑ p1 @ₑ x ⊣ c;env with
                 | Some (dcoll l1) =>
                     match
                       oflat_map
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
                     rmap (fun x0 : data => Some (dcoll (x0 :: nil))) l1
                   with
                   | Some a' => Some (dcoll a')
                   | None => None
                   end
               | _ => None
               end) l
               ); try reflexivity; try congruence; simpl in *.
      destruct ((oflat_map
          (fun x : data =>
           match x with
           | dcoll y => Some y
           | _ => None
           end) l2)); try reflexivity; try congruence; simpl in *.
      destruct (       (oflat_map
          (fun x : data =>
           match x with
           | dcoll y => Some y
           | _ => None
           end) l0)); try reflexivity; try congruence; simpl in *.
      generalize (rmap_to_map l4); intros.
      rewrite H in *; clear H.
      generalize (rmap_to_map (l1++l4)); intros.
      rewrite H in *; clear H.
      inversion IHl; clear IHl H0.
      * rewrite map_app; simpl; reflexivity.
      * destruct ((oflat_map
                   (fun x : data =>
                      match x with
                        | dcoll y => Some y
                        | _ => None
                      end) l0)); try reflexivity; try congruence; simpl in *.
        generalize (rmap_to_map l3); intros.
        rewrite H in *; clear H; congruence.
      * destruct ((oflat_map
                     (fun x : data =>
                        match x with
                          | dcoll y => Some y
                          | _ => None
                        end) l0)); try reflexivity; try congruence; simpl in *.
        generalize (rmap_to_map l2); intros.
        rewrite H in *; clear H; congruence.
    - destruct d0; try reflexivity; try congruence; simpl in *.
      destruct (rmap (fun x : data => Some (dcoll (x :: nil))) l0); try reflexivity; try congruence; simpl.
      destruct (            rmap
              (fun x : data =>
               match
                 match h ⊢ₑ p1 @ₑ x ⊣ c;env with
                 | Some x' =>
                     lift_oncoll
                       (fun l0 : list data =>
                        match rflatten l0 with
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
                        rmap (fun x0 : data => Some (dcoll (x0 :: nil))) c1
                      with
                      | Some a' => Some (dcoll a')
                      | None => None
                      end) x'
               | None => None
               end) l); try reflexivity; try congruence; simpl in *.
      unfold rflatten in *; simpl.
      destruct (oflat_map
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); clear x p2; intros.
    destruct o; try reflexivity.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    generalize (h ⊢ₑ p1 @ₑ a ⊣ c;env); clear a; intros; simpl.
    destruct o; try reflexivity; simpl.
    unfold olift in *.
    revert IHl.
    generalize (rmap
             (fun x : data =>
              match h ⊢ₑ p1 @ₑ x ⊣ c;env with
              | Some x' => Some (dcoll (x' :: nil))
              | None => None
              end) l); generalize (rmap (cnraenv_eval h c p1 env) l); intros.
    unfold lift in *; simpl.
    destruct o; destruct o0; simpl; try reflexivity; try congruence.
    - simpl in *.
      unfold rflatten in *; simpl in *.
      revert IHl.
      generalize ((oflat_map
                     (fun x : data =>
                        match x with
                          | dcoll y => Some y
                          | _ => None
                        end) l1)); intros; simpl in *.
      destruct o; try congruence.
      inversion IHl; clear IHl H0; reflexivity.
    - simpl in *.
      unfold rflatten in *; simpl.
      revert IHl.
      generalize ((oflat_map
                     (fun x : data =>
                        match x with
                          | dcoll y => Some y
                          | _ => None
                        end) l0)); intros; simpl in *.
      destruct o; try congruence; reflexivity.
  Qed.

  Lemma select_over_nil p₁ :
    σ⟨p₁⟩(ANConst (dcoll nil)) ≡ₑ ANConst (dcoll nil).
  Proof.
    red; intros br env dn_env d dn_d.
    simpl; trivial.
  Qed.

  Lemma map_over_nil p₁ :
    χ⟨p₁⟩(ANConst (dcoll nil)) ≡ₑ ANConst (dcoll nil).
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
    case_eq (rflatten l); [intros ? eqq1 | intros eqq1];
    rewrite eqq1 in IHl; simpl in *;
    [rewrite (rflatten_cons _ _ _ eqq1) | rewrite (rflatten_cons_none _ _ eqq1)]
    ; (case_eq (rmap
                 (fun x : data =>
                  lift_oncoll
                    (fun c1 : list data =>
                     lift dcoll (rmap (cnraenv_eval br c p₁ env) c1)) x) l);  [intros ? eqq2 | intros eqq2];
     rewrite eqq2 in IHl; simpl in * ).
    - apply lift_injective in IHl; [ | inversion 1; trivial].
      rewrite rmap_over_app.
      rewrite IHl.
      destruct (rmap (cnraenv_eval br c p₁ env) l0); simpl; trivial.
    - apply none_lift in IHl.
      rewrite rmap_over_app.
      rewrite IHl; simpl.
      destruct (rmap (cnraenv_eval br c p₁ env) l0); simpl; trivial.
    - clear IHl.
      cut False; [intuition | ].
      revert eqq1 l1 eqq2.
      induction l; simpl in *; try discriminate.
      destruct a; simpl in *; try discriminate.
      intros.
      unfold rflatten in *.
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
    case_eq (rflatten l); [intros ? eqq1 | intros eqq1];
    rewrite eqq1 in IHl; simpl in *;
    [rewrite (rflatten_cons _ _ _ eqq1) | rewrite (rflatten_cons_none _ _ eqq1)];
    (case_eq (rmap
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
      unfold rflatten in *.
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
    σ⟨p₁⟩( ANEither p₂ p₃) ≡ₑ ANEither (σ⟨p₁⟩(p₂)) (σ⟨p₁⟩(p₃)).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    match_destr.
  Qed.

  (* [ a1 : p1; a2 : p1 ].a2 ≡ p1 *)
  (** Now has a (better) typed variant for arbitrary p1/p2, see TOptimEnv *)

  Lemma envdot_from_duplicate_r s1 s2 p1 :
    (‵[| (s1, p1) |] ⊕ ‵[| (s2, p1) |])·s2 ≡ₑ p1.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
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
    χ⟨p₁⟩( ANEither p₂ p₃) ≡ₑ ANEither (χ⟨p₁⟩(p₂)) (χ⟨p₁⟩(p₃)).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    match_destr.
  Qed.

  Lemma envmap_over_either_app p₁ p₂ p₃ p₄:
    χ⟨p₁⟩( ANEither p₂ p₃ ◯ p₄) ≡ₑ ANEither (χ⟨p₁⟩(p₂)) (χ⟨p₁⟩(p₃)) ◯ p₄.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    unfold olift.
    destruct (h ⊢ₑ p₄ @ₑ x ⊣ c; env); simpl; trivial.
    destruct d; simpl; trivial.
  Qed.

  (* χ⟨ ID ⟩( { P } ) ≡ { P } *)
  
  Lemma envmap_into_id p :
    χ⟨ ID ⟩(‵{| p |}) ≡ₑ ‵{| p |}.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; reflexivity.
  Qed.

  

  (* χ⟨ ID ⟩( ♯flatten(P) ) ≡ ♯flatten(P) *)
  
  Lemma envmap_into_id_flatten p :
    χ⟨ ID ⟩( ♯flatten(p) ) ≡ₑ ♯flatten(p).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); clear x p; intros.
    destruct o; try reflexivity; simpl.
    unfold lift_oncoll; simpl.
    destruct d; try reflexivity; simpl.
    unfold olift, lift; simpl.
    destruct (rflatten l); try reflexivity; clear l; simpl.
    induction l0; try reflexivity; simpl.
    unfold lift; simpl.
    revert IHl0; destruct (rmap (fun x: data => Some x) l0); congruence.
  Qed.

  (* { [ s1 : p1 ] } × { [ s2 : p2 ] } ≡ { [ s1 : p1; s2 : p2 ] } *)

  Lemma product_singletons s1 s2 p1 p2:
    ‵{|‵[| (s1, p1) |] |} × ‵{| ‵[| (s2, p2) |] |} ≡ₑ
     ‵{|‵[| (s1, p1) |] ⊕ ‵[| (s2, p2) |] |}.
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; destruct o0; reflexivity.
  Qed.

  (* p ◯ ID ≡ p *)
  
  Lemma app_over_id p:
    p ◯ ID ≡ₑ p.
  Proof.
    unfold alg_eq, cnraenv_eq; intros; reflexivity.
  Qed.    

  (* ENV ◯ₑ p ≡ p *)
  
  Lemma appenv_over_env p:
    ENV ◯ₑ p ≡ₑ p.
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); reflexivity.
  Qed.

  (* ID ◯ p ≡ p *)
  
  Lemma app_over_id_l p:
    ID ◯ p ≡ₑ p.
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (p1 ◯ p2) ◯ p3 ≡ p1 ◯ (p2 ◯ p3) *)
  
  Lemma app_over_app p1 p2 p3:
    (p1 ◯ p2) ◯ p3  ≡ₑ p1 ◯ (p2 ◯ p3).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p3 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (ANUnop u p1) ◯ p2 ≡ (ANUnop u (p1 ◯ p2)) *)

  Lemma app_over_unop u p1 p2:
    (ANUnop u p1) ◯ p2 ≡ₑ (ANUnop u (p1 ◯ p2)).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (ANUnop u p1) ◯ p2 ≡ (ANUnop u (p1 ◯ p2)) *)

  Lemma appenv_over_unop u p1 p2:
    (ANUnop u p1) ◯ₑ p2 ≡ₑ (ANUnop u (p1 ◯ₑ p2)).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  Lemma unop_over_either u p₁ p₂ :
    ANUnop u (ANEither p₁ p₂) ≡ₑ ANEither (ANUnop u p₁)(ANUnop u p₂).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    match_destr.
  Qed.

  Lemma unop_over_either_app u p₁ p₂ p₃ :
    ANUnop u (ANEither p₁ p₂ ◯ p₃)  ≡ₑ ANEither (ANUnop u p₁)(ANUnop u p₂) ◯ p₃.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    unfold olift.
    destruct (h ⊢ₑ p₃ @ₑ x ⊣ c; env); simpl; trivial.
    destruct d; simpl; trivial.
  Qed.

  (* (ENV ⊗ p1) ◯ p2 ≡ ENV ⊗ (p1 ◯ p2) *)

  Lemma app_over_merge p1 p2:
    (ANEnv ⊗ p1) ◯ p2 ≡ₑ ANEnv ⊗ (p1 ◯ p2).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* (ANBinop b p2 (ANConst d) ◯ p1) ≡ (ANBinop b (p2 ◯ p1) (ANConst d)) *)
  
  Lemma app_over_binop_l b d p1 p2:
    (ANBinop b p2 (ANConst d) ◯ p1)
      ≡ₑ (ANBinop b (p2 ◯ p1) (ANConst d)).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.
 
  (* (ANBinop b p1 p2 ◯ (p3 ⊕ p4)) ≡ (ANBinop b (p1 ◯ (p3 ⊕ p4)) (p2 ◯ (p3 ⊕ p4))) *)
  
  Lemma app_concat_over_binop b p1 p2 p3 p4:
    (ANBinop b p1 p2 ◯ (p3 ⊕ p4) )
      ≡ₑ (ANBinop b (p1 ◯ (p3 ⊕ p4)) (p2 ◯ (p3 ⊕ p4))).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    destruct (h ⊢ₑ p3 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct (h ⊢ₑ p4 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct d0; reflexivity.
  Qed.

  (* (ANBinop b p2 (ANConst d) ◯ p1) ≡ (ANBinop b (p2 ◯ p1) (ANConst d)) *)
  
  Lemma app_over_binop_env b p1 p2 s:
    (ANBinop b p1 p2 ◯ (ANUnop (ADot s) ANEnv))
      ≡ₑ (ANBinop b (p1 ◯ (ANUnop (ADot s) ANEnv)) (p2 ◯ (ANUnop (ADot s) ANEnv))).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    destruct env; try reflexivity; simpl.
    destruct (edot l s); reflexivity.
  Qed.

  (* σ⟨ p1 ⟩( p2 ) ◯ p0 ≡ σ⟨ p1 ⟩( p2 ◯ p0 ) *)
  
  Lemma app_over_select p0 p1 p2:
    σ⟨ p1 ⟩( p2 ) ◯ p0 ≡ₑ σ⟨ p1 ⟩( p2 ◯ p0 ).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    

  (* χ⟨ p1 ⟩( p2 ) ◯ p0 ≡ χ⟨ p1 ⟩( p2 ◯ p0 ) *)
  
  Lemma app_over_map p0 p1 p2:
    χ⟨ p1 ⟩( p2 ) ◯ p0 ≡ₑ χ⟨ p1 ⟩( p2 ◯ p0 ).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    
  
  (* ⋈ᵈ⟨ p1 ⟩( p2 ) ◯ p0 ≡ ⋈ᵈ⟨ p1 ⟩( p2 ◯ p0 ) *)
  
  Lemma app_over_mapconcat p0 p1 p2:
    ⋈ᵈ⟨ p1 ⟩( p2 ) ◯ p0 ≡ₑ ⋈ᵈ⟨ p1 ⟩( p2 ◯ p0 ).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    
  
  (* (p1 × p2) ◯ p0 ≡ (p1  ◯ p0) × (p2 ◯ p0) *)
  
  Lemma app_over_product p0 p1 p2:
    (p1 × p2) ◯ p0 ≡ₑ (p1  ◯ p0) × (p2 ◯ p0).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    
  
  (* χ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ χ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)
  
  Lemma appenv_over_map p0 p1 p2:
    cnraenv_ignores_id p0 ->
    χ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ₑ χ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ).
  Proof.
    unfold alg_eq, cnraenv_eq; intros ? ? ? _ ? _ ? _; simpl.
    case_eq (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros; try reflexivity; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;d); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    rewrite (cnraenv_ignores_id_swap p0 H h c env a x).
    rewrite H0; simpl.
    destruct (h ⊢ₑ p1 @ₑ a ⊣ c;d); try reflexivity; simpl.
    f_equal; unfold lift in *; simpl in *.
    destruct (rmap (cnraenv_eval h c p1 d) l);
      destruct (rmap
            (fun x0 : data =>
             olift (fun env' : data => h ⊢ₑ p1 @ₑ x0 ⊣ c;env') (h ⊢ₑ p0 @ₑ x0 ⊣ c;env)) l); congruence.
  Qed.    

  (* σ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ σ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)
  
  Lemma appenv_over_select p0 p1 p2:
    cnraenv_ignores_id p0 ->
    σ⟨ p1 ⟩( p2 ) ◯ₑ p0 ≡ₑ σ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ).
  Proof.
    unfold alg_eq, cnraenv_eq; intros ? ? ? _ ? _ ? _; simpl.
    case_eq (h ⊢ₑ p0 @ₑ x ⊣ c;env); intros; try reflexivity; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;d); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    rewrite (cnraenv_ignores_id_swap p0 H h c env a x).
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
    ANAppEnv (ANMapEnv (ANUnop AColl ANEnv)) (ANUnop AFlatten p) ≡ₑ (ANMap (ANUnop AColl ANID) (ANUnop AFlatten p)).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

   (* (χᵉ⟨ { { ENV } } ⟩ ◯ₑ ♯flatten(p)) ≡ χ⟨ { { ID } } ⟩(♯flatten(p)) *)

  Lemma appenv_over_mapenv_coll p:
    ANAppEnv (ANMapEnv (ANUnop AColl (ANUnop AColl ANEnv))) (ANUnop AFlatten p) ≡ₑ (ANMap (ANUnop AColl (ANUnop AColl ANID)) (ANUnop AFlatten p)).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    generalize (h ⊢ₑ p @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.    

  (* χᵉ⟨ { ENV.e } ⟩ ◯ₑ (ENV ⊗ ID) ≡ χ⟨ { ID.e } ⟩(ENV ⊗ ID) *)
  
  Lemma appenv_over_mapenv_merge s:
    ANAppEnv (ANMapEnv (ANUnop AColl ((ENV) · s))) (ENV ⊗ ID)
             ≡ₑ ANMap (ANUnop AColl ((ID) · s)) (ENV ⊗ ID).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    destruct x; reflexivity.
  Qed.

  (* cnraenv_ignores_env p1 -> (ENV ⊗ p1) ◯ₑ p2 ≡ p2 ⊗ p1 *)
  
  Lemma appenv_over_env_merge_l p1 p2:
    cnraenv_ignores_env p1 ->
    ANAppEnv (ENV ⊗ p1) p2 ≡ₑ p2 ⊗ p1.
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity; simpl.
    rewrite (cnraenv_ignores_env_swap p1 H h c d env x).
    destruct (h ⊢ₑ p1 @ₑ x ⊣ c;env); reflexivity.
  Qed.

  (* χᵉ⟨ ENV.e ⟩ ◯ₑ (ENV ⊗ ID) ≡ χ⟨ ID.e ⟩(ENV ⊗ ID) *)
  
  Lemma appenv_over_mapenv_merge2 s:
    ANAppEnv (ANMapEnv ((ENV) · s)) (ENV ⊗ ID)
             ≡ₑ ANMap ((ID) · s) (ENV ⊗ ID).
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
    destruct x; reflexivity.
  Qed.    

  (* ENV ◯ₑ p ≡ p *)

  Lemma env_appenv p:
    (ENV) ◯ₑ p ≡ₑ p.
  Proof.
    unfold alg_eq, cnraenv_eq; intros; simpl.
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); generalize(h ⊢ₑ p2 @ₑ x ⊣ c;env); clear p1 p2 x; intros.
    destruct o; try reflexivity; simpl.
    - unfold olift, olift2; simpl.
      destruct o0; try reflexivity; simpl.
      destruct (StringOrder.lt_dec s3 s1); try reflexivity; simpl.
      unfold lift; simpl.
      unfold rmap_concat, oomap_concat; simpl.
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
      unfold rmap_concat, oomap_concat; simpl.
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
      unfold rmap_concat, oomap_concat; simpl.
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
      unfold rmap_concat, oomap_concat; simpl.
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

  (* (ANBinop u ID.a1 ID.a2) ◯ ([ a1 : p1; a2 : p2 ]) ≡ (ANBinop u p1 p2) *)

  Lemma binop_over_rec_pair b p1 p2 a1 a2:
    a1 <> a2 ->
    (ANBinop b ((ID) · a1) ((ID) · a2))
      ◯ (‵[| (a1, p1) |] ⊕ ‵[| (a2, p2) |])
      ≡ₑ (ANBinop b p1 p2).
  Proof.
    unfold alg_eq, cnraenv_eq; intros ? ? ? _ ? _ ? _; simpl.
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
    (‵[| (s1, p1) |] ⊕ ‵[| (s2, ANConst d) |])
      ◯ p2
     ≡ₑ (‵[| (s1, p1 ◯ p2) |] ⊕ ‵[| (s2, ANConst d) |]).
  Proof.
    unfold alg_eq, cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  (* #toString(s) ≡ s *)
  
  Lemma tostring_dstring s:
    (ANUnop AToString (ANConst (dstring s))) ≡ₑ (ANConst (dstring s)).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; reflexivity.
  Qed.

  (* #toString(#toString(p)) ≡ #toString(p) *)
  
  Lemma tostring_tostring p:
    (ANUnop AToString (ANUnop AToString p)) ≡ₑ (ANUnop AToString p).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); reflexivity.
  Qed.

  (* This one should be generalized based on types
      (ENV ◯ (ENV.a)).a ≡ₑ ENV.a
   *)
  
  Lemma app_over_env_dot s:
    (ENV ◯ (ENV) · s) · s ≡ₑ (ENV) · s.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct env; try reflexivity; simpl.
    case_eq (RRelation.edot l s); intros; try reflexivity; assumption.
  Qed.

  Lemma app_over_appenv p1 p2 p3:
    cnraenv_ignores_id p3 ->
    ((p3 ◯ₑ p2) ◯ p1) ≡ₑ p3 ◯ₑ (p2 ◯ p1).
  Proof.
    unfold cnraenv_eq; intros ? ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    generalize (h ⊢ₑ p2 @ₑ d ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    apply cnraenv_ignores_id_swap; assumption.
  Qed.

  Lemma appenv_over_app_ie p1 p2 p3:
    cnraenv_ignores_env p3 ->
    ((p3 ◯ p2) ◯ₑ p1) ≡ₑ p3 ◯ (p2 ◯ₑ p1).
  Proof.
    unfold cnraenv_eq; intros ? ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p1 @ₑ x ⊣ c;env); intros.
    destruct o; try reflexivity; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;d); simpl; trivial.
    apply cnraenv_ignores_env_swap; assumption.
  Qed.

  Lemma app_over_appenv_over_mapenv p1 p2:
    (((ANMapEnv (‵{|ENV|})) ◯ₑ p1) ◯ p2) ≡ₑ
    (((ANMapEnv (‵{|ENV|})) ◯ₑ (p1 ◯ p2) )).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    generalize (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros.
    destruct o; reflexivity.
  Qed.

  Lemma map_full_over_select_id p0 p1 p2:
    χ⟨ p0 ⟩(σ⟨ p1 ⟩(‵{| p2 |})) ≡ₑ χ⟨ p0 ◯ p2 ⟩(σ⟨ p1 ◯ p2 ⟩(‵{| ID |})).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    case_eq (h ⊢ₑ p2 @ₑ x ⊣ c;env); intros; try reflexivity; simpl.
    destruct (h ⊢ₑ p1 @ₑ d ⊣ c;env); try reflexivity; simpl.
    destruct d0; try reflexivity; simpl.
    case_eq b; intros; try reflexivity; simpl.
    rewrite H; simpl. reflexivity.
  Qed.

  Lemma compose_selects_in_mapenv p1 p2 :
    (♯flatten(ANMapEnv (χ⟨ENV⟩(σ⟨p1⟩( ‵{| ID |}))))) ◯ₑ (χ⟨ENV⟩(σ⟨p2⟩( ‵{| ID |})))
            ≡ₑ (χ⟨ENV⟩(σ⟨p1⟩(σ⟨p2⟩( ‵{| ID |})))).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); reflexivity.
  Qed.

  Lemma appenv_through_either q₁ q₂ q₃:
    cnraenv_ignores_id q₃ ->
    ANEither q₁ q₂ ◯ₑ q₃ ≡ₑ ANEither (q₁ ◯ₑ q₃) (q₂ ◯ₑ q₃).
  Proof.
    intros.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    unfold olift.
    generalize (cnraenv_ignores_id_swap q₃ H h c env x); intros eqq.
    destruct (h ⊢ₑ q₃ @ₑ x ⊣ c;env); simpl in * ;
    destruct x; simpl; trivial;
    specialize (eqq x); rewrite <- eqq; trivial.
  Qed.


  (* ♯flatten(χᵉ⟨{ p1 }⟩) ≡ χᵉ⟨ p1 ⟩ *)
  
  Lemma flatten_mapenv_coll p1:
    ♯flatten(ANMapEnv (‵{| p1 |})) ≡ₑ ANMapEnv p1.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct env; try reflexivity; simpl.
    autorewrite with alg.
    induction l; try reflexivity; simpl in *.
    destruct (h ⊢ₑ p1 @ₑ x ⊣ c;a); try reflexivity; simpl.
    apply f_equal.
    revert IHl.
    destruct ((rmap (fun env' : data => h ⊢ₑ p1 @ₑ x ⊣ c;env') l));
      destruct ((rmap
                   (fun env' : data =>
                      olift (fun d1 : data => Some (dcoll (d1 :: nil)))
                            (h ⊢ₑ p1 @ₑ x ⊣ c;env')) l)); intros; simpl in *; try congruence.
    rewrite (rflatten_cons (d::nil) l1 l0).
    auto.
    destruct (rflatten l1); simpl in *; congruence.
    unfold lift in *.
    case_eq (rflatten l0); intros; simpl in *; try (rewrite H in *; congruence).
    unfold rflatten in *; simpl.
    rewrite H.
    reflexivity.
  Qed.

  Lemma flip_env1 p :
    χ⟨ENV⟩(σ⟨ p ⟩(‵{|ID|})) ◯ₑ ID ≡ₑ (σ⟨ p ⟩(‵{|ID|})) ◯ₑ ID.
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;x); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct b; reflexivity.
  Qed.

  Lemma flip_env2 p :
    (σ⟨ p ⟩(‵{|ID|}) ◯ₑ ID) ≡ₑ σ⟨ p ◯ₑ ID ⟩(‵{|ID|}).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;x); reflexivity.
  Qed.

  Lemma flip_env3 b p1 p2 :
     (ANBinop b p1 p2) ◯ₑ ID ≡ₑ (ANBinop b (p1 ◯ₑ ID) (p2 ◯ₑ ID)).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; reflexivity.
  Qed.

  Lemma flip_env4 p1 p2 s :
     (ANUnop (ADot s) p1) ◯ₑ p2 ≡ₑ (ANUnop (ADot s) (p1 ◯ₑ p2)).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); reflexivity.
  Qed.

  Lemma flip_env5 p1 p2:
    ♯flatten(χ⟨σ⟨p1⟩(‵{|ID|})⟩(p2)) ≡ₑ σ⟨p1⟩(p2).
  Proof.
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    autorewrite with alg.
    induction l; try reflexivity; simpl.
    destruct (h ⊢ₑ p1 @ₑ a ⊣ c;env); try reflexivity; simpl.
    f_equal.
    destruct d; try reflexivity; simpl.
    destruct b; try reflexivity; simpl.
    - destruct ((rmap
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
      rewrite rflatten_cons with (r' := l1).
      simpl.
      reflexivity.
      unfold lift in IHl.
      destruct (rflatten l0); try congruence.
      unfold lift in IHl.
      unfold rflatten in *; simpl in *.
      destruct (oflat_map
            (fun x0 : data =>
             match x0 with
             | dcoll y => Some y
             | _ => None
             end) l0); try congruence; try reflexivity.
      congruence.
      reflexivity.
    - destruct ((rmap
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
      rewrite rflatten_cons with (r' := l1).
      reflexivity.
      unfold lift in *.
      destruct (rflatten l0); simpl in *.
      inversion IHl; reflexivity.
      congruence.
      unfold rflatten in *; simpl in *.
      destruct ((oflat_map
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
    cnraenv_ignores_id p1 ->
    (ANMapEnv (‵{| p1 |})) ◯ₑ p2 ≡ₑ χ⟨‵{| p1 ◯ₑ ID |}⟩(p2).
  Proof.
    unfold cnraenv_eq; intros ? ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p2 @ₑ x ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    rewrite (cnraenv_ignores_id_swap p1 H h c a x a).
    destruct (h ⊢ₑ p1 @ₑ a ⊣ c;a); try reflexivity; simpl.
    destruct ((rmap
             (fun env' : data =>
              olift (fun d1 : data => Some (dcoll (d1 :: nil)))
                    (h ⊢ₑ p1 @ₑ x ⊣ c;env')) l));
      destruct ((rmap
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
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
    unfold cnraenv_eq; intros ? ? _ ? _ ? _; simpl.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); try reflexivity; simpl.
    unfold edot; simpl.
    destruct (string_eqdec s s); congruence.
  Qed.

  (* optimizations for Either *)
  Lemma either_app_over_dleft p₁ p₂ d :
    (ANEither p₁ p₂) ◯ (ANConst (dleft d)) ≡ₑ p₁ ◯ (ANConst d).
  Proof.
    red; simpl; intros; reflexivity.
  Qed.

  Lemma either_app_over_dright p₁ p₂ d :
    (ANEither p₁ p₂) ◯ (ANConst (dright d)) ≡ₑ p₂ ◯ (ANConst d).
  Proof.
    red; simpl; intros; reflexivity.
  Qed.

  Lemma either_app_over_aleft p₁ p₂ p :
    (ANEither p₁ p₂) ◯ (ANUnop ALeft p) ≡ₑ p₁ ◯ p.
  Proof.
    red; simpl; intros.
    unfold olift.
    destruct (h ⊢ₑ p @ₑ x ⊣ c;env); trivial.
  Qed.
  
  Lemma either_app_over_aright p₁ p₂ p :
    (ANEither p₁ p₂) ◯ (ANUnop ARight p) ≡ₑ p₂ ◯ p.
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
    π[sl](ANConst (drec l)) ≡ₑ ANConst (drec (RRelation.rproject l sl)).
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
    π[sl](ANEither p1 p2) ≡ₑ ANEither (π[sl](p1)) (π[sl](p2)).
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
    destruct (rmap
              (fun x0 : data =>
               match h ⊢ₑ p₂ @ₑ x0 ⊣ c; env with
               | Some x'0 =>
                   lift_oncoll
                     (fun c1 : list data =>
                      match rmap (cnraenv_eval h c p₁ env) c1 with
                      | Some a' => Some (dcoll a')
                      | None => None
                      end) x'0
               | None => None
               end) l);
      destruct (rmap (cnraenv_eval h c p₂ env) l);
      simpl in * .
    - destruct (rmap
            (fun x0 : data =>
             lift_oncoll
               (fun c1 : list data =>
                match rmap (cnraenv_eval h c p₁ env) c1 with
                | Some a' => Some (dcoll a')
                | None => None
                end) x0) l1); try discriminate.
      inversion IHl; clear IHl; subst.
      trivial.
    - discriminate.
    - destruct (rmap
            (fun x0 : data =>
             lift_oncoll
               (fun c1 : list data =>
                match rmap (cnraenv_eval h c p₁ env) c1 with
                | Some a' => Some (dcoll a')
                | None => None
                end) x0) l0); try discriminate.
      trivial.
    - destruct ( lift_oncoll
         (fun c1 : list data =>
          match rmap (cnraenv_eval h c p₁ env) c1 with
          | Some a' => Some (dcoll a')
          | None => None
          end) d); trivial.
  Qed.
  
  (* optimization for distinct *)
  Definition nodupA : cnraenv -> Prop :=
    cnraenv_always_ensures
      (fun d => match d with
                | dcoll dl => NoDup dl
                | _ => False
                end).
  
  Lemma dup_elim (q:cnraenv) :
    nodupA q -> ANUnop ADistinct q  ≡ₑ  q.
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
    would actually be done on input data. ANID means that either it is ANID     or none such can be found.  We don't bother trying to unify the 
    continuation of binops or ANEIther
    since that would be done separately anyway *)
  (** returns: (last part of the computation, rest of it) *)
  Fixpoint cnraenv_split_last (e:cnraenv) : (cnraenv*cnraenv)
    := match e with
         | ANID => (ANID,ANID)
         | ANConst c =>  (ANID,ANConst c)
         | ANBinop b e1 e2 => (ANBinop b e1 e2,ANID)
         | ANUnop u e1 =>
           match cnraenv_split_last e1 with
             | (ANID, r) => (ANUnop u r, ANID)
             | (e1last, e1rest) => (e1last, ANUnop u e1rest)
           end
         | ANMap e1 e2 =>
           match cnraenv_split_last e2 with
             | (ANID, r) => (ANMap e1 e2, ANID)
             | (e2last, e2rest) => (e2last, ANMap e1 e2rest)
           end
         | ANMapConcat e1 e2 =>
           match cnraenv_split_last e2 with
             | (ANID, r) => (ANMapConcat e1 e2, ANID)
             | (e2last, e2rest) => (e2last, ANMapConcat e1 e2rest)
           end
         | ANProduct e1 e2 => (ANProduct e1 e2,ANID)
         | ANSelect e1 e2 =>
           match cnraenv_split_last e2 with
             | (ANID, r) => (ANSelect e1 e2, ANID)
             | (e2last, e2rest) => (e2last, ANSelect e1 e2rest)
           end         
         | ANDefault e1 e2 => (ANDefault e1 e2,ANID)
         | ANEither l r => (ANEither l r, ANID)
         | ANEitherConcat l r =>
           (ANEitherConcat l r, ANID)
         | ANApp e1 e2 =>
           match cnraenv_split_last e2 with
             | (ANID, r) => (e1, r)
             | (e2last, e2rest) => (e2last, ANApp e1 e2rest)
           end         
         | ANGetConstant s => (ANID,ANGetConstant s)
         | ANEnv => (ANID,ANEnv)
         | ANAppEnv e1 e2 => (ANAppEnv e1 e2, ANID)
         | ANMapEnv e => (ANMapEnv e, ANID)
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

Hint Rewrite @envflatten_map_coll : cnraenv_optim.
Hint Rewrite @envmap_into_id : cnraenv_optim.
Hint Rewrite @envmap_into_id_flatten : cnraenv_optim.

(*
       -- Those introduce a ◯ , but remove a χ
       envmap_map_compose : χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ≡ χ⟨ P1 ◯ P2 ⟩( P3 )
       envmap_singleton : χ⟨ P1 ⟩( { P2 } ) ≡ { P1 ◯ P2 }
*)

Hint Rewrite @envmap_map_compose : cnraenv_optim.
Hint Rewrite @envmap_singleton : cnraenv_optim.

(*
       -- Those remove over flatten
    ** envflatten_coll_mergeconcat: ♯flatten( { ANBinop AMergeConcat p1 p2 } ) ≡ (ANBinop AMergeConcat p1 p2)
    ** envflatten_coll_map : ♯flatten( { χ⟨ p1 ⟩( p2 ) } ) ≡ χ⟨ p1 ⟩( p2 )
    ** envflatten_coll_flatten : ♯flatten({ ♯flatten( p ) }) ≡ ♯flatten( p )
    ** envflatten_coll_coll : ♯flatten({ { p } }) ≡ ♯flatten( p )
    Generalized into: tenvflatten_coll
*)

Hint Rewrite @envflatten_coll_mergeconcat : cnraenv_optim.
Hint Rewrite @envflatten_coll_map : cnraenv_optim.
Hint Rewrite @envflatten_coll_flatten : cnraenv_optim.
Hint Rewrite @envflatten_coll_coll : cnraenv_optim.

(*
       -- Those push-down or remove ◯
       app_over_id : p ◯ ID ≡ p
       app_over_id_l : ID ◯ p ≡ p
       app_over_app : o(p1 ◯ p2) ◯ p3 ≡ p1 ◯ (p2 ◯ p3)
       app_over_map : χ⟨ p1 ⟩( p2 ) ◯ p0 ≡ χ⟨ p1 ⟩( p2 ◯ p0 )
       app_over_select : σ⟨ p1 ⟩( p2 ) ◯ p0 ≡ σ⟨ p1 ⟩( p2 ◯ p0 )
       app_over_unop : (ANUnop u p1) ◯ p2 ≡ₑ (ANUnop u (p1 ◯ p2))
       app_over_binop_l : (ANBinop b p2 (ANConst d) ◯ p1) ≡ (ANBinop b (p2 ◯ p1) (ANConst d))
       app_over_merge : (ENV ⊗ p1) ◯ p2 ≡ₑ ENV ⊗ (p1 ◯ p2)
       app_over_rec : [ a : P1 ] ◯ P2 ≡ [ a : P1 ◯ P2 ]
       binop_over_rec_pair : (ANBinop b ID.a1 ID.a2) ◯ ([ a1 : p1; a2 : p2 ]) ≡ ANBinop b p1 p2
       concat_id_left : ([ a1 : p1; a2 : d ]) ◯ p2 ≡ [ a1 : p1 ◯ p2; a2 : d ]
       app_over_env_dot : (ENV ◯ (ENV.a)).a ≡ₑ ENV.a
       app_over_appenv_over_mapenv :
             ((χᵉ⟨‵{|ENV|} ⟩( ID)) ◯ₑ (χ⟨ENV ⟩( σ⟨p1 ⟩( ‵{|ID|})))) ◯ p2
          ≡ₑ (χᵉ⟨‵{|ENV|} ⟩( ID)) ◯ₑ (χ⟨ENV ⟩( σ⟨p1 ⟩( ‵{|ID|}))) ◯ p2
*)

Hint Rewrite @app_over_id : cnraenv_optim.
Hint Rewrite @app_over_id_l : cnraenv_optim.
Hint Rewrite @app_over_app : cnraenv_optim.           (* Not in ROptimEnvFunc *)
Hint Rewrite @app_over_map : cnraenv_optim.
Hint Rewrite @app_over_select : cnraenv_optim.
Hint Rewrite @app_over_unop : cnraenv_optim.
Hint Rewrite @app_over_binop_l : cnraenv_optim.
Hint Rewrite @app_over_merge : cnraenv_optim.
Hint Rewrite @app_over_rec : cnraenv_optim.
Hint Rewrite @binop_over_rec_pair : cnraenv_optim.
Hint Rewrite @concat_id_left : cnraenv_optim.
Hint Rewrite @app_over_env_dot : cnraenv_optim.
Hint Rewrite @app_over_appenv_over_mapenv : cnraenv_optim.

(*
       -- Other misc rewrites
       product_singletons : { [ s1 : p1 ] } × { [ s2 : p2 ] } ≡ { [ s1 : p1; s2 : p2 ] }
       double_flatten_map_coll : ♯flatten(χ⟨ χ⟨ { ID } ⟩( ♯flatten( p1 ) ) ⟩( p2 ))
                                 ≡ χ⟨ { ID } ⟩(♯flatten(χ⟨ ♯flatten( p1 ) ⟩( p2 )))
*)

Hint Rewrite @product_singletons : cnraenv_optim.
Hint Rewrite @double_flatten_map_coll : cnraenv_optim.
Hint Rewrite @tostring_dstring : cnraenv_optim.
Hint Rewrite @tostring_tostring : cnraenv_optim.

(*
       -- Those handle operators on the environment
       appenv_over_mapenv : χᵉ⟨ { ENV } ⟩(ID) ◯ₑ ♯flatten(p) ≡ χ⟨ { ID } ⟩(♯flatten(p))
       appenv_over_mapenv_coll : (χᵉ⟨ { { ENV } } ⟩(ID) ◯ₑ ♯flatten(p)) ≡ χ⟨ { { ID } } ⟩(♯flatten(p))
       appenv_over_mapenv_merge : (χᵉ⟨ { ENV.e } ⟩(ID) ◯ₑ ANBinop AMergeConcat ENV ID)
                                   ≡ₑ χ⟨ { ID.e } ⟩(ANBinop AMergeConcat ENV ID)
*)

Hint Rewrite @env_appenv : cnraenv_optim.
Hint Rewrite @appenv_over_mapenv : cnraenv_optim.
Hint Rewrite @appenv_over_mapenv_coll : cnraenv_optim.
Hint Rewrite @appenv_over_mapenv_merge : cnraenv_optim.
Hint Rewrite @appenv_over_mapenv_merge2 : cnraenv_optim.
Hint Rewrite @compose_selects_in_mapenv : cnraenv_optim.
Hint Rewrite @flatten_through_appenv : cnraenv_optim.
Hint Rewrite @flatten_mapenv_coll : cnraenv_optim.

(* Simple optimizations for either *)
Hint Rewrite @either_app_over_dleft : cnraenv_optim.
Hint Rewrite @either_app_over_dright : cnraenv_optim.
Hint Rewrite @either_app_over_aleft : cnraenv_optim.
Hint Rewrite @either_app_over_aright : cnraenv_optim.

(* Optimizations for rproject *)
Hint Rewrite @rproject_over_concat : cnraenv_optim.
Hint Rewrite @rproject_over_rec_in : cnraenv_optim. 
Hint Rewrite @rproject_over_rec_nin : cnraenv_optim. 
Hint Rewrite @rproject_over_rproject : cnraenv_optim. 
Hint Rewrite @rproject_over_either  : cnraenv_optim.
  
(* end hide *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
