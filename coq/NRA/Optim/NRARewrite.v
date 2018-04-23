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
Require Import Utils.
Require Import CommonRuntime.
Require Import NRA.
Require Import NRAEq.
  
Section NRARewrite.
  Local Open Scope nra_scope.

  Context {fruntime:foreign_runtime}.

  (* Some of algebraic equivalences for NRA *)
  (* Those are valid without type *)

  (* P1 ∧ P2 ≡ P2 ∧ P1 *)

  Lemma and_comm (p1 p2: nra) :
    p2 ∧ p1 ≡ₐ p1 ∧ p2.
  Proof.
    unfold nra_eq; intros; simpl.
    generalize (h ⊢ p1 @ₐ x ⊣ c); generalize (h ⊢ p2 @ₐ x ⊣ c); intros.
    destruct o; destruct o0; try reflexivity.
    unfold unbdbool.
    destruct d; destruct d0; try reflexivity; simpl.
    rewrite Bool.andb_comm; reflexivity.
  Qed.

  (* (P1 ⋃ P2) ⋃ P3 ≡ P1 ⋃ (P2 ⋃ P3) *)

  Lemma union_assoc (p1 p2 p3: nra):
    (p1 ⋃ p2) ⋃ p3 ≡ₐ p1 ⋃ (p2 ⋃ p3).
  Proof.
    unfold nra_eq; intros; simpl.
    generalize (h ⊢ p1 @ₐ x ⊣ c) as d1.
    generalize (h ⊢ p2 @ₐ x ⊣ c) as d2.
    generalize (h ⊢ p3 @ₐ x ⊣ c) as d3.
    intros.
    destruct d1; destruct d2; destruct d3; try reflexivity.
    destruct d; destruct d0; destruct d1; try reflexivity.
    simpl.
    autorewrite with alg.
    rewrite bunion_assoc.
    reflexivity.
    destruct (rondcoll2 bunion d d0); autorewrite with alg; reflexivity.
  Qed.
  
  (* σ⟨ P ⟩(P1 ⋃ P2) ≡ σ⟨ P ⟩(P1) ⋃ σ⟨ P ⟩(P2) *)

  Lemma union_select_distr (p p1 p2: nra) :
    σ⟨ p ⟩(p1 ⋃ p2) ≡ₐ σ⟨ p ⟩(p1) ⋃ σ⟨ p ⟩(p2).
  Proof.
    unfold nra_eq; intros.
    simpl.
    generalize (h ⊢ p1 @ₐ x ⊣ c) as d1.
    generalize (h ⊢ p2 @ₐ x ⊣ c) as d2.
    intros.
    destruct d1; destruct d2; try (autorewrite with alg; reflexivity).
    - destruct d; try reflexivity.
      destruct d0; simpl; try (destruct (lift_filter
         (fun x' : data =>
          match h ⊢ p @ₐ x' ⊣ c with
          | Some (dbool b) => Some b
          | _ => None
          end) l); reflexivity).
      induction l; simpl.
      destruct (lift_filter
         (fun x' : data =>
          match h ⊢ p @ₐ x' ⊣ c with
          | Some (dbool b) => Some b
          | _ => None
          end) l0); reflexivity.
      generalize(h ⊢ p @ₐ a ⊣ c); intros.
      unfold bunion.
      rewrite lift_app_filter.
      destruct o; try reflexivity.
      destruct d; try reflexivity.
      revert IHl.
      generalize ((lift_filter
            (fun x' : data =>
             match h ⊢ p @ₐ x' ⊣ c with
             | Some (dbool b0) => Some b0
             | _ => None
             end) l)).
      generalize (lift_filter
             (fun x' : data =>
              match h ⊢ p @ₐ x' ⊣ c with
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

  Lemma map_singleton (p1 p2:nra) :
    χ⟨ p1 ⟩( ‵{| p2 |} ) ≡ₐ ‵{| p1 ◯ p2 |}.
  Proof.
    unfold nra_eq; intros; simpl.
    generalize (h ⊢ p2 @ₐ x ⊣ c); intros.
    destruct o; try reflexivity; simpl.
    generalize (h ⊢ p1 @ₐ d ⊣ c); intros; simpl.
    destruct o; reflexivity.
  Qed.

  (* [ a : ID ] ◯ P ≡ [ a : P ] *)

  Lemma compose_rec_id s p:
    ‵[| (s, ID) |] ◯ p ≡ₐ ‵[| (s, p) |].
  Proof.
    unfold nra_eq; intros; simpl.
    generalize (h ⊢ p @ₐ x ⊣ c); intros.
    destruct o; reflexivity.
  Qed.

  Lemma flatten_map_coll p1 p2 :
    ♯flatten(χ⟨ ‵{| p1 |} ⟩( p2 )) ≡ₐ χ⟨ p1 ⟩( p2 ).
  Proof.
    unfold nra_eq; intros h c _ x _; simpl.
    generalize (h ⊢ p2 @ₐ x ⊣ c); clear x p2; intros.
    destruct o; try reflexivity.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    generalize (h ⊢ p1 @ₐ a ⊣ c); clear a; intros; simpl.
    destruct o; try reflexivity; simpl.
    unfold olift in *.
    revert IHl.
    generalize (lift_map
             (fun x : data =>
              match h ⊢ p1 @ₐ x ⊣ c with
              | Some x' => Some (dcoll (x' :: nil))
              | None => None
              end) l); generalize (lift_map (nra_eval h c p1) l); intros.
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

  (* [ a1 : p1; a2 : p1 ].a2 ≡ₐ p1 *)

  Lemma dot_from_duplicate_r s1 s2 p1 :
    (‵[| (s1, p1) |] ⊕ ‵[| (s2, p1) |])·s2 ≡ₐ p1.
  Proof.
    unfold nra_eq; intros ? ? _ x _; simpl.
    generalize (h ⊢ p1 @ₐ x ⊣ c); clear p1 x; intros.
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

  (* [ a1 : p1; a2 : p1 ].a1 ≡ₐ p1 *)

  Lemma dot_from_duplicate_l s1 s2 p1 :
    (‵[| (s1, p1) |] ⊕ ‵[| (s2, p1) |])·s1 ≡ₐ p1.
  Proof.
    unfold nra_eq; intros ? ? _ x _; simpl.
    generalize (h ⊢ p1 @ₐ x ⊣ c); clear p1 x; intros.
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

  (* χ⟨ { ID } ⟩( P ) ≡ { { P } }*)
  
  Lemma map_into_singleton p :
    χ⟨ ‵{| ID |} ⟩(‵{| p |}) ≡ₐ ‵{|‵{| p |}|}.
  Proof.
    unfold nra_eq; intros ? ? _ x _; simpl.
    generalize (h ⊢ p @ₐ x ⊣ c); clear x p; intros.
    destruct o; reflexivity.
  Qed.

  (* ♯flatten( χ⟨ { { P1 } } ⟩( P2 ) ) ≡ χ⟨ { P1 } ⟩( P2 ) *)
  
  Lemma flatten_over_map_into_singleton p1 p2:
    ♯flatten( χ⟨ ‵{|‵{| p1 |}|} ⟩( p2 ) ) ≡ₐ χ⟨ ‵{| p1 |} ⟩( p2 ).
  Proof.
    unfold nra_eq; intros ? ? _ ? _; simpl.
    generalize (h ⊢ p2 @ₐ x ⊣ c); clear p2 x; intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    induction l; try reflexivity; simpl.
    unfold olift, lift in *; simpl.
    generalize (h ⊢ p1 @ₐ a ⊣ c); clear a; intros; simpl.
    destruct o; try reflexivity; simpl.
    revert IHl.
    generalize (lift_map
              (fun x : data =>
               match
                 match h ⊢ p1 @ₐ x ⊣ c with
                 | Some x' => Some (dcoll (x'::nil))
                 | None => None
                 end
               with
               | Some x' => Some (dcoll (x'::nil))
               | None => None
               end) l);
    generalize (lift_map
            (fun x : data =>
             match h ⊢ p1 @ₐ x ⊣ c with
             | Some x' => Some (dcoll (x'::nil))
             | None => None
             end) l); intros.
    destruct o; destruct o0; try reflexivity; simpl; unfold lift_oncoll in *; simpl; try congruence.
    - unfold oflatten in *; simpl in *.
      revert IHl; generalize (lift_flat_map
                                (fun x : data =>
                                   match x with
                                     | dcoll y => Some y
                                     | _ => None
                                   end) l1); intros.
      destruct o; try reflexivity; simpl.
      inversion IHl; reflexivity.
      congruence.
    - unfold oflatten in *; simpl.
      revert IHl; generalize (lift_flat_map
                                (fun x : data =>
                                   match x with
                                     | dcoll y => Some y
                                     | _ => None
                                   end) l0); intros.
      destruct o; try reflexivity; simpl.
      congruence.
  Qed.
  
  (*****************)
  (* Rules Section *)
  (*****************)
  
  (* Composite/specialized rewrites, useful for rules optimization *)
  
  Lemma map_singleton_rec s1 s2 :
    χ⟨‵[| (s1, ID) |] ⟩( ‵{|(ID) · s2 |}) ≡ₐ ‵{|‵[| (s1, (ID) · s2) |] |}.
  Proof.
    apply map_singleton.
  Qed.

  (* χ⟨ ID.a ⟩( { P } ) ≡ { P.a } *)
  
  Lemma map_dot_singleton s p :
    χ⟨ (ID)·s ⟩( ‵{| p |} ) ≡ₐ ‵{| p·s |}.
  Proof.
    apply map_singleton.
  Qed.

  (*
     a1, a2, a3 are distinct field names
     ============================================================================
     χ⟨ ¬π[a1](ID) ⟩ ( ⋈ᵈ⟨ χ⟨ [ a2 : ID ] ⟩(ID.a1) ⟩( { [ a3 : p1; a1: { p2 } ] } )
     ≡ { [ (a3 : p1; a2 : p2 ] } *)
  
  Lemma unnest_singleton s1 s2 s3 p1 p2 :
    s1 <> s2 /\ s2 <> s3 /\ s3 <> s1 ->
    χ⟨ ¬π[s1](ID) ⟩(
       ⋈ᵈ⟨ χ⟨ ‵[| (s2,ID) |] ⟩((ID)·s1) ⟩( ‵{|‵[| (s3,p1) |] ⊕ ‵[| (s1,‵{| p2 |}) |]|} )
     )
     ≡ₐ ‵{|‵[| (s3, p1) |] ⊕ ‵[| (s2, p2) |]|}.
  Proof.
    intros.
    elim H; clear H; intros.
    elim H0; clear H0; intros.
    unfold nra_eq; intros ? ? _ ? _; simpl.
    generalize (h ⊢ p1 @ₐ x ⊣ c); generalize(h ⊢ p2 @ₐ x ⊣ c); clear p1 p2 x; intros.
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

  (* χ⟨ [ PBIND : ID.PBIND; PDATA : ID.PDATA.WORLD ].PDATA ⟩({ p })
     ≡ { [ PBIND : p.PBIND; PDATA: p.PDATA.WORLD ].PDATA } *)
  
  Lemma substitute_in_bindings (p:nra) :
    χ⟨ (‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PDATA"·"WORLD") |])·"PDATA" ⟩( ‵{| p |} )
     ≡ₐ ‵{|(‵[| ("PBIND", p·"PBIND") |] ⊕ ‵[| ("PDATA", p·"PDATA"·"WORLD") |])·"PDATA" |}.
  Proof.
    unfold nra_eq, olift; intros ? ? _ ? _; simpl.
    generalize (h ⊢ p @ₐ x ⊣ c); simpl; intros; clear p x.
    destruct o; try reflexivity.
    destruct d; try reflexivity.
    unfold olift, lift; simpl.
    generalize (edot l "PBIND"); generalize (edot l "PDATA"); intros; clear l; simpl.
    destruct o; destruct o0; try reflexivity; simpl.
    generalize (match
                   match d with
                     | drec r => edot r "WORLD"
                     | _ => None
                   end
                 with
                   | Some x' => Some (drec (("PDATA"%string, x') :: nil))
        | None => None
        end
               ); intros; simpl.
    destruct (         match o with
         | Some (drec r2) =>
             Some
               (drec
                  (SortingAdd.insertion_sort_insert rec_field_lt_dec 
                     ("PBIND"%string, d0) (rec_sort r2)))
         | _ => None
         end
             ); intros; simpl.
    destruct d1; try reflexivity.
    generalize (edot l "PDATA"); clear l; intros.
    destruct o0; try reflexivity; simpl.
    reflexivity.
  Qed.

  (* [ PBIND : ID.PBIND; PDATA : ID.PBIND ].PDATA ≡ₐ ID.PBIND *)

  Lemma dot_from_duplicate_bind_r :
    (‵[| ("PBIND", (NRAUnop (OpDot "PBIND") NRAID)) |] ⊕ ‵[| ("PDATA", (NRAUnop (OpDot "PBIND") NRAID)) |])·"PDATA" ≡ₐ (NRAUnop (OpDot "PBIND") NRAID).
  Proof.
    rewrite (dot_from_duplicate_r "PBIND" "PDATA" (NRAUnop (OpDot "PBIND") NRAID)).
    reflexivity.
  Qed.

  (* [ PBIND : ID.PBIND; PDATA : ID.PBIND ].PBIND ≡ₐ ID.PBIND *)

  Lemma dot_from_duplicate_bind_l :
    (‵[| ("PBIND", (NRAUnop (OpDot "PBIND") NRAID)) |] ⊕ ‵[| ("PDATA", (NRAUnop (OpDot "PBIND") NRAID)) |])·"PBIND" ≡ₐ (NRAUnop (OpDot "PBIND") NRAID).
  Proof.
    rewrite (dot_from_duplicate_l "PBIND" "PDATA" (NRAUnop (OpDot "PBIND") NRAID)).
    reflexivity.
  Qed.

  (* [ PBIND : ID·PBIND; PDATA : ID·PBIND·WORLD ]·PDATA ≡ ID·PBIND·WORLD *)
  
  Lemma dot_dot_from_duplicate_bind :
    (‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PBIND"·"WORLD") |])·"PDATA"
     ≡ₐ ID·"PBIND"·"WORLD".
  Proof.
    unfold nra_eq; intros ? ? _ ? _; simpl.
    destruct x; try reflexivity; simpl.
    generalize (edot l "PBIND"); clear l; intros.
    destruct o; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    generalize (edot l "WORLD"); intros; simpl.
    destruct o; reflexivity.
  Qed.

  (*   [ PBIND : ID.PBIND;
         a1 : χ⟨ [ PBIND : ID.PBIND; PDATA : ID.PDATA.e ].PDATA ⟩ (
                 { [ PBIND : ID.PBIND; PDATA : ID.PBIND ] }
                 ) ]
     ≡ₐ [ PBIND : ID.PBIND; a1 : { ID.PBIND.e } ].
   *)

  Lemma big_nested_bind_simplify_one :
    ‵[| ("PBIND", ID·"PBIND") |]
     ⊕ ‵[| ("a1",
            χ⟨(‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID·"PDATA"·"e") |])·"PDATA"
             ⟩( ‵{|‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("PDATA", ID· "PBIND") |] |}))|]
     ≡ₐ ‵[| ("PBIND", ID·"PBIND") |] ⊕ ‵[| ("a1", ‵{| ID·"PBIND"·"e" |}) |].
  Proof.
    unfold nra_eq; intros ? ? _; simpl.
    destruct x; try reflexivity; simpl.
    generalize (edot l "PBIND"); intros.
    destruct o; try reflexivity; simpl.
    unfold olift2, olift; simpl.
    destruct d; try reflexivity; simpl.
    generalize (edot l0 "e"); intros.
    destruct o; try reflexivity; simpl.
  Qed.
  
End NRARewrite.

