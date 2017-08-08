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

Section TNNRC.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Program.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import BasicSystem.
  Require Import cNNRC.
  Require Import NNRC.
  Require Import TcNNRC.

  (** Typing rules for NNRC *)
  Section typ.
    Context {m:basic_model}.
    Context (τconstants:tbindings).

    Definition nnrc_ext_type (env:tbindings) (n:nnrc) (t:rtype) : Prop :=
      nnrc_type τconstants env (nnrc_ext_to_nnrc n) t.
  End typ.
  
  (** Main lemma for the type correctness of NNNRC *)

  Theorem typed_nnrc_ext_yields_typed_data {m:basic_model} {τcenv} {τ} (cenv env:bindings) (tenv:tbindings) (e:nnrc) :
    bindings_type cenv τcenv ->
    bindings_type env tenv ->
    nnrc_ext_type τcenv tenv e τ ->
    (exists x, (@nnrc_ext_eval _ brand_relation_brands cenv env e) = Some x /\ (data_type x τ)).
  Proof.
    intros.
    unfold nnrc_ext_eval.
    unfold nnrc_ext_type in H1.
    apply (@typed_nnrc_yields_typed_data _ τcenv _ cenv env tenv).
    assumption.
    assumption.
    assumption.
  Qed.

  (* we are only sensitive to the environment up to lookup *)
  Global Instance nnrc_ext_type_lookup_equiv_prop {m:basic_model} :
    Proper (eq ==> lookup_equiv ==> eq ==> eq ==> iff) nnrc_ext_type.
  Proof.
    generalize nnrc_type_lookup_equiv_prop; intro Hnnrc_prop.
    unfold Proper, respectful, lookup_equiv, iff, impl in *; intros; subst.
    apply Hnnrc_prop; try reflexivity;
      try assumption.
  Qed.

End TNNRC.

Ltac nnrc_ext_inverter :=
  unfold nnrc_ext_type, nnrc_ext_to_nnrc in *; simpl in *; try nnrc_inverter.

Ltac nnrc_ext_input_well_typed :=
  repeat progress
         match goal with
         | [HO:nnrc_ext_type ?Γc ?Γ ?op ?τout,
               HE:bindings_type ?env ?Γ
            |- context [(nnrc_ext_eval brand_relation_brands ?cenv ?env ?op)]] =>
           let xout := fresh "dout" in
           let xtype := fresh "τout" in
           let xeval := fresh "eout" in
           destruct (typed_nnrc_ext_yields_typed_data env Γ op HE HO)
             as [xout [xeval xtype]]; rewrite xeval in *; simpl
         end.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
