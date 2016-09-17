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

Require Import ZArith.
Local Open Scope Z_scope.
Require Import String.
Local Open Scope string.
Require Import List.
Import ListNotations.

Require Import BasicSystem CAMPRuntime.
Require Import TrivialModel.

Require Compiler CompDriver CompilerRuntime.

Definition CPRModel := ("MainEntity", "Entity") :: nil.
Instance CPRModel_relation : brand_relation
  := mkBrand_relation CPRModel (eq_refl _) (eq_refl _).

Module TR := TrivialRuntime.
Module CD := CompDriver.CompDriver(TR).

(* This module encodes the examples in sample-rules.txt *)
Section CompilerUntypedTest.

  Local Open Scope rule_scope.
  Local Open Scope string.

  
  (* This was copy/pastes from sample-rules (with [] added in at the top level *)
  Definition makeMainEntity (db:Z) (id:string) (i:Z) 
    := class (singleton "MainEntity")
             (drec [("doubleAttribute",dconst db);
                     ("intAttribute", dconst i);
                     ("id",dconst id)
             ]).

  Definition MainEntity (inp:Z*string*Z) 
    := makeMainEntity (fst (fst inp)) (snd (fst inp)) (snd inp).

  Example exampleWM : list data 
    := [makeMainEntity 120 "string1" 1;
         makeMainEntity 50 "string2" 2;
         makeMainEntity 125 "string3" 3;
         makeMainEntity 50 "string4" 4].

  (* Example1: Aggregate, counts customers with age 32 *)

   (*
      rule r1 {
        when {
          total-attribute:
            aggregate {
      	      e:MainEntity(doubleAttribute == 50);
    	    } do { count {e}; }
        } then {
          System.out.println("total-attribute: " + total-attribute);
        }
      }

    rule Example1 {
        when {
          cs: aggregate {
            c:MainEntity( age == 32 );
          }
          do { count {c.name}; }
        }
        then {
          System.out.println("MainEntitys with age 32: " + cs);  
        }
      }

 *)

  Example Example1' :=
    ("total-attribute" IS AGGREGATE
                       (rule_when ("e" INSTANCEOF (singleton "MainEntity") WHERE ("doubleAttribute" !#-> … ≐ ‵50)))
                       DO ACount
                       OVER (withVar "e" …)
                       FLATTEN 0).
  
  Example Example1 := 
        rule_global
          ("total-attribute" IS AGGREGATE
                             (rule_when ("e" INSTANCEOF (singleton "MainEntity") WHERE ("doubleAttribute" !#-> … ≐ ‵50)))
                             DO ACount
                             OVER (withVar "e" …)
                             FLATTEN 0)
          ;; rule_return (‵"MainEntitys with doubleAttribute 50: "
                          +s+ toString (lookup "total-attribute")).


  Example Example1_result := eval_rule nil Example1 exampleWM.
  Example Example1_expected := map dconst
                                   ["MainEntitys with doubleAttribute 50: 2"].

  Definition pat5 : CD.camp := Eval compute in Example1'.
  Definition algopt5 : CD.nraenv := CD.camp_to_nraenv Example1'.
  
  Definition rpat5 : CD.rule := Eval compute in Example1.
  Definition ralgopt5 : CD.nraenv  := CD.rule_to_nraenv_optim Example1.
  Definition rnnrc5 : CD.nnrc := CD.rule_to_nnrc_optim Example1.
  
  Definition inp1 : (list (string*data)) := (("WORLD", dcoll exampleWM)::nil).
  Definition inp2 : data := dunit.

  End CompilerUntypedTest.

  Section CompilerBrandModelTest.
    
    Program Definition MainEntityDataType :=
      Rec Open (("doubleAttribute", Nat) :: ("id", String) :: ("intAttribute", Nat) :: nil) _.

    Program Definition EntityType : rtype
      := Rec Open [] _.

    Definition CPTModelTypes :=
      [("Entity", EntityType);
      ("MainEntity", MainEntityDataType)
      ].

    Definition CPTModel
      := @mkBrand_context _ CPRModel_relation CPTModelTypes (eq_refl _).

    Instance CPModel : brand_model
      := mkBrand_model CPRModel_relation CPTModel (eq_refl _) (eq_refl _).

  End CompilerBrandModelTest.

  Require Import CompilerModel.
  
  Module MyBrandModel <: CompilerBrandModel(TrivialForeignType).
    Definition compiler_brand_model := CPModel.
  End MyBrandModel.
  Module TM := TrivialModel(MyBrandModel).
  
  Section CompilerTypedTest.
    Existing Instance CPModel.
  
    (* Eval compute in (interp Example1' inp1 inp2). *)

    Lemma makeMainEntity_typed db id i:
      (normalize_data brand_relation_brands (makeMainEntity db id i)) ▹ (Brand (singleton "MainEntity")).
    Proof.
      simpl.
      apply (@dtbrand' _ _ _ CPModel).
      - eauto.
      - rewrite (@canon_brands_singleton (@brand_model_relation _ CPModel)).
        rewrite brands_type_singleton. simpl.
        apply (@dtrec_full _ _ _ CPModel).
        apply Forall2_cons; simpl.
        split; [reflexivity|constructor].
        apply Forall2_cons; simpl.
        split; [reflexivity|constructor].
        apply Forall2_cons; simpl.
        split; [reflexivity|constructor].
        apply Forall2_nil; simpl.
      - rewrite (@canon_brands_singleton (@brand_model_relation _ CPModel)).
        reflexivity.
    Qed.

  (* We don't have a typing rule for ⊤ ...
  Lemma makeMainEntity_typedAll db id i:
    (normalize_data (makeMainEntity db id i)) ▹ (Rec AllEntityType AllEntity_pf).
  Proof.
    unfold hasType.
    apply dtrec.
    apply Forall2_cons; simpl.
    - split; try reflexivity.
      (* Type ⊤ here *)
    - apply Forall2_cons; simpl.
      split; [reflexivity|apply dtstring].
      apply Forall2_nil; simpl.
  Qed.
   *)
  
  Definition tout1 := Rec Closed (("total-attribute", Nat)::nil) eq_refl.
  
  Definition tinp1 := (("WORLD", Coll (Brand (singleton "MainEntity")))::nil).

  Require Import TPattern TOps.

  (* This is collapsed using econstructor, but not sure how systematic that would be... -JS *)
  Lemma Example1'_wt τ :
    pat_type tinp1 nil Example1' τ tout1.
  Proof.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    rewrite brands_type_singleton. simpl.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    Grab Existential Variables.
    eauto. eauto. eauto. eauto. eauto.
  Qed.

  (*
  Require Import TAlgEnvInfer.

  Definition tout1infer : option rtype₀ :=
    match infer_algenv_type alg5 (Rec tinp1 eq_refl) Unit with
      | None => None
      | Some x => Some (proj1_sig x)
    end.
  *)

  (*
  Eval compute in tout1infer.
  Eval compute in (proj1_sig tout1).
  *)
    
  Require Import TAlgEnv TPatterntoNRAEnv.
  
  Lemma alg5_wt τ :
    algopt5 ▷ τ >=> Coll tout1 ⊣ tinp1;(Rec Closed nil eq_refl).
  Proof.
    unfold algopt5, CD.camp_to_nraenv.
    unfold PatterntoNRAEnv.translate_pat_to_algenv.
    unfold PatterntoNRAEnv.algenv_of_pat.
    econstructor; eauto.
    econstructor; eauto.
    Focus 2.
    apply (@algenv_of_pat_type_preserve).
    apply Example1'_wt.
    repeat econstructor; eauto.
    Grab Existential Variables.
    eauto.
  Qed.

End CompilerTypedTest.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
