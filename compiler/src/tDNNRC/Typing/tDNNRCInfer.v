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
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import DNNRCSystem.
Require Import tDNNRC.

Section tDNNRCInfer.
  (** Type inference for NNNRC when given the type of the environment *)

  Section helpers.
    Context {ftype:foreign_type}.
    Context {br:brand_relation}.
    
    Definition lift_tlocal (dτ:drtype) : option rtype :=
      match dτ with
      | Tlocal τ => Some τ
      | Tdistr _ => None
      end.
  
    Definition lift_tdistr (dτ:drtype) : option rtype :=
      match dτ with
      | Tlocal _ => None
      | Tdistr τ => Some (Coll τ)
      end.

    Definition drtype_join (dτ₁ dτ₂:drtype) : option drtype
      := match dτ₁, dτ₂ with
         | Tlocal τ₁, Tlocal τ₂ => Some (Tlocal (τ₁ ⊔ τ₂))
         | Tdistr τ₁, Tdistr τ₂ => Some (Tdistr (τ₁ ⊔ τ₂))
         | _, _ => None
         end.

    Definition drtype_map (f:rtype->rtype) (d:drtype) : drtype
      := match d with
         | Tlocal t => Tlocal (f t)
         | Tdistr t => Tdistr (f t)
         end.

    Definition drtype_omap (f:rtype->option rtype) (d:drtype) : option drtype
      := match d with
         | Tlocal t => lift Tlocal (f t)
         | Tdistr t => lift Tdistr (f t)
         end.

  End helpers.
  
  Context {fruntime:foreign_runtime}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  Context {fdtyping:foreign_data_typing}.
  Context {fboptyping:foreign_binary_op_typing}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {plug_type:Set}.
  Context {plug:AlgPlug plug_type}.

  Definition di_typeof {A} (d:@dnnrc_base _ (type_annotation A) plug_type)
    := ta_inferred (dnnrc_base_annotation_get d).

  Definition di_required_typeof {A} (d:@dnnrc_base _ (type_annotation A) plug_type)
    := ta_required (dnnrc_base_annotation_get d).

  Definition ta_mk {A:Set} (base:A) (dτ:drtype) : type_annotation A
    := mkType_annotation base dτ dτ.

  Definition ta_require {A} (dτ:drtype) (d:@dnnrc_base _ (type_annotation A) plug_type)
    := dnnrc_base_annotation_update
         (fun a:type_annotation A =>
            mkType_annotation (ta_base a) (ta_inferred a) dτ) d.
  
  Definition bind_local_distr {A} (dτ:drtype) (f1:rtype -> A)
             (f2:rtype -> A) : A :=
    match dτ with
    | Tlocal τ => f1 τ
    | Tdistr τ => f2 τ
    end.

  Context (τconstants:tdbindings).
      
  Fixpoint infer_dnnrc_base_type {A} (tenv:tdbindings) (n:@dnnrc_base _ A plug_type) :
    option (@dnnrc_base _ (type_annotation A) plug_type)
    := match n with
       | DNNRCGetConstant a v =>
         lift (fun τ => DNNRCGetConstant (ta_mk a τ) v)
              (tdot τconstants v)
              
       | DNNRCVar a v =>
         lift (fun τ => DNNRCVar (ta_mk a τ) v)
              (lookup equiv_dec tenv v)
              
       | DNNRCConst a d =>
         lift (fun τ => DNNRCConst (ta_mk a (Tlocal τ)) d)
              (infer_data_type (normalize_data brand_relation_brands d))
              
       | DNNRCBinop a b n1 n2 =>
         let binf (n₁ n₂:@dnnrc_base _ (type_annotation A) plug_type) : option (@dnnrc_base _ (type_annotation A) plug_type)
             := let dτ₁ := (di_typeof n₁) in
                let dτ₂ := (di_typeof n₂) in
                olift2 (fun τ₁ τ₂ =>
                          lift (fun τs =>
                                  let '(τ, τ₁', τ₂') := τs in
                                  DNNRCBinop
                                    (ta_mk a (Tlocal τ))
                                    b
                                    (ta_require (Tlocal τ₁') n₁)
                                    (ta_require (Tlocal τ₂') n₂))
                          (infer_binary_op_type_sub b τ₁ τ₂))
                       (lift_tlocal dτ₁) (lift_tlocal dτ₂)
         in
         olift2 binf (infer_dnnrc_base_type tenv n1) (infer_dnnrc_base_type tenv n2)

       | DNNRCUnop a u n1 =>
         let unf (n₁:@dnnrc_base _ (type_annotation A) plug_type) : option (@dnnrc_base _ (type_annotation A) plug_type)
             := let dτ₁ := (di_typeof n₁) in
                bind_local_distr dτ₁
                                 (* Infer for local values *)
                                 (fun τ₁ =>
                                    lift (fun τs =>
                                            let '(τ, τ₁') := τs in
                                            DNNRCUnop
                                              (ta_mk a (Tlocal τ))
                                              u
                                              (ta_require (Tlocal τ₁') n₁))
                                         (infer_unary_op_type_sub u τ₁))
                                 (* Infer for distributed values *)
                                 (* Note: one example of unop from distr to local ;
                                          one example from distr to distr ... *)
                                 (fun τ₁ =>
                                    match u with
                                    | OpCount =>
                                      lift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              DNNRCUnop
                                                (ta_mk a (Tlocal τ))
                                                OpCount
                                                (ta_require (Tlocal τ₁') n₁))
                                           (infer_unary_op_type_sub OpCount (Coll τ₁))
                                    | OpNatSum =>
                                      lift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              DNNRCUnop
                                                (ta_mk a (Tlocal τ))
                                                OpNatSum
                                                (ta_require (Tlocal τ₁') n₁))
                                           (infer_unary_op_type_sub OpNatSum (Coll τ₁))
                                    | OpDistinct =>
                                      olift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              lift2 (fun τc =>
                                                       fun τc₁' =>
                                                         DNNRCUnop
                                                           (ta_mk a (Tdistr τc))
                                                           OpDistinct
                                                           (ta_require (Tdistr τc₁') n₁))
                                                    (tuncoll τ)
                                                    (tuncoll τ₁')) (* Note: tuncoll is safe because the inference for ADistinct does a join with (Coll ⊥) ensuring that tuncoll would work *)
                                           (infer_unary_op_type_sub OpDistinct (Coll τ₁))
                                    | OpFlatten =>
                                      olift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              lift2 (fun τc =>
                                                       fun τc₁' =>
                                                         DNNRCUnop
                                                           (ta_mk a (Tdistr τc))
                                                           OpFlatten
                                                           (ta_require (Tdistr τc₁') n₁))
                                                    (tuncoll τ)
                                                    (tuncoll τ₁')) (* Note: tuncoll is safe because the inference for ADistinct does a join with (Coll ⊥) ensuring that tuncoll would work *)
                                           (infer_unary_op_type_sub OpFlatten (Coll τ₁))
                                    | _ => None
                                    end
                                 )
         in
         olift unf (infer_dnnrc_base_type tenv n1)

       | DNNRCLet a v n1 n2 =>
         bind (infer_dnnrc_base_type tenv n1)
              (fun n₁ =>
                 let dτ₁ := (di_typeof n₁) in
                 lift (fun n₂ => DNNRCLet (ta_mk a (di_typeof n₂)) v n₁ n₂)
                      (infer_dnnrc_base_type ((v,dτ₁)::tenv) n2))

       | DNNRCFor a v n1 n2 =>
         bind (infer_dnnrc_base_type tenv n1)
              (fun n₁ =>
                 bind_local_distr (di_typeof n₁)
                                  (* Infer for local collection *)
                                  (fun τ₁l =>
                                     let τ₁l' := τ₁l ⊔ (Coll ⊥) in
                                     bind (tuncoll τ₁l')
                                          (fun τ₁ =>
                                             bind (infer_dnnrc_base_type ((v,Tlocal τ₁)::tenv) n2)
                                                  (fun n₂ =>
                                                     let τ₂ := di_typeof n₂ in
                                                     lift (fun τ₂' =>
                                                             DNNRCFor
                                                               (ta_mk a (Tlocal (Coll τ₂')))
                                                               v
                                                               (ta_require (Tlocal τ₁l') n₁)
                                                               n₂)
                                                          (lift_tlocal τ₂))))
                                  (* Infer for distributed collection *)
                                  (fun τ₁l =>
                                     let τ₁ := τ₁l ⊔ ⊥ in
                                     bind (infer_dnnrc_base_type ((v,Tlocal τ₁)::tenv) n2)
                                          (fun n₂ =>
                                             let τ₂ := di_typeof n₂ in
                                             lift (fun τ₂' =>
                                                     DNNRCFor
                                                       (ta_mk a (Tdistr τ₂'))
                                                       v
                                                       (ta_require (Tlocal τ₁) n₁)
                                                       n₂)
                                                  (lift_tlocal τ₂)))
              )
       | DNNRCIf a n0 n1 n2 =>
         bind (infer_dnnrc_base_type tenv n0)
              (fun n₀ =>
                 let dτ₀ := di_typeof n₀ in
                 if (drtype_sub_dec dτ₀ (Tlocal Bool))
                 then
                   bind (infer_dnnrc_base_type tenv n1)
                        (fun n₁ =>
                           bind (infer_dnnrc_base_type tenv n2)
                                (fun n₂ =>
                                   bind (drtype_join (di_typeof n₁) (di_typeof n₂))
                                        (fun dτ =>
                                           Some (DNNRCIf
                                                   (ta_mk a dτ)
                                                   (ta_require (Tlocal Bool) n₀)
                                                   (ta_require dτ n₁)
                                                   (ta_require dτ n₂)
                                   
                        ))))
                 else None
              )

       | DNNRCEither a n0 v1 n1 v2 n2 =>
         bind (infer_dnnrc_base_type tenv n0)
              (fun n₀ =>
                 bind (lift_tlocal (di_typeof n₀))
                      (fun dτ₀l =>
                         (* see if it can be given the right structure *)
                         let τ₀l' := dτ₀l ⊔ (Either ⊥ ⊥) in
                         bind (tuneither τ₀l')
                              (fun τlτr =>
                                    let '(τl, τr) := τlτr in
                                    bind (infer_dnnrc_base_type
                                            ((v1,Tlocal τl)::tenv) n1)
                                         (fun n₁ =>
                                            bind (infer_dnnrc_base_type
                                                    ((v2,Tlocal τr)::tenv) n2)
                                                 (fun n₂ =>
                                                    bind (drtype_join (di_typeof n₁) (di_typeof n₂))
                                        (fun dτ =>
                                           Some (DNNRCEither
                                                   (ta_mk a dτ)
                                                   (ta_require (Tlocal τ₀l') n₀)
                                                   v1
                                                   (ta_require dτ n₁)
                                                   v2
                                                   (ta_require dτ n₂)
                                 )
              ))))))

       | DNNRCCollect a n0 =>
         bind (infer_dnnrc_base_type tenv n0)
              (fun n₀ =>
                 bind (lift_tdistr (di_typeof n₀))
                      (fun τ₀ =>
                         let τ := Tlocal τ₀ in
                         Some (DNNRCCollect
                                 (ta_mk a τ)
                                 n₀)))

       | DNNRCDispatch a n0 =>
         bind (infer_dnnrc_base_type tenv n0)
              (fun n₀ =>
                 bind (lift_tlocal (di_typeof n₀))
                      (fun τ₀l =>
                         let τ₀l' := τ₀l ⊔ (Coll ⊥) in
                         bind (tuncoll τ₀l')
                              (fun τ₀ =>
                                 let τ := Tdistr τ₀ in
                                 Some (DNNRCDispatch
                                         (ta_mk a τ)
                                         (ta_require (Tlocal τ₀l') n₀
              )))))

       | DNNRCGroupBy a g sl n1 =>
         bind (infer_dnnrc_base_type tenv n1)
              (fun n₁ =>
                 bind (lift_tlocal (di_typeof n₁))
                      (fun τ₁l =>
                         let τ₁l' := τ₁l ⊔ (Coll ⊥) in
                         bind (tuncoll τ₁l')
                              (fun τ₁ =>
                                 olift (fun τs =>
                                         let '(τ, τ₁') := τs in
                                         olift (fun τs₂ =>
                                                 let '(τ₂, τ₂') := τs₂ in
                                                 lift (fun τs₃ =>
                                                         let '(τ₃, τ₃', τ₃'') := τs₃ in
                                                         DNNRCGroupBy
                                                           (ta_mk a (Tlocal (Coll τ₃)))
                                                           g sl
                                                           (ta_require (Tlocal (Coll τ₁l')) n₁))
                                                      (infer_binary_op_type_sub OpRecConcat τ₂ τ)
                                               )
                                               (infer_unary_op_type_sub (OpRec g) τ₁l'))
                                       (infer_unary_op_type_sub (OpRecProject sl) τ₁))))
       | DNNRCAlg _ _ _ => None
       end.

  Example ex1 : @dnnrc_base _ unit plug_type
    := DNNRCLet tt "x"%string (DNNRCConst tt (dnat 3)) (DNNRCBinop tt OpLt (DNNRCVar tt "x"%string)
                 (DNNRCConst tt (dnat 5))).

  Example ex2 : @dnnrc_base _ unit plug_type
    := DNNRCFor tt
               "x"%string
               (DNNRCConst tt (dcoll nil))
               (DNNRCIf tt
                       (DNNRCVar tt "x"%string)
                       (DNNRCConst tt (dcoll ((dbool true)::nil)))
                       (DNNRCConst tt (dcoll ((dnat 3)::nil)))).

  Example ex3 : @dnnrc_base _ unit plug_type
    := DNNRCFor tt
               "x"%string
               (DNNRCConst tt (dcoll nil))
               (DNNRCEither tt
                           (DNNRCVar tt "x"%string)
                           "x1"%string
                           (DNNRCUnop tt OpNatSum (DNNRCConst tt (dcoll (nil))))
                           "x2"%string
                           (DNNRCConst tt (dcoll ((dbool true)::nil)))).

  Example ex4 : @dnnrc_base _ unit plug_type :=
    DNNRCFor tt "el"%string
            (DNNRCCollect tt (DNNRCVar tt "WORLD"%string))
            (DNNRCUnop tt OpToString (DNNRCVar tt "el"%string)).

  Example ex5 : @dnnrc_base _ unit plug_type :=
    DNNRCFor tt "el"%string
            (DNNRCVar tt "WORLD"%string)
            (DNNRCUnop tt OpToString (DNNRCVar tt "el"%string)).

  Example ex6 : @dnnrc_base _ unit plug_type :=
    DNNRCUnop tt OpCount
             (DNNRCCollect tt (DNNRCVar tt "WORLD"%string)).

  Example ex7 : @dnnrc_base _ unit plug_type :=
    DNNRCUnop tt OpCount (DNNRCVar tt "WORLD"%string).

  Example ex8 : @dnnrc_base _ unit plug_type :=
    DNNRCUnop tt OpDistinct
             (DNNRCCollect tt (DNNRCVar tt "WORLD"%string)).

  Example ex9 : @dnnrc_base _ unit plug_type :=
    DNNRCUnop tt OpDistinct (DNNRCVar tt "WORLD"%string).

  Example ex10 : @dnnrc_base _ unit plug_type :=
    DNNRCVar tt "WORLD"%string.

  (*
    Eval simpl in infer_dnnrc_base_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex4.
    Eval simpl in infer_dnnrc_base_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex5.
    Eval simpl in infer_dnnrc_base_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex6.
    Eval simpl in infer_dnnrc_base_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex7.

    Eval simpl in infer_dnnrc_base_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex8.

    Eval simpl in infer_dnnrc_base_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex9.

    Eval simpl in infer_dnnrc_base_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex10.

   *)

  (* Small utility function which gets the final type annotation,
     removes the proof and evaluates it to get the final type result *)
  Definition unwrap_pf_compute {A} n :=
    Eval vm_compute in
    match @di_typeof A n with
    | Tlocal r => (proj1_sig r)
    | Tdistr r => (proj1_sig r)
    end.

  (* A slightly more interesting type with records to test the group by inference *)
  (* Note "partition" is there to check that the concat order in the type inference is right,
     the new "partition" for the group in the example should shadow the one from the input *)
  Definition t0_rec :=
    ("age"%string,Nat)::("name"%string,String)::("partition"%string,Nat)::nil.

  Lemma t0_rec_wf :
    is_list_sorted ODT_lt_dec (domain t0_rec) = true.
  Proof.
    simpl.
    reflexivity.
  Defined.
  
  Definition t0 :=
    Tdistr (Rec Closed t0_rec t0_rec_wf).

  Example ex11 : @dnnrc_base _ unit plug_type :=
    DNNRCGroupBy tt "partition"%string ("name"%string::nil)
                 (DNNRCCollect tt (DNNRCVar tt "$vConst$WORLD"%string)).

  (*
  Eval vm_compute in (lift unwrap_pf_compute
                        (infer_dnnrc_base_type
                           (("$vConst$WORLD"%string, t0)::nil)
                           ex11)).
   *)

  Example ex12 : @dnnrc_base _ unit plug_type :=
    DNNRCGroupBy tt "partition"%string ("age"%string::"name"%string::nil)
                 (DNNRCCollect tt (DNNRCVar tt "$vConst$WORLD"%string)).

  (*
  Eval vm_compute in (lift unwrap_pf_compute
                        (infer_dnnrc_base_type
                           (("$vConst$WORLD"%string, t0)::nil)
                           ex12)).
   *)

  Example ex13 : @dnnrc_base _ unit plug_type :=
    DNNRCFor tt
             "$vtmap$0"%string
             (DNNRCUnop tt OpFlatten
                        (DNNRCFor tt
                                  "$vtprod$0"%string
                                  (DNNRCCollect tt (DNNRCVar tt "$vConst$WORLD"%string))
                                  (DNNRCUnop tt OpBag
                                             (DNNRCBinop tt OpRecConcat
                                                         (DNNRCVar tt "$vtprod$0"%string)
                                                         (DNNRCConst tt (drec nil))))))
             (DNNRCUnop tt (OpRec "name")
                        (DNNRCUnop tt (OpDot "name") (DNNRCVar tt "$vtmap$0"%string))).

  (*
  Eval vm_compute in (lift unwrap_pf_compute
                        (infer_dnnrc_base_type
                           (("$vConst$WORLD"%string, t0)::nil)
                           ex13)).
*)
  
(*
  Eval vm_compute in infer_dnnrc_base_type nil ex1.
  Eval vm_compute in infer_dnnrc_base_type nil ex2.
  Eval vm_compute in infer_dnnrc_base_type nil ex3.
  Eval vm_compute in infer_dnnrc_base_type nil ex4.
  Eval vm_compute in infer_dnnrc_base_type nil ex5.
  Eval vm_compute in infer_dnnrc_base_type nil ex6.
 *)

End tDNNRCInfer.

(* Global Arguments type_annotation {ftype br} A: clear implicits.  *)

