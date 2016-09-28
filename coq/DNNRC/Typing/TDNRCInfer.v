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

Section TDNRCInfer.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Bool.
  Require Import Program.
  Require Import EquivDec Morphisms.

  Require Import Utils BasicSystem.
  Require Import DNNRC.

  Require Import TDNRC.

  (** Type inference for NNRC when given the type of the environment *)

  Require Import TDataInfer.
  Require Import TOpsInfer.
  Require Import TOpsInferSub.

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

  Record type_annotation {A:Set} : Set :=
    mkType_annotation {
        ta_base:A
        (* the inferred (actual most general) type of the expression *)
        ; ta_inferred:drtype
        (* the type as it is used by the context.
           it should always be the case that
           drtype_sub ta_inferred ta_required (proof obligation)
         *)
        ; ta_required:drtype

      }.

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

  Global Arguments type_annotation : clear implicits. 
  Global Arguments mkType_annotation {A} ta_base ta_inferred ta_required.

    End helpers.
  
  Context {fruntime:foreign_runtime}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  Context {fdtyping:foreign_data_typing}.
  Context {fboptyping:foreign_binary_op_typing}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {plug_type:Set}.
  Context {plug:AlgPlug plug_type}.
  (*  Context {tplug:TAlgPlug plug_type}. *)

  Definition di_typeof {A} (d:dnrc (type_annotation A) plug_type)
    := ta_inferred (dnrc_annotation_get d).

  Definition di_required_typeof {A} (d:dnrc (type_annotation A) plug_type)
    := ta_required (dnrc_annotation_get d).

  Definition ta_mk {A:Set} (base:A) (dτ:drtype) : type_annotation A
    := mkType_annotation base dτ dτ.

  Definition ta_require {A} (dτ:drtype) (d:dnrc (type_annotation A) plug_type)
    := dnrc_annotation_update
         (fun a:type_annotation A =>
            mkType_annotation (ta_base a) (ta_inferred a) dτ) d.
  
  Definition bind_local_distr {A} (dτ:drtype) (f1:rtype -> A)
             (f2:rtype -> A) : A :=
    match dτ with
    | Tlocal τ => f1 τ
    | Tdistr τ => f2 τ
    end.

  Fixpoint infer_dnrc_type {A} (tenv:tdbindings) (n:dnrc A plug_type) :
    option (dnrc (type_annotation A) plug_type)
    := match n with
       | DNRCVar a v =>
         lift (fun τ => DNRCVar (ta_mk a τ) v)
              (lookup equiv_dec tenv v)
              
       | DNRCConst a d =>
         lift (fun τ => DNRCConst (ta_mk a (Tlocal τ)) d)
              (infer_data_type (normalize_data brand_relation_brands d))
              
       | DNRCBinop a b n1 n2 =>
         let binf (n₁ n₂:dnrc (type_annotation A) plug_type) : option (dnrc (type_annotation A) plug_type)
             := let dτ₁ := (di_typeof n₁) in
                let dτ₂ := (di_typeof n₂) in
                olift2 (fun τ₁ τ₂ =>
                          lift (fun τs =>
                                  let '(τ, τ₁', τ₂') := τs in
                                  DNRCBinop
                                    (ta_mk a (Tlocal τ))
                                    b
                                    (ta_require (Tlocal τ₁') n₁)
                                    (ta_require (Tlocal τ₂') n₂))
                          (infer_binop_type_sub b τ₁ τ₂))
                       (lift_tlocal dτ₁) (lift_tlocal dτ₂)
         in
         olift2 binf (infer_dnrc_type tenv n1) (infer_dnrc_type tenv n2)

       | DNRCUnop a u n1 =>
         let unf (n₁:dnrc (type_annotation A) plug_type) : option (dnrc (type_annotation A) plug_type)
             := let dτ₁ := (di_typeof n₁) in
                bind_local_distr dτ₁
                                 (* Infer for local values *)
                                 (fun τ₁ =>
                                    lift (fun τs =>
                                            let '(τ, τ₁') := τs in
                                            DNRCUnop
                                              (ta_mk a (Tlocal τ))
                                              u
                                              (ta_require (Tlocal τ₁') n₁))
                                         (infer_unop_type_sub u τ₁))
                                 (* Infer for distributed values *)
                                 (* Note: one example of unop from distr to local ;
                                          one example from distr to distr ... *)
                                 (fun τ₁ =>
                                    match u with
                                    | ACount =>
                                      lift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              DNRCUnop
                                                (ta_mk a (Tlocal τ))
                                                ACount
                                                (ta_require (Tlocal τ₁') n₁))
                                           (infer_unop_type_sub ACount (Coll τ₁))
                                    | ASum =>
                                      lift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              DNRCUnop
                                                (ta_mk a (Tlocal τ))
                                                ASum
                                                (ta_require (Tlocal τ₁') n₁))
                                           (infer_unop_type_sub ASum (Coll τ₁))
                                    | ADistinct =>
                                      olift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              lift2 (fun τc =>
                                                       fun τc₁' =>
                                                         DNRCUnop
                                                           (ta_mk a (Tdistr τc))
                                                           ADistinct
                                                           (ta_require (Tdistr τc₁') n₁))
                                                    (tuncoll τ)
                                                    (tuncoll τ₁')) (* Note: tuncoll is safe because the inference for ADistinct does a join with (Coll ⊥) ensuring that tuncoll would work *)
                                           (infer_unop_type_sub ADistinct (Coll τ₁))
                                    | AFlatten =>
                                      olift (fun τs =>
                                              let '(τ, τ₁') := τs in
                                              lift2 (fun τc =>
                                                       fun τc₁' =>
                                                         DNRCUnop
                                                           (ta_mk a (Tdistr τc))
                                                           AFlatten
                                                           (ta_require (Tdistr τc₁') n₁))
                                                    (tuncoll τ)
                                                    (tuncoll τ₁')) (* Note: tuncoll is safe because the inference for ADistinct does a join with (Coll ⊥) ensuring that tuncoll would work *)
                                           (infer_unop_type_sub AFlatten (Coll τ₁))
                                    | _ => None
                                    end
                                 )
         in
         olift unf (infer_dnrc_type tenv n1)

       | DNRCLet a v n1 n2 =>
         bind (infer_dnrc_type tenv n1)
              (fun n₁ =>
                 let dτ₁ := (di_typeof n₁) in
                 lift (fun n₂ => DNRCLet (ta_mk a (di_typeof n₂)) v n₁ n₂)
                      (infer_dnrc_type ((v,dτ₁)::tenv) n2))

       | DNRCFor a v n1 n2 =>
         bind (infer_dnrc_type tenv n1)
              (fun n₁ =>
                 bind_local_distr (di_typeof n₁)
                                  (* Infer for local collection *)
                                  (fun τ₁l =>
                                     let τ₁l' := τ₁l ⊔ (Coll ⊥) in
                                     bind (tuncoll τ₁l')
                                          (fun τ₁ =>
                                             bind (infer_dnrc_type ((v,Tlocal τ₁)::tenv) n2)
                                                  (fun n₂ =>
                                                     let τ₂ := di_typeof n₂ in
                                                     lift (fun τ₂' =>
                                                             DNRCFor
                                                               (ta_mk a (Tlocal (Coll τ₂')))
                                                               v
                                                               (ta_require (Tlocal τ₁l') n₁)
                                                               n₂)
                                                          (lift_tlocal τ₂))))
                                  (* Infer for distributed collection *)
                                  (fun τ₁l =>
                                     let τ₁ := τ₁l ⊔ ⊥ in
                                     bind (infer_dnrc_type ((v,Tlocal τ₁)::tenv) n2)
                                          (fun n₂ =>
                                             let τ₂ := di_typeof n₂ in
                                             lift (fun τ₂' =>
                                                     DNRCFor
                                                       (ta_mk a (Tdistr τ₂'))
                                                       v
                                                       (ta_require (Tlocal τ₁) n₁)
                                                       n₂)
                                                  (lift_tlocal τ₂)))
              )
       | DNRCIf a n0 n1 n2 =>
         bind (infer_dnrc_type tenv n0)
              (fun n₀ =>
                 let dτ₀ := di_typeof n₀ in
                 if (drtype_sub_dec dτ₀ (Tlocal Bool))
                 then
                   bind (infer_dnrc_type tenv n1)
                        (fun n₁ =>
                           bind (infer_dnrc_type tenv n2)
                                (fun n₂ =>
                                   bind (drtype_join (di_typeof n₁) (di_typeof n₂))
                                        (fun dτ =>
                                           Some (DNRCIf
                                                   (ta_mk a dτ)
                                                   (ta_require (Tlocal Bool) n₀)
                                                   (ta_require dτ n₁)
                                                   (ta_require dτ n₂)
                                   
                        ))))
                 else None
              )

       | DNRCEither a n0 v1 n1 v2 n2 =>
         bind (infer_dnrc_type tenv n0)
              (fun n₀ =>
                 bind (lift_tlocal (di_typeof n₀))
                      (fun dτ₀l =>
                         (* see if it can be given the right structure *)
                         let τ₀l' := dτ₀l ⊔ (Either ⊥ ⊥) in
                         bind (tuneither τ₀l')
                              (fun τlτr =>
                                    let '(τl, τr) := τlτr in
                                    bind (infer_dnrc_type
                                            ((v1,Tlocal τl)::tenv) n1)
                                         (fun n₁ =>
                                            bind (infer_dnrc_type
                                                    ((v2,Tlocal τr)::tenv) n2)
                                                 (fun n₂ =>
                                                    bind (drtype_join (di_typeof n₁) (di_typeof n₂))
                                        (fun dτ =>
                                           Some (DNRCEither
                                                   (ta_mk a dτ)
                                                   (ta_require (Tlocal τ₀l') n₀)
                                                   v1
                                                   (ta_require dτ n₁)
                                                   v2
                                                   (ta_require dτ n₂)
                                 )
              ))))))

       | DNRCCollect a n0 =>
         bind (infer_dnrc_type tenv n0)
              (fun n₀ =>
                 bind (lift_tdistr (di_typeof n₀))
                      (fun τ₀ =>
                         let τ := Tlocal τ₀ in
                         Some (DNRCCollect
                                 (ta_mk a τ)
                                 n₀)))

       | DNRCDispatch a n0 =>
         bind (infer_dnrc_type tenv n0)
              (fun n₀ =>
                 bind (lift_tlocal (di_typeof n₀))
                      (fun τ₀l =>
                         let τ₀l' := τ₀l ⊔ (Coll ⊥) in
                         bind (tuncoll τ₀l')
                              (fun τ₀ =>
                                 let τ := Tdistr τ₀ in
                                 Some (DNRCDispatch
                                         (ta_mk a τ)
                                         (ta_require (Tlocal τ₀l') n₀
              )))))

       | _ => None
       end.

  Example ex1 : dnrc unit plug_type
    := DNRCLet tt "x"%string (DNRCConst tt (dnat 3)) (DNRCBinop tt ALt (DNRCVar tt "x"%string)
                 (DNRCConst tt (dnat 5))).

  Example ex2 : dnrc unit plug_type
    := DNRCFor tt
               "x"%string
               (DNRCConst tt (dcoll nil))
               (DNRCIf tt
                       (DNRCVar tt "x"%string)
                       (DNRCConst tt (dcoll ((dbool true)::nil)))
                       (DNRCConst tt (dcoll ((dnat 3)::nil)))).

  Example ex3 : dnrc unit plug_type
    := DNRCFor tt
               "x"%string
               (DNRCConst tt (dcoll nil))
               (DNRCEither tt
                           (DNRCVar tt "x"%string)
                           "x1"%string
                           (DNRCUnop tt ASum (DNRCConst tt (dcoll (nil))))
                           "x2"%string
                           (DNRCConst tt (dcoll ((dbool true)::nil)))).

  Example ex4 : dnrc unit plug_type :=
    DNRCFor tt "el"%string
            (DNRCCollect tt (DNRCVar tt "WORLD"%string))
            (DNRCUnop tt AToString (DNRCVar tt "el"%string)).

  Example ex5 : dnrc unit plug_type :=
    DNRCFor tt "el"%string
            (DNRCVar tt "WORLD"%string)
            (DNRCUnop tt AToString (DNRCVar tt "el"%string)).

  Example ex6 : dnrc unit plug_type :=
    DNRCUnop tt ACount
             (DNRCCollect tt (DNRCVar tt "WORLD"%string)).

  Example ex7 : dnrc unit plug_type :=
    DNRCUnop tt ACount (DNRCVar tt "WORLD"%string).

  Example ex8 : dnrc unit plug_type :=
    DNRCUnop tt ADistinct
             (DNRCCollect tt (DNRCVar tt "WORLD"%string)).

  Example ex9 : dnrc unit plug_type :=
    DNRCUnop tt ADistinct (DNRCVar tt "WORLD"%string).

  Example ex10 : dnrc unit plug_type :=
    DNRCCollect tt (DNRCUnop tt ADistinct (DNRCVar tt "WORLD"%string)).

  (*
    Eval simpl in infer_dnrc_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex4.
    Eval simpl in infer_dnrc_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex5.
    Eval simpl in infer_dnrc_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex6.
    Eval simpl in infer_dnrc_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex7.

    Eval simpl in infer_dnrc_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex8.

    Eval simpl in infer_dnrc_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex9.

    Eval simpl in infer_dnrc_type
                         (("WORLD"%string, (Tdistr (Brand (("Any"%string)::nil))))::nil)
                         ex10.
   *)

(*
  Eval vm_compute in infer_dnrc_type nil ex1.
  Eval vm_compute in infer_dnrc_type nil ex2.
  Eval vm_compute in infer_dnrc_type nil ex3.
  Eval vm_compute in infer_dnrc_type nil ex4.
  Eval vm_compute in infer_dnrc_type nil ex5.
  Eval vm_compute in infer_dnrc_type nil ex6.
 *)

End TDNRCInfer.

Global Arguments type_annotation {ftype br} A: clear implicits. 

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
