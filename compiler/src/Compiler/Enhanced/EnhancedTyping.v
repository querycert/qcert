(*
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
Require Import ZArith.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import ToString.
Require Import String.
Require Import Utils.
Require Import DataSystem.
Require Import SqlDateComponent.
Require Import UriComponent.

Require Import EnhancedData.
Require Import EnhancedEJson.
Require Import EnhancedDataToEJson.
Require Import EnhancedEJsonToJSON.
Require Import EnhancedToJava.
Require Import EnhancedToJavascriptAst.
Require Import EnhancedReduceOps.
Require Import EnhancedToReduceOps.
Require Import EnhancedToSpark.
Require Import EnhancedType.
Require Import EnhancedToScala.
Require Import EnhancedDataTyping.
Require Import EnhancedTypeToJSON.
Require Import EnhancedRuntime.

Definition SqlDate {br:brand_relation} : rtype := Foreign enhancedSqlDate.
Definition SqlDatePeriod {br:brand_relation} : rtype := Foreign enhancedSqlDatePeriod.

Definition isSqlDate {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedSqlDate => true
  | _ => false
  end.

Definition isSqlDatePeriod {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedSqlDatePeriod => true
  | _ => false
  end.

Definition isNat {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Nat₀ => true
  | _ => false
  end.

Definition isString {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | String₀ => true
  | _ => false
  end.

Definition tuncoll {model:brand_model} (τ:rtype) : option rtype.
Proof.
  destruct τ.
  destruct x.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact (Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)). 
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
Defined.

Inductive sql_date_unary_op_has_type {model:brand_model} : sql_date_unary_op -> rtype -> rtype -> Prop :=
| tuop_sql_date_get_component part : sql_date_unary_op_has_type (uop_sql_date_get_component part) SqlDate Nat
| tuop_sql_date_from_string : sql_date_unary_op_has_type uop_sql_date_from_string RType.String SqlDate
| tuop_sql_date_period_from_string : sql_date_unary_op_has_type uop_sql_date_period_from_string RType.String SqlDatePeriod
.

Inductive uri_unary_op_has_type {model:brand_model} : uri_unary_op -> rtype -> rtype -> Prop :=
| tuop_uri_encode : uri_unary_op_has_type uop_uri_encode RType.String RType.String
| tuop_uri_decode : uri_unary_op_has_type uop_uri_decode RType.String RType.String
.

Definition sql_date_unary_op_type_infer {model : brand_model} (op:sql_date_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_sql_date_get_component part =>
    if isSqlDate τ₁ then Some Nat else None
  | uop_sql_date_from_string =>
    if isString τ₁ then Some SqlDate else None
  | uop_sql_date_period_from_string =>
    if isString τ₁ then Some SqlDatePeriod else None
  end.

Definition uri_unary_op_type_infer {model : brand_model} (op:uri_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_uri_encode =>
    if isString τ₁ then Some RType.String else None
  | uop_uri_decode =>
    if isString τ₁ then Some RType.String else None
  end.

Definition sql_date_unary_op_type_infer_sub {model : brand_model} (op:sql_date_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_sql_date_get_component part =>
    enforce_unary_op_schema (τ₁,SqlDate) Nat
  | uop_sql_date_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) SqlDate
  | uop_sql_date_period_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) SqlDatePeriod
  end.

Lemma sql_date_unary_op_typing_sound {model : brand_model}
      (fu : sql_date_unary_op) (τin τout : rtype) :
  sql_date_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      sql_date_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
              try invcs H0;
              try invcs H3;
              simpl; unfold denhancedsqldate, denhancedsqldateperiod; simpl;
              eexists; split; try reflexivity; repeat constructor;
              repeat constructor].
  destruct part;
    inversion 1; subst;
      try invcs H0;
      try invcs H3;
      simpl; unfold denhancedsqldate, denhancedsqldateperiod; simpl;
        eexists; split; try reflexivity; repeat constructor;
          destruct part; repeat constructor.
Qed.

Lemma uri_unary_op_typing_sound {model : brand_model}
      (fu : uri_unary_op) (τin τout : rtype) :
  uri_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      uri_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
              try invcs H0;
              try invcs H3;
              simpl; simpl;
              eexists; split; try reflexivity;
              repeat constructor].
Qed.

Inductive enhanced_unary_op_has_type {model:brand_model} : enhanced_unary_op -> rtype -> rtype -> Prop
  :=
  | tenhanced_unary_sql_date_op fu τin τout:
      sql_date_unary_op_has_type fu τin τout ->
      enhanced_unary_op_has_type (enhanced_unary_sql_date_op fu) τin τout
  | tenhanced_unary_uri_op fu τin τout:
      uri_unary_op_has_type fu τin τout ->
      enhanced_unary_op_has_type (enhanced_unary_uri_op fu) τin τout.

Definition enhanced_unary_op_typing_infer {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option rtype :=
  match fu with
  | enhanced_unary_uri_op op => uri_unary_op_type_infer op τ
  | enhanced_unary_sql_date_op op => sql_date_unary_op_type_infer op τ
  end.

Lemma enhanced_unary_op_typing_infer_correct
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout} :
  enhanced_unary_op_typing_infer fu τ₁ = Some τout ->
  enhanced_unary_op_has_type fu τ₁ τout.
Proof.
  intros.
  destruct fu; simpl.
  - destruct s; simpl in *.
    + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          destruct ft; simpl in *; try congruence;
            inversion H; subst; clear H; constructor;
              rewrite Foreign_canon; constructor.
    + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H; constructor;
            rewrite String_canon; constructor.
    + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence.
      inversion H; subst; clear H; constructor.
      rewrite String_canon; constructor.
  - destruct u; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H; constructor;
            try (rewrite String_canon; constructor);
            rewrite String_canon; constructor.
Qed.

Lemma enhanced_unary_op_typing_infer_least
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout₁ τout₂} :
  enhanced_unary_op_typing_infer fu τ₁ = Some τout₁ ->
  enhanced_unary_op_has_type fu τ₁ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fu; simpl in *.
  - destruct s; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence.
    + destruct ft; simpl in *; try congruence;
        inversion H; subst; clear H;
          rewrite Foreign_canon in H0;
          inversion H0; subst; clear H0;
            inversion H1; subst; clear H1;
              reflexivity.
    + inversion H; subst; clear H;
        rewrite String_canon in H0;
        inversion H0; subst; clear H0;
          inversion H1; subst; clear H1;
            reflexivity.
    + inversion H; subst; clear H;
        rewrite String_canon in H0;
        inversion H0; subst; clear H0;
          inversion H1; subst; clear H1;
            reflexivity.
  - destruct u; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H;
            try (rewrite String_canon in H0);
            inversion H0; subst; clear H0;
              inversion H1; subst; clear H1;
                reflexivity.
Qed.

Lemma enhanced_unary_op_typing_infer_complete
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout} : 
  enhanced_unary_op_typing_infer fu τ₁ = None ->
  ~ enhanced_unary_op_has_type fu τ₁ τout.
Proof.
  intros.
  destruct fu; simpl in *.
  - destruct s; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          unfold not; intros;
            inversion H0; subst; clear H0;
              inversion H2; subst; clear H2.
    + simpl in H; congruence.
  - destruct u; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          unfold not; intros;
            inversion H0; subst; clear H0;
              inversion H2; subst; clear H2; inversion H.
Qed.

Definition uri_unary_op_type_infer_sub {model : brand_model} (op:uri_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_uri_encode =>
    enforce_unary_op_schema (τ₁,RType.String) RType.String
  | uop_uri_decode =>
    enforce_unary_op_schema (τ₁,RType.String) RType.String
  end.

Definition enhanced_unary_op_typing_infer_sub {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option (rtype*rtype) :=
  match fu with
  | enhanced_unary_sql_date_op op => sql_date_unary_op_type_infer_sub op τ
  | enhanced_unary_uri_op op => uri_unary_op_type_infer_sub op τ
  end.

Lemma enhanced_unary_op_typing_sound {model : brand_model}
      (fu : foreign_operators_unary) (τin τout : rtype) :
  enhanced_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      enhanced_unary_op_interp brand_relation_brands fu din = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply sql_date_unary_op_typing_sound; eauto.
  - eapply uri_unary_op_typing_sound; eauto.
Qed.

Inductive sql_date_binary_op_has_type {model:brand_model} :
  sql_date_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tbop_sql_date_plus :
      sql_date_binary_op_has_type bop_sql_date_plus SqlDate SqlDatePeriod SqlDate 
  | tbop_sql_date_minus :
      sql_date_binary_op_has_type bop_sql_date_minus SqlDate SqlDatePeriod SqlDate 
  | tbop_sql_date_ne :
      sql_date_binary_op_has_type bop_sql_date_ne SqlDate SqlDate Bool 
  | tbop_sql_date_lt :
      sql_date_binary_op_has_type bop_sql_date_lt SqlDate SqlDate Bool 
  | tbop_sql_date_le :
      sql_date_binary_op_has_type bop_sql_date_le SqlDate SqlDate Bool 
  | tbop_sql_date_gt :
      sql_date_binary_op_has_type bop_sql_date_gt SqlDate SqlDate Bool 
  | tbop_sql_date_ge :
      sql_date_binary_op_has_type bop_sql_date_ge SqlDate SqlDate Bool
  | tbop_sql_date_period_between  :
      sql_date_binary_op_has_type bop_sql_date_period_between SqlDate SqlDate SqlDatePeriod
  | tbop_sql_date_set_component part : sql_date_binary_op_has_type (bop_sql_date_set_component part) SqlDate Nat SqlDate
.

Definition sql_date_binary_op_type_infer {model : brand_model} (op:sql_date_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | bop_sql_date_plus =>
    if isSqlDate τ₁ && isSqlDatePeriod τ₂ then Some SqlDate else None
  | bop_sql_date_minus =>
    if isSqlDate τ₁ && isSqlDatePeriod τ₂ then Some SqlDate else None
  | bop_sql_date_ne =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_lt =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_le =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_gt =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_ge =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_period_between  =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some SqlDatePeriod else None
  | bop_sql_date_set_component part =>
    if isSqlDate τ₁ && isNat τ₂ then Some SqlDate else None
  end.

Lemma sql_date_binary_op_typing_sound {model : brand_model}
      (fb : sql_date_binary_op) (τin₁ τin₂ τout : rtype) :
  sql_date_binary_op_has_type fb τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      sql_date_binary_op_interp fb din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    inversion 1; subst;
      inversion 1; subst;
        try invcs H0;
        try invcs H1;
        invcs H3;
        try invcs H4;
        simpl; 
        try (destruct part);
        eexists; split; try reflexivity;
          repeat constructor.
Qed.

Definition sql_date_binary_op_type_infer_sub {model : brand_model} (op:sql_date_binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
  match op with
  | bop_sql_date_plus => enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDatePeriod) SqlDate
  | bop_sql_date_minus => enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDatePeriod) SqlDate
  | bop_sql_date_ne
  | bop_sql_date_lt
  | bop_sql_date_le
  | bop_sql_date_gt
  | bop_sql_date_ge =>
    enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDate) Bool
  | bop_sql_date_period_between  =>
    enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDate) SqlDatePeriod
  | bop_sql_date_set_component part =>
    enforce_binary_op_schema (τ₁,SqlDate) (τ₂,Nat) SqlDate
  end.

Inductive enhanced_binary_op_has_type {model:brand_model} :
  enhanced_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tenhanced_binary_sql_date_op fb τin₁ τin₂ τout:
      sql_date_binary_op_has_type fb τin₁ τin₂ τout ->
      enhanced_binary_op_has_type (enhanced_binary_sql_date_op fb) τin₁ τin₂ τout.

Definition enhanced_binary_op_typing_infer {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_sql_date_op fb => sql_date_binary_op_type_infer fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_infer_correct
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout} :
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  intros.
  destruct fb; simpl.
  - destruct s; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate;
        unfold isSqlDate, isSqlDatePeriod, isNat in *
        ; destruct x; simpl in H; try discriminate
        ; destruct ft; simpl in H; try discriminate
        ; destruct x0; simpl in H; try discriminate
        ; try (destruct ft; simpl in H; try discriminate)
        ; invcs H
        ; constructor
        ; repeat rewrite Nat_canon
        ; repeat rewrite Foreign_canon
        ; constructor.
Qed.

Lemma enhanced_binary_op_typing_infer_least
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout₁ τout₂} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout₁ ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fb; simpl.
  - destruct s; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate
      ; unfold isSqlDate, isSqlDatePeriod, isNat in *
      ; destruct x; simpl in H; try discriminate
      ; destruct ft; simpl in H; try discriminate
      ; destruct x0; simpl in H; try discriminate
      ; try (destruct ft; simpl in H; try discriminate)
      ; invcs H
      ; repeat rewrite Foreign_canon in H0
      ; invcs H0
      ; invcs H1
      ; reflexivity.
Qed.

Lemma enhanced_binary_op_typing_infer_complete
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = None ->
  ~ enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  destruct fb; simpl; intros.
  - intro HH; invcs HH.
    destruct s; simpl in *; invcs H1; simpl in H; try discriminate.
Qed.

Definition enhanced_binary_op_typing_infer_sub {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_sql_date_op fb => sql_date_binary_op_type_infer_sub fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_sound {model : brand_model}
      (fu : foreign_operators_binary) (τin₁ τin₂ τout : rtype) :
  enhanced_binary_op_has_type fu τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      enhanced_binary_op_interp brand_relation_brands fu din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply sql_date_binary_op_typing_sound; eauto.
Qed.

Instance enhanced_foreign_operators_typing
         {model:brand_model} :
  @foreign_operators_typing
    enhanced_foreign_data
    enhanced_foreign_operators
    enhanced_foreign_type
    enhanced_foreign_data_typing
    model
  := { foreign_operators_typing_unary_has_type := enhanced_unary_op_has_type
       ; foreign_operators_typing_unary_sound := enhanced_unary_op_typing_sound
       ; foreign_operators_typing_unary_infer := enhanced_unary_op_typing_infer
       ; foreign_operators_typing_unary_infer_correct := enhanced_unary_op_typing_infer_correct
       ; foreign_operators_typing_unary_infer_least := enhanced_unary_op_typing_infer_least
       ; foreign_operators_typing_unary_infer_complete := enhanced_unary_op_typing_infer_complete
       ; foreign_operators_typing_unary_infer_sub := enhanced_unary_op_typing_infer_sub
       ; foreign_operators_typing_binary_has_type := enhanced_binary_op_has_type
       ; foreign_operators_typing_binary_sound := enhanced_binary_op_typing_sound
       ; foreign_operators_typing_binary_infer := enhanced_binary_op_typing_infer
       ; foreign_operators_typing_binary_infer_correct := enhanced_binary_op_typing_infer_correct
       ; foreign_operators_typing_binary_infer_least := enhanced_binary_op_typing_infer_least
       ; foreign_operators_typing_binary_infer_complete := enhanced_binary_op_typing_infer_complete
       ; foreign_operators_typing_binary_infer_sub := enhanced_binary_op_typing_infer_sub
     }.

Instance enhanced_foreign_typing {model:brand_model}:
  @foreign_typing
    enhanced_foreign_runtime
    enhanced_foreign_type
    model
  := mk_foreign_typing
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_data_typing
       enhanced_foreign_operators_typing.

