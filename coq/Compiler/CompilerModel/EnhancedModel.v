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

Require Import List EquivDec.

Require Import Utils BasicSystem.
Require Import ForeignToJava ForeignToJavascript ForeignToScala ForeignToJSON ForeignTypeToJSON.
Require Import ForeignToSpark.
Require Import ForeignReduceOps ForeignToReduceOps.
Require Import ForeignCloudant ForeignToCloudant.
Require Import CompilerRuntime CompilerModel.

Require Import FloatModelPart StringModelPart. 
Require Import DateTimeModelPart.
Require NNRCMR CloudantMR.
Require Import OptimizerLogger String RAlgEnv NNRC.

Import ListNotations.

Local Open Scope list_scope.

(* TODO: these should move *)
Definition check_subtype_pairs
           {br:brand_relation}
           {fr:foreign_type}
           (l:list (rtype*rtype)) : bool
  := forallb (fun τs => if subtype_dec (fst τs) (snd τs) then true else false) l.

Definition enforce_unary_op_schema
           {br:brand_relation}
           {fr:foreign_type}
           (ts1:rtype*rtype) (tr:rtype)
  : option (rtype*rtype)
  := if check_subtype_pairs (ts1::nil)
    then Some (tr, (snd ts1))
    else None.

Definition enforce_binary_op_schema
           {br:brand_relation}
           {fr:foreign_type}
           (ts1:rtype*rtype) (ts2:rtype*rtype) (tr:rtype)
  : option (rtype*rtype*rtype)
  := if check_subtype_pairs (ts1::ts2::nil)
    then Some (tr, (snd ts1), (snd ts2))
    else None.

Inductive enhanced_data : Set
  :=
  | enhancedfloat : FLOAT -> enhanced_data
  | enhancedstring : STRING -> enhanced_data
  | enhancedtimescale : time_scale -> enhanced_data
  | enhancedtimeduration : TIME_DURATION -> enhanced_data
  | enhancedtimepoint : TIME_POINT -> enhanced_data
.

Inductive enhanced_type : Set
  :=
  | enhancedTop : enhanced_type
  | enhancedBottom : enhanced_type
  | enhancedFloat : enhanced_type
  | enhancedString : enhanced_type
  | enhancedTimeScale : enhanced_type
  | enhancedTimeDuration : enhanced_type
  | enhancedTimePoint : enhanced_type
.

Definition enhanced_type_to_string (et:enhanced_type) : string :=
  match et with
  | enhancedTop => "ETop"
  | enhancedBottom => "EBottom"
  | enhancedFloat => "EFloat"
  | enhancedString => "EString"
  | enhancedTimeScale => "ETimeScale"
  | enhancedTimeDuration => "ETimeDuration"
  | enhancedTimePoint => "ETimePoint"
  end.

Definition string_to_enhanced_type (s:string) : option enhanced_type :=
  match s with
  | "ETop"%string => Some enhancedTop
  | "EBottom"%string => Some enhancedBottom
  | "EFloat"%string => Some enhancedFloat
  | "EString"%string => Some enhancedString
  | "ETimeScale"%string => Some enhancedTimeScale
  | "ETimeDuration"%string => Some enhancedTimeDuration
  | "ETimePoint"%string => Some enhancedTimePoint
  | _ => None
  end.

Require Import RelationClasses Equivalence.

Existing Instance float_foreign_data.
Existing Instance time_scale_foreign_data.
Existing Instance time_duration_foreign_data.
Existing Instance time_point_foreign_data.
Program Instance enhanced_foreign_data : foreign_data
  := mk_foreign_data enhanced_data _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  destruct x; destruct y; simpl; try solve [right; inversion 1].
  - destruct (@foreign_data_dec float_foreign_data f f0); simpl; intros.
    + left; congruence.
    + right; congruence.
  - case_eq (STRING_eq s s0).
    + left; intros.
      f_equal.
      apply StringModelPart.STRING_eq_correct in H.
      trivial.
    + right; intros.
      inversion H0.
      apply StringModelPart.STRING_eq_correct in H2.
      congruence.
  - destruct (t == t0).
    + left; congruence.
    + right; congruence.
  - case_eq (TIME_DURATION_eq t t0).
    + left; intros.
      f_equal.
      apply DateTimeModelPart.TIME_DURATION_eq_correct in H.
      trivial.
    + right; intros.
      inversion H0.
      apply DateTimeModelPart.TIME_DURATION_eq_correct in H2.
      congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec time_point_foreign_data) t t0).
    + left; congruence.
    + right; congruence.
Defined.
Next Obligation.
  (* normalized? *)
  destruct a.
  - exact (@foreign_data_normalized float_foreign_data f).
  - exact True.
  - exact (@foreign_data_normalized time_scale_foreign_data t).
  - exact (@foreign_data_normalized time_duration_foreign_data t).
  - exact (@foreign_data_normalized time_point_foreign_data t).
Defined.
Next Obligation.
  destruct a.
  - exact (@foreign_data_normalize_normalizes float_foreign_data f).
  - simpl; trivial.
  - exact (@foreign_data_normalize_normalizes time_scale_foreign_data t).
  - exact (@foreign_data_normalize_normalizes time_duration_foreign_data t).
  - exact (@foreign_data_normalize_normalizes time_point_foreign_data t).
Defined.
Next Obligation.
  constructor.
  destruct 1.
  - exact (@toString _ (@foreign_data_tostring float_foreign_data) f).
  - exact (STRING_tostring s).
  - exact (toString t).
  - exact (@toString _ (@foreign_data_tostring time_duration_foreign_data) t).
  - exact (@toString _ (@foreign_data_tostring time_point_foreign_data) t).
Defined.

Definition denhancedfloat f := dforeign (enhancedfloat f).
Definition denhancedstring s := dforeign (enhancedstring s).
Definition denhancedtimescale ts := dforeign (enhancedtimescale ts).
Definition denhancedtimeduration td := dforeign (enhancedtimeduration td).
Definition denhancedtimepoint tp := dforeign (enhancedtimepoint tp).

Require Import JSON.
Definition jenhancedfloat f := jforeign (enhancedfloat f).
Definition jenhancedstring s := jforeign (enhancedstring s).
Definition jenhancedtimescale ts := jforeign (enhancedtimescale ts).
Definition jenhancedtimeduration td := jforeign (enhancedtimeduration td).
Definition jenhancedtimepoint tp := jforeign (enhancedtimepoint tp).

Inductive enhanced_unary_op
  :=
  | enhanced_unary_float_op : float_unary_op -> enhanced_unary_op
  | enhanced_unary_time_op : time_unary_op -> enhanced_unary_op.

Definition ondfloat {A} (f : FLOAT -> A) (d : data) : option A
  := match d with
     | dforeign (enhancedfloat fd) => Some (f fd)
     | _ => None
     end.

Definition rondfloat (f: FLOAT -> FLOAT) (d:data) : option data
  := lift denhancedfloat (ondfloat f d).

Definition ondcollfloat {A} (f : list FLOAT -> A) (d : data) : option A
  := lift_oncoll (fun x => lift f (rmap (fun z => ondfloat id z) x)) d.

Definition rondcollfloat (f: list FLOAT -> FLOAT) (d:data) : option data
  := lift denhancedfloat (ondcollfloat f d).

Definition float_unary_op_interp (op:float_unary_op) (d:data) : option data

  := match op with
     | uop_float_neg => rondfloat FLOAT_neg d
     | uop_float_sqrt => rondfloat FLOAT_sqrt d
     | uop_float_exp => rondfloat FLOAT_exp d
     | uop_float_log => rondfloat FLOAT_log d
     | uop_float_log10 => rondfloat FLOAT_log10 d
     | uop_float_of_int => lift denhancedfloat (ondnat FLOAT_of_int d)
     | uop_float_ceil => rondfloat FLOAT_ceil d
     | uop_float_floor => rondfloat FLOAT_floor d
     | uop_float_truncate => lift dnat (ondfloat FLOAT_truncate d)
     | uop_float_abs => rondfloat FLOAT_abs d
     | uop_float_sum => rondcollfloat FLOAT_sum d
     | uop_float_arithmean => rondcollfloat FLOAT_arithmean d
     | uop_float_listmin => rondcollfloat FLOAT_listmin d
     | uop_float_listmax => rondcollfloat FLOAT_listmax d
     end.

Definition ondstring {A} (f : String.string -> A) (d : data) : option A
  := match d with
     | dstring s => Some (f s)
     | _ => None
     end.

Definition ondtimepoint {A} (f : TIME_POINT -> A) (d : data) : option A
  := match d with
     | dforeign (enhancedtimepoint fd) => Some (f fd)
     | _ => None
     end.

Definition time_unary_op_interp (op:time_unary_op) (d:data) : option data
  := match op with
     | uop_time_to_scale => lift denhancedtimescale (ondtimepoint TIME_POINT_to_scale d)
     | uop_time_from_string => lift denhancedtimepoint (ondstring TIME_POINT_from_string d)
     | uop_time_duration_from_string => lift denhancedtimeduration (ondstring TIME_DURATION_from_string d)
     end.

Definition enhanced_unary_op_interp
           (br:brand_relation_t)
           (op:enhanced_unary_op)
           (d:data) : option data
  := match op with
     | enhanced_unary_float_op f => float_unary_op_interp f d
     | enhanced_unary_time_op f => time_unary_op_interp f d
     end.

Require Import String.

Program Instance enhanced_foreign_unary_op : foreign_unary_op
  := { foreign_unary_op_type := enhanced_unary_op
       ; foreign_unary_op_interp := enhanced_unary_op_interp }.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  - decide equality.
  - decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (float_unary_op_tostring f).
  - exact (time_unary_op_tostring t).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct f; simpl in H;
      unfold rondfloat, rondcollfloat, lift in H;
      destruct d; simpl in H; try discriminate;
        simpl in H; try unfold lift in H;
        try (destruct f; invcs H;
          repeat constructor).
    + destruct z; invcs H; repeat constructor.
    + match_destr_in H; invcs H; repeat constructor.
    + match_destr_in H; invcs H; repeat constructor.
    + match_destr_in H; invcs H; repeat constructor.
    + match_destr_in H; invcs H; repeat constructor.
  - destruct t; simpl in H;
      unfold ondtimepoint, ondstring, denhancedtimepoint, denhancedtimeduration, lift in H; simpl in H;
        destruct d; simpl in H; try discriminate.
    + destruct f; invcs H; repeat constructor.
    + invcs H; repeat constructor.
    + invcs H; repeat constructor.
Qed.

Definition ondfloat2 {A} (f : FLOAT -> FLOAT -> A) (d1 d2 : data) : option A
  := match d1, d2 with
     | dforeign (enhancedfloat fd1), dforeign (enhancedfloat fd2) => Some (f fd1 fd2)
     | _, _ => None
     end.

Definition rondfloat2 (f: FLOAT -> FLOAT -> FLOAT) (d1 d2:data) : option data
  := lift denhancedfloat (ondfloat2 f d1 d2).

Definition rondboolfloat2 (f: FLOAT -> FLOAT -> bool) (d1 d2:data) : option data
  := lift dbool (ondfloat2 f d1 d2).

Inductive enhanced_binary_op
  :=
  | enhanced_binary_float_op : float_binary_op -> enhanced_binary_op
  | enhanced_binary_time_op : time_binary_op -> enhanced_binary_op
.

Definition float_binary_op_interp
           (op:float_binary_op) (d1 d2:data) : option data
  := match op with
     | bop_float_plus => rondfloat2 FLOAT_plus d1 d2
     | bop_float_minus => rondfloat2 FLOAT_minus d1 d2
     | bop_float_mult => rondfloat2 FLOAT_mult d1 d2
     | bop_float_div => rondfloat2 FLOAT_div d1 d2
     | bop_float_pow => rondfloat2 FLOAT_pow d1 d2
     | bop_float_min => rondfloat2 FLOAT_min d1 d2
     | bop_float_max => rondfloat2 FLOAT_max d1 d2
     | bop_float_ne => rondboolfloat2 FLOAT_ne d1 d2
     | bop_float_lt => rondboolfloat2 FLOAT_lt d1 d2
     | bop_float_le => rondboolfloat2 FLOAT_le d1 d2
     | bop_float_gt => rondboolfloat2 FLOAT_gt d1 d2
     | bop_float_ge => rondboolfloat2 FLOAT_ge d1 d2
     end.

Definition ondtimepoint2 {A} (f : TIME_POINT -> TIME_POINT -> A) (d1 d2 : data) : option A
  := match d1, d2 with
     | dforeign (enhancedtimepoint fd1), dforeign (enhancedtimepoint fd2) => Some (f fd1 fd2)
     | _, _ => None
     end.

Definition rondbooltimepoint2 (f: TIME_POINT -> TIME_POINT -> bool) (d1 d2:data) : option data
  := lift dbool (ondtimepoint2 f d1 d2).

Definition rondtimepoint2 (f: TIME_POINT -> TIME_POINT -> TIME_POINT) (d1 d2:data) : option data
  := lift denhancedtimepoint (ondtimepoint2 f d1 d2).

Definition time_binary_op_interp
           (op:time_binary_op) (d1 d2:data) : option data
  := match op with
     | bop_time_as =>
       match d1, d2 with
       | dforeign (enhancedtimepoint tp), dforeign (enhancedtimescale ts)
         => Some (denhancedtimepoint (TIME_POINT_as tp ts))
       | _,_ => None
       end
     | bop_time_shift =>
       match d1, d2 with
       | dforeign (enhancedtimepoint tp), dforeign (enhancedtimeduration td)
         => Some (denhancedtimepoint (TIME_POINT_shift tp td))
       | _,_ => None
       end
     | bop_time_ne => rondbooltimepoint2 TIME_POINT_ne d1 d2
     | bop_time_lt => rondbooltimepoint2 TIME_POINT_lt d1 d2
     | bop_time_le => rondbooltimepoint2 TIME_POINT_le d1 d2
     | bop_time_gt => rondbooltimepoint2 TIME_POINT_gt d1 d2
     | bop_time_ge => rondbooltimepoint2 TIME_POINT_ge d1 d2
     | bop_time_duration_from_scale =>
       match d1, d2 with
       | dforeign (enhancedtimescale ts), (dnat count)
         => Some (denhancedtimeduration (TIME_DURATION_from_scale ts count))
       | _,_ => None
       end
     | bop_time_duration_between => lift denhancedtimeduration (ondtimepoint2 TIME_DURATION_between d1 d2)
     end.

Definition enhanced_binary_op_interp
           (br:brand_relation_t)
           (op:enhanced_binary_op)
           (d1 d2:data) : option data
  := match op with
     | enhanced_binary_float_op f => float_binary_op_interp f d1 d2
     | enhanced_binary_time_op f => time_binary_op_interp f d1 d2
     end.

Program Instance enhanced_foreign_binary_op : foreign_binary_op
  := { foreign_binary_op_type := enhanced_binary_op
       ; foreign_binary_op_interp := enhanced_binary_op_interp }.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  - decide equality.
  - decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (float_binary_op_tostring f).
  - exact (time_binary_op_tostring t).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct f; simpl in H;
    unfold rondfloat2, rondboolfloat2, lift in H
    ; destruct d1; simpl in H; try discriminate
    ; destruct f; simpl in H; try discriminate
    ; destruct d2; simpl in H; try discriminate
    ; destruct f0; simpl in H; try discriminate
    ; invcs H
    ; repeat constructor.
  - destruct t; simpl in H;
      unfold rondtimepoint2, rondbooltimepoint2, denhancedtimeduration, lift in H
      ; destruct d1; simpl in H; try discriminate
      ; destruct f; simpl in H; try discriminate
      ; destruct d2; simpl in H; try discriminate
      ; try (destruct f; simpl in H; try discriminate)
      ; invcs H
      ; repeat constructor.
Qed.

Instance enhanced_foreign_runtime :
  foreign_runtime
  := mk_foreign_runtime
       enhanced_foreign_data
       enhanced_foreign_unary_op
       enhanced_foreign_binary_op.

(* TODO: fix me *)
Definition enhanced_to_java_data
           (quotel:String.string) (fd:enhanced_data) : java_json
  := match fd with
     | enhancedfloat f => mk_java_json (FLOAT_tostring f)
     | enhancedstring s => mk_java_json (STRING_tostring s)
     | enhancedtimescale ts => mk_java_json (time_scale_to_java_string ts)
     | enhancedtimeduration td => mk_java_json (@toString _ time_duration_foreign_data.(@foreign_data_tostring ) td)
     | enhancedtimepoint tp => mk_java_json (@toString _ time_point_foreign_data.(@foreign_data_tostring ) tp)
     end.

Definition enhanced_to_java_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:enhanced_unary_op)
             (d:java_json) : java_json
  := match fu with
     | enhanced_unary_float_op op =>
       float_to_java_unary_op indent eol quotel op d
     | enhanced_unary_time_op op =>
       time_to_java_unary_op indent eol quotel op d
     end.

Definition enhanced_to_java_binary_op
           (indent:nat) (eol:String.string)
           (quotel:String.string) (fb:enhanced_binary_op)
           (d1 d2:java_json) : java_json
  := match fb with
     | enhanced_binary_float_op op =>
       float_to_java_binary_op indent eol quotel op d1 d2
     | enhanced_binary_time_op op =>
       time_to_java_binary_op indent eol quotel op d1 d2
     end.

Instance enhanced_foreign_to_java :
  @foreign_to_java enhanced_foreign_runtime
  := mk_foreign_to_java
       enhanced_foreign_runtime
       enhanced_to_java_data
       enhanced_to_java_unary_op
       enhanced_to_java_binary_op.

Definition enhanced_to_javascript_data
           (quotel:String.string) (fd:enhanced_data) : String.string
  := match fd with
     | enhancedfloat f => FLOAT_tostring f
     | enhancedstring s => STRING_tostring s
     | enhancedtimescale ts => toString ts
     | enhancedtimeduration td => (@toString _ time_duration_foreign_data.(@foreign_data_tostring ) td)
     | enhancedtimepoint tp => (@toString _ time_point_foreign_data.(@foreign_data_tostring ) tp)
     end.

(* Java equivalent: JavaScriptBackend.foreign_to_javascript_unary_op *)
Definition enhanced_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:enhanced_unary_op)
             (d:String.string) : String.string
  := match fu with
     | enhanced_unary_float_op op =>
       float_to_javascript_unary_op indent eol quotel op d
     | enhanced_unary_time_op op =>
       time_to_javascript_unary_op indent eol quotel op d
     end.

(* Java equivalent: JavaScriptBackend.foreign_to_javascript_binary_op *)
Definition enhanced_to_javascript_binary_op
           (indent:nat) (eol:String.string)
           (quotel:String.string) (fb:enhanced_binary_op)
           (d1 d2:String.string) : String.string
  := match fb with
     | enhanced_binary_float_op op =>
       float_to_javascript_binary_op indent eol quotel op d1 d2
     | enhanced_binary_time_op op =>
       time_to_javascript_binary_op indent eol quotel op d1 d2
     end.

Instance enhanced_foreign_to_javascript :
  @foreign_to_javascript enhanced_foreign_runtime
  := mk_foreign_to_javascript
       enhanced_foreign_runtime
       enhanced_to_javascript_data
       enhanced_to_javascript_unary_op
       enhanced_to_javascript_binary_op.

Definition enhanced_to_scala_unary_op (op: enhanced_unary_op) (d: string) : string :=
  match op with
    | enhanced_unary_float_op op =>
      float_to_scala_unary_op op d
    | enhanced_unary_time_op op => "EnhancedModel: Time ops not supported for now."
  end.

Instance enhanced_foreign_to_scala :
  @foreign_to_scala enhanced_foreign_runtime
  := mk_foreign_to_scala
       enhanced_foreign_runtime
       enhanced_to_scala_unary_op.

(* TODO: add general support for "tagged" stuff in JSON.
    Like our left/right encoding.  so that we can use it for
    timescale/timepoint.  just using a string may work for now.
*)



Program Instance enhanced_foreign_to_JSON : foreign_to_JSON
  := mk_foreign_to_JSON enhanced_foreign_data _ _.
Next Obligation.
  (* TODO: For now, we assume that JSON supports floating point *)
  exact None.
Defined.
Next Obligation.
  destruct fd.
  - exact (jenhancedfloat f).
  - exact (jenhancedstring s).
  - exact (jstring (toString t)).
  - exact (jstring (@toString _ time_duration_foreign_data.(@foreign_data_tostring ) t)).
  - exact (jstring (@toString _ time_point_foreign_data.(@foreign_data_tostring ) t)).
Defined.

  Inductive enhanced_numeric_type :=
  | enhanced_numeric_int
  | enhanced_numeric_float.

  Global Instance enhanced_numeric_type_eqdec : EqDec enhanced_numeric_type eq.
  Proof.
    red. unfold equiv, complement.
    change (forall x y : enhanced_numeric_type, {x = y} + {x <> y}).
    decide equality.
  Defined.

  Definition enhanced_to_cld_numeric_type
             (typ:enhanced_numeric_type) : CloudantMR.cld_numeric_type
    := match typ with
       | enhanced_numeric_int => CloudantMR.Cld_int
       | enhanced_numeric_float => CloudantMR.Cld_float
       end.

Inductive enhanced_reduce_op
  := RedOpCount : enhanced_reduce_op
   | RedOpSum (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMin (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMax (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpArithMean (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpStats (typ:enhanced_numeric_type) : enhanced_reduce_op.

Definition enhanced_numeric_type_prefix
           (typ:enhanced_numeric_type) : string
  := match typ with
     | enhanced_numeric_int => ""%string
     | enhanced_numeric_float => "F"%string
     end.

Definition enhanced_reduce_op_tostring (op:enhanced_reduce_op) : string
  := match op with
     | RedOpCount => "COUNT"%string
     | RedOpSum typ => append (enhanced_numeric_type_prefix typ) "FSUM"%string
     | RedOpMin typ  => append (enhanced_numeric_type_prefix typ) "FMIN"%string
     | RedOpMax typ => append (enhanced_numeric_type_prefix typ) "FMAX"%string
     | RedOpArithMean typ => append (enhanced_numeric_type_prefix typ) "FARITHMEAN"%string
     | RedOpStats typ => append (enhanced_numeric_type_prefix typ) "FSTATS"%string
     end.

Definition enhanced_numeric_sum (typ:enhanced_numeric_type) : unaryOp
  := match typ with
     | enhanced_numeric_int
       => ASum
     | enhanced_numeric_float
       => AForeignUnaryOp (enhanced_unary_float_op uop_float_sum)
     end.

Definition enhanced_numeric_min (typ:enhanced_numeric_type) : unaryOp
  := match typ with
     | enhanced_numeric_int
       => ANumMin
     | enhanced_numeric_float
       => AForeignUnaryOp (enhanced_unary_float_op uop_float_listmin)
     end.

Definition enhanced_numeric_max (typ:enhanced_numeric_type) : unaryOp
  := match typ with
     | enhanced_numeric_int
       => ANumMax
     | enhanced_numeric_float
       => AForeignUnaryOp (enhanced_unary_float_op uop_float_listmax)
     end.

Definition enhanced_numeric_arith_mean (typ:enhanced_numeric_type) : unaryOp
  := match typ with
     | enhanced_numeric_int
       => AArithMean
     | enhanced_numeric_float
       => AForeignUnaryOp (enhanced_unary_float_op uop_float_arithmean)
     end.

Definition enhanced_reduce_op_interp
           (br:brand_relation_t)
           (op:enhanced_reduce_op)
           (dl:list data) : option data
  := match op with
      | RedOpCount | RedOpSum _ | RedOpMin _ | RedOpMax _ | RedOpArithMean _ =>
        let uop :=
            match op with
            | RedOpCount  => ACount
            | RedOpSum typ => enhanced_numeric_sum typ
            | RedOpMin typ => enhanced_numeric_min typ
            | RedOpMax typ => enhanced_numeric_max typ
            | RedOpArithMean typ => enhanced_numeric_arith_mean typ
            | RedOpStats _ => ACount (* assert false *)
            end
        in
        fun_of_unaryop br uop (dcoll dl) 
      | RedOpStats typ =>
        let coll := dcoll dl in
        let count := fun_of_unaryop br ACount coll in
        let sum := fun_of_unaryop br (enhanced_numeric_sum typ) coll in
        let min := fun_of_unaryop br (enhanced_numeric_min typ) coll in
        let max := fun_of_unaryop br (enhanced_numeric_max typ) coll in
        let v :=
            match (count, sum, min, max) with
              | (Some count, Some sum, Some min, Some max) =>
                Some (drec (("count"%string, count)
                              ::("max"%string, max)
                              ::("min"%string, min)
                              ::("sum"%string, sum)
                              ::nil))
              | _ => None
            end
        in
        v
     end.

Program Instance enhanced_foreign_reduce_op : foreign_reduce_op
  := mk_foreign_reduce_op enhanced_foreign_data enhanced_reduce_op _ _ enhanced_reduce_op_interp _.
Next Obligation.
  red; unfold equiv, complement.
  change (forall x y:enhanced_reduce_op, {x = y} + {x <> y}).
  decide equality; decide equality.
Defined.
Next Obligation.
  constructor.
  apply enhanced_reduce_op_tostring.
Defined.
Next Obligation.
  destruct op; simpl in *; invcs H.
  - constructor.
  - destruct typ; simpl in *.
    + apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold rondcollfloat, ondcollfloat, lift in H2.
      simpl in H2.
      match_destr_in H2.
      invcs H2.
      repeat constructor.
  - destruct typ; simpl in *.
    + unfold lifted_min in *.
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold rondcollfloat, ondcollfloat, lift in H2.
      simpl in H2.
      match_destr_in H2.
      invcs H2.
      repeat constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold rondcollfloat, ondcollfloat, lift in H2.
      simpl in H2.
      match_destr_in H2.
      invcs H2.
      repeat constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold rondcollfloat, ondcollfloat, lift in H2.
      simpl in H2.
      match_destr_in H2.
      invcs H2.
      repeat constructor.
  - destruct typ; simpl in *.
    + destruct (dsum dl); simpl in *; try discriminate.
      unfold lifted_min, lifted_max in *.
      destruct ((lift bnummin (lifted_zbag dl))); simpl in *; try discriminate.
      destruct ((lift bnummax (lifted_zbag dl))); simpl in *; try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
      * reflexivity.
    + unfold rondcollfloat, ondcollfloat, lift in H2.
      simpl in H2.
      destruct ( match rmap (fun z : data => ondfloat id z) dl with
           | Some a' => Some (FLOAT_sum a')
           | None => None
           end); try discriminate.
      destruct ( match rmap (fun z : data => ondfloat id z) dl with
               | Some a' => Some (FLOAT_listmin a')
               | None => None
                 end); try discriminate.
      destruct ( match rmap (fun z : data => ondfloat id z) dl with
               | Some a' => Some (FLOAT_listmax a')
               | None => None
                 end); try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
      * reflexivity.
Qed.

Definition enhanced_to_reduce_op (uop:unaryOp) : option NNRCMR.reduce_op
  := match uop with
     | ACount => Some (NNRCMR.RedOpForeign RedOpCount)
     | ASum =>
       Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int))
     | AForeignUnaryOp (enhanced_unary_float_op uop_float_sum) =>
       Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float))
     | ANumMin =>
       Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int))
     | AForeignUnaryOp (enhanced_unary_float_op uop_float_listmin) =>
       Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float))
     | ANumMax =>
       Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int))
     | AForeignUnaryOp (enhanced_unary_float_op uop_float_listmax) =>
       Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float))
     | AArithMean =>
       Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int))
     | AForeignUnaryOp (enhanced_unary_float_op uop_float_arithmean) =>
       Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float))
     | _ => None
     end.

Definition enhanced_of_reduce_op (rop:NNRCMR.reduce_op) : option unaryOp
  := match rop with
     | NNRCMR.RedOpForeign RedOpCount => Some ACount
     | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int) =>
       Some (ASum)
     | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float) =>
       Some (AForeignUnaryOp (enhanced_unary_float_op uop_float_sum))
     | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int) =>
       Some (ANumMin)
     | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float) =>
       Some (AForeignUnaryOp (enhanced_unary_float_op uop_float_listmin))
     | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int) =>
       Some (ANumMax)
     | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float) =>
       Some (AForeignUnaryOp (enhanced_unary_float_op uop_float_listmax))
     | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int) =>
       Some (AArithMean)
     | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float) =>
       Some (AForeignUnaryOp (enhanced_unary_float_op uop_float_arithmean))
     | NNRCMR.RedOpForeign (RedOpStats _) =>
       None (* XXX TODO? XXX *)
     end.

Program Instance enhanced_foreign_to_reduce_op : foreign_to_reduce_op
  := mk_foreign_to_reduce_op enhanced_foreign_runtime enhanced_foreign_reduce_op enhanced_to_reduce_op _ enhanced_of_reduce_op _.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct uop; simpl in *; invcs H; try reflexivity.
  destruct fu; try discriminate.
  destruct f; invcs H1; reflexivity.
Qed.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct rop; simpl in *; invcs H; try reflexivity.
  destruct f; invcs H1; simpl; try reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
Qed.

Local Open Scope string_scope.
Definition enhanced_to_spark_reduce_op
           (rop:enhanced_reduce_op)
           (scala_endl quotel:string) : string
  := match rop with
      | RedOpCount => ".count().toString()"
      | RedOpSum enhanced_numeric_int => ".aggregate(0)(_ + _.toInt, _ + _).toString()"
      | RedOpSum enhanced_numeric_float => ".aggregate(0.0)(_ + _.toDouble, _ + _).toString()"
      | RedOpMin enhanced_numeric_int => ".aggregate(Int.MaxValue)(((x, y) => Math.min(x, y.toInt)), Math.min).toString()"
      | RedOpMin enhanced_numeric_float => ".aggregate(Double.MaxValue)(((x, y) => Math.min(x, y.toDouble)), Math.min).toString()"
      | RedOpMax enhanced_numeric_int =>
        ".aggregate(Int.MinValue)(((x, y) => Math.max(x, y.toInt)), Math.max).toString()"
      | RedOpMax enhanced_numeric_float =>
        ".aggregate(Double.MinValue)(((x, y) => Math.max(x, y.toDouble)), Math.max).toString()"
      | RedOpStats _ =>
        ".aggregate("""")(statsReduce, statsRereduce).toString()" ++ scala_endl ++
                     "  sc.parallelize(Array(res))"
      | RedOpArithMean _ => (* assert false *)
        ".arithmean /* ArithMean must be removed before code generation */"
     end.

(* NRCMR rewrites *)
Require Import NNRCRuntime NNRCMRRuntime NRewMR.

  (* Java equivalent: MROptimizer.min_max_to_stats *)
  Definition min_max_to_stats avoid (mr: mr) :=
    match mr.(mr_reduce) with
    | RedOp (RedOpForeign op) =>
      match op with
      | RedOpMin typ | RedOpMax typ =>
        let stats_field :=
            match op with
            | RedOpMin _ => "min"%string
            | RedOpMax _ => "max"%string
            | _ => "ERROR"%string (* assert false *)
            end
        in
        let (tmp, avoid) := fresh_mr_var "stats$" avoid in
        let mr1 :=
           mkMR
             mr.(mr_input)
             tmp
             mr.(mr_map)
             (RedOp (RedOpForeign (RedOpStats typ)))
        in
        let x := "stats"%string in
        let mr2 :=
            mkMR
              tmp
              mr.(mr_output)
              (MapScalar (x, NRCUnop AColl (NRCUnop (ADot stats_field) (NRCVar x))))
              RedSingleton
        in
        Some (mr1::mr2::nil)
      | _ => None
      end
    | _ => None
    end.

  (* Java equivalent: MROptimizer.arithmean_to_stats *)
  Definition arithmean_to_stats avoid (mr: mr) :=
    match mr.(mr_reduce) with
    | RedOp (RedOpForeign op) =>
      match op with
      | RedOpArithMean typ =>
        let (tmp, avoid) := fresh_mr_var "stats$" avoid in
        let mr1 :=
           mkMR
             mr.(mr_input)
             tmp
             mr.(mr_map)
             (RedOp (RedOpForeign (RedOpStats typ)))
        in
        let map :=
            match typ with
            | enhanced_numeric_int =>
              let zero := NRCConst (dnat 0) in
              let x := "stats"%string in
              MapScalar (x, NRCUnop AColl
                                    (NRCIf (NRCBinop AEq (NRCUnop (ADot "count"%string) (NRCVar x)) zero)
                                           zero
                                           (NRCBinop (ABArith ArithDivide)
                                                     (NRCUnop (ADot "sum"%string) (NRCVar x))
                                                     (NRCUnop (ADot "count"%string) (NRCVar x)))))
            | enhanced_numeric_float =>
              let zero := NRCConst (dnat 0) in
              let zerof := NRCConst (denhancedfloat FLOAT_CONST0) in
              let x := "stats"%string in
              MapScalar (x, NRCUnop AColl
                                    (NRCIf (NRCBinop AEq (NRCUnop (ADot "count"%string) (NRCVar x)) zero)
                                           zerof
                                           (NRCBinop (AForeignBinaryOp (enhanced_binary_float_op bop_float_div))
                                                     (NRCUnop (ADot "sum"%string) (NRCVar x))
                                                     (NRCUnop (AForeignUnaryOp (enhanced_unary_float_op uop_float_of_int))
                                                       (NRCUnop (ADot "count"%string) (NRCVar x))))))
            end
        in
        let mr2 :=
            mkMR
              tmp
              mr.(mr_output)
              map
              RedSingleton
        in
        Some (mr1::mr2::nil)
      | _ => None
      end
    | _ => None
    end.

  Definition min_max_free_reduce (src:reduce_fun)
    := match src with
       | RedOp (RedOpForeign (RedOpMin _|RedOpMax _)) => False
       | _ => True
       end.

  Definition arithmean_free_reduce (src:reduce_fun)
    := match src with
       | RedOp (RedOpForeign (RedOpArithMean _)) => False
       | _ => True
       end.

  Definition min_max_free_mr (src:mr)
    := min_max_free_reduce src.(mr_reduce).

  Definition arithmean_free_mr (src:mr)
    := arithmean_free_reduce src.(mr_reduce).

  Definition min_max_free_mr_chain (src:list mr)
    := Forall min_max_free_mr src.

  Definition min_max_free_nrcmr (src:nrcmr)
    := min_max_free_mr_chain src.(mr_chain).

  Definition arithmean_free_mr_chain (src:list mr)
    := Forall arithmean_free_mr src.

  Definition arithmean_free_nrcmr (src:nrcmr)
    := arithmean_free_mr_chain src.(mr_chain).

  Definition to_spark_nrcmr (l: nrcmr) :=
    let avoid := get_nrcmr_vars l in
    let l := apply_rewrite (arithmean_to_stats avoid) l in
    l.

  Definition to_spark_nrcmr_prepared (src:nrcmr)
    := arithmean_free_nrcmr src.

Program Instance enhanced_foreign_to_spark : foreign_to_spark
  := mk_foreign_to_spark
       enhanced_foreign_runtime
       enhanced_foreign_reduce_op
       enhanced_to_spark_reduce_op
       to_spark_nrcmr.

Instance enhanced_foreign_cloudant : foreign_cloudant
  := mk_foreign_cloudant
       enhanced_foreign_runtime
       (AForeignUnaryOp (enhanced_unary_float_op uop_float_sum))
       (AForeignUnaryOp (enhanced_unary_float_op uop_float_listmin))
       (AForeignUnaryOp (enhanced_unary_float_op uop_float_listmax)).

Definition enhanced_to_cloudant_reduce_op
           (rop:enhanced_reduce_op) : CloudantMR.cld_reduce_op
  := match rop with
     | RedOpCount => CloudantMR.CldRedOpCount
     | RedOpSum typ => CloudantMR.CldRedOpSum (enhanced_to_cld_numeric_type typ)
     | RedOpStats typ => CloudantMR.CldRedOpStats (enhanced_to_cld_numeric_type typ)
     | RedOpMin _ => CloudantMR.CldRedOpStats CloudantMR.Cld_int (* assert false *)
     | RedOpMax _ => CloudantMR.CldRedOpStats CloudantMR.Cld_int (* assert false *)
     | RedOpArithMean _ => CloudantMR.CldRedOpStats CloudantMR.Cld_int (* assert false *)
     end.

  (* Java equivalent: MROptimizer.foreign_to_cloudant_prepare_nrcmr *)
  Definition to_cloudant_nrcmr (l: nrcmr) :=
    let avoid := get_nrcmr_vars l in
    let l := apply_rewrite (min_max_to_stats avoid) l in
    let l := apply_rewrite (arithmean_to_stats avoid) l in
    l.

  Definition to_cloudant_nrcmr_prepared (src:nrcmr)
    := min_max_free_nrcmr src /\ arithmean_free_nrcmr src.

  Program Instance enhanced_foreign_to_cloudant : foreign_to_cloudant
    :=
      { foreign_to_cloudant_reduce_op := enhanced_to_cloudant_reduce_op
        ; foreign_to_cloudant_prepare_nrcmr := to_cloudant_nrcmr
        ; foreign_to_cloudant_nrcmr_prepared := to_cloudant_nrcmr_prepared
      }.
  Next Obligation.
    unfold to_cloudant_nrcmr.
    unfold to_cloudant_nrcmr_prepared.
    unfold min_max_free_nrcmr, min_max_free_mr_chain, min_max_free_mr, min_max_free_reduce.
    split.
    - unfold apply_rewrite, min_max_to_stats.
      unfold mr_chain_apply_rewrite.
      apply Forall_forall; intros ? inn.
      simpl in *.
      apply in_flat_map in inn.
      destruct inn as [? [inn1 inn2]].
      destruct x; simpl.
      destruct mr_reduce; simpl in *;
        unfold min_max_free_mr;
        simpl;
      trivial.
      destruct r; simpl in *; trivial.
      destruct x0; simpl in *.
      destruct mr_reduce; simpl in *;
        try solve [invcs inn2; invcs H].
      destruct r; simpl in * .
      destruct f0; simpl in *.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + admit.
      + admit. (* XXXXXXXXXXXXXXXX *)
      + intuition.
        invcs H; trivial.
        intuition.
        invcs H0; trivial.
      + intuition.
        invcs H; trivial.
    - unfold apply_rewrite, mr_chain_apply_rewrite, arithmean_free_nrcmr, arithmean_free_mr_chain.
      simpl in *.
      apply Forall_forall; intros ? inn.
      apply in_flat_map in inn.
      destruct inn as [? [inn1 inn2]].
      destruct x; simpl.
      destruct mr_reduce; simpl in *;
        unfold arithmean_free_mr;
        simpl;
      trivial.
      destruct r; simpl in *; trivial.
      destruct x0; simpl in *.
      destruct mr_reduce; simpl in *;
        try solve [invcs inn2; invcs H].
      destruct r; simpl in * .
      destruct f0; simpl in *.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
        invcs H0; trivial.
      + intuition.
        invcs H; trivial.
  Admitted.

  (* optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_token_type : Set.
  Extract Constant OPTIMIZER_LOGGER_token_type => "Util.logger_token_type".

  Axiom OPTIMIZER_LOGGER_nra_startPass :
    String.string -> algenv -> OPTIMIZER_LOGGER_token_type.

  Extract Constant OPTIMIZER_LOGGER_nra_startPass =>
  "(fun name input -> Logger.log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_nra_step :
    OPTIMIZER_LOGGER_token_type -> String.string ->
    algenv -> algenv ->
    OPTIMIZER_LOGGER_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nra_step =>
  "(fun token name input output -> Logger.log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_nra_endPass :
    OPTIMIZER_LOGGER_token_type -> algenv -> OPTIMIZER_LOGGER_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nra_endPass =>
  "(fun token output -> Logger.log_endPass token output)".

  Instance foreign_nra_optimizer_logger :
    optimizer_logger string algenv
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nra_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nra_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nra_endPass
      } .

  Axiom OPTIMIZER_LOGGER_nrc_startPass :
    String.string -> nrc -> OPTIMIZER_LOGGER_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nrc_startPass =>
  "(fun name input -> Logger.log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_nrc_step :
    OPTIMIZER_LOGGER_token_type -> String.string ->
    nrc -> nrc ->
    OPTIMIZER_LOGGER_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nrc_step =>
  "(fun token name input output -> Logger.log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_nrc_endPass :
    OPTIMIZER_LOGGER_token_type -> nrc -> OPTIMIZER_LOGGER_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nrc_endPass =>
  "(fun token output -> Logger.log_endPass token output)".

  Instance foreign_nrc_optimizer_logger :
    optimizer_logger string nrc
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nrc_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nrc_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nrc_endPass
      } .
    

(** Foreign typing, used to build the basic_model *)

Definition enhanced_type_join (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedBottom, _ => t2
     | _, enhancedBottom => t1
     | enhancedFloat, enhancedFloat => enhancedFloat
     | enhancedString, enhancedString => enhancedString
     | enhancedTimeScale, enhancedTimeScale => enhancedTimeScale
     | enhancedTimeDuration, enhancedTimeDuration => enhancedTimeDuration
     | enhancedTimePoint, enhancedTimePoint => enhancedTimePoint
     | _, _ => enhancedTop
     end.

Definition enhanced_type_meet (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedTop, _ => t2
     | _, enhancedTop => t1
     | enhancedFloat, enhancedFloat => enhancedFloat
     | enhancedString, enhancedString => enhancedString
     | enhancedTimeScale, enhancedTimeScale => enhancedTimeScale
     | enhancedTimeDuration, enhancedTimeDuration => enhancedTimeDuration
     | enhancedTimePoint, enhancedTimePoint => enhancedTimePoint
     | _, _ => enhancedBottom
     end.

Inductive enhanced_subtype : enhanced_type -> enhanced_type -> Prop :=
| enhanced_subtype_top t : enhanced_subtype t enhancedTop
| enhanced_subtype_bottom t : enhanced_subtype enhancedBottom t
| enhanced_subtype_refl t : enhanced_subtype t t.

Instance enhanced_subtype_pre : PreOrder enhanced_subtype.
Proof.
  constructor; red; intros.
  - destruct x; constructor.
  - inversion H; inversion H0; subst; try constructor; congruence.
Qed.

Instance enhanced_subtype_post : PartialOrder eq enhanced_subtype.
Proof.
  intros x y; split.
  - intros; subst.
    repeat red.
    split; constructor.
  - destruct 1.
    inversion H; inversion H0; congruence.
Qed.

Instance enhanced_type_lattice : Lattice enhanced_type eq
  := {
      join := enhanced_type_join
      ; meet := enhanced_type_meet
    }.
Proof.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
    reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
    reflexivity.
  - red; intros t1.
    simpl.
    destruct t1; simpl; try reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
    reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
    reflexivity.
  - red; intros t1.
    destruct t1; simpl;
    reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
Defined.

Instance enhanced_type_olattice : OLattice eq enhanced_subtype.
Proof.
  constructor.
  split.
  - destruct a; destruct b; inversion 1; simpl; reflexivity.
  - destruct a; destruct b; inversion 1; simpl;
    constructor.
Qed.

Program Instance enhanced_foreign_type : foreign_type
  := mk_foreign_type enhanced_type _ _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  intros.
  change ({x = y} + {x <> y}).
  decide equality.
Defined.
Next Obligation.
  destruct a; destruct b; try solve [left; constructor | right; inversion 1].
Defined.

Program Instance enhanced_foreign_type_to_JSON : foreign_type_to_JSON
  := mk_foreign_type_to_JSON enhanced_foreign_type _ _.
Next Obligation.
  exact (string_to_enhanced_type s).
Defined.
Next Obligation.
  exact (enhanced_type_to_string fd).
Defined.

Inductive enhanced_has_type : enhanced_data -> enhanced_type -> Prop :=
| enhanced_has_type_top fd : enhanced_has_type fd enhancedTop
| enhanced_has_type_float (f:FLOAT) : enhanced_has_type (enhancedfloat f) enhancedFloat
| enhanced_has_type_string (s:STRING) : enhanced_has_type (enhancedstring s) enhancedString
| enhanced_has_type_timescale (ts:time_scale) : enhanced_has_type (enhancedtimescale ts) enhancedTimeScale
| enhanced_has_type_timepoint (tp:TIME_POINT) : enhanced_has_type (enhancedtimepoint tp) enhancedTimePoint
| enhanced_has_type_timeduration (td:TIME_DURATION) : enhanced_has_type (enhancedtimeduration td) enhancedTimeDuration
.

Definition enhanced_infer_type (d:enhanced_data) : option enhanced_type
  := match d with
     | enhancedfloat _ => Some enhancedFloat
     | enhancedstring _ => Some enhancedString
     | enhancedtimescale _ => Some enhancedTimeScale
     | enhancedtimeduration _ => Some enhancedTimeDuration
     | enhancedtimepoint _ => Some enhancedTimePoint
     end.

Program Instance enhanced_foreign_data_typing :
  @foreign_data_typing enhanced_foreign_data enhanced_foreign_type
  := mk_foreign_data_typing
       enhanced_foreign_data
       enhanced_foreign_type
       enhanced_has_type _ _ _
       enhanced_infer_type _ _ _
.
Next Obligation.
  inversion H; subst;
    simpl; trivial.
  - destruct d; simpl; constructor.
  - constructor.
  - constructor.
  - constructor.
Defined.
Next Obligation.
  inversion H0; subst; simpl.
  - constructor.
  - inversion H.
  - trivial.
Defined.
Next Obligation.
  inversion H; inversion H0; subst; simpl; try constructor; congruence.
Defined.
Next Obligation.
  destruct d; simpl; eexists; reflexivity.
Defined.
Next Obligation.
  destruct d; simpl in H; invcs H; constructor.
Defined.
Next Obligation.
  destruct d; simpl in H, H0
  ; invcs H; invcs H0; constructor.
Defined.

Module EnhancedRuntime <: CompilerRuntime.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_foreign_runtime : foreign_runtime
    := enhanced_foreign_runtime.
  Definition compiler_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_foreign_to_javascript : foreign_to_javascript
    := enhanced_foreign_to_javascript.
  Definition compiler_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_foreign_to_JSON : foreign_to_JSON
    := enhanced_foreign_to_JSON.
  Definition compiler_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_foreign_cloudant : foreign_cloudant
    := enhanced_foreign_cloudant.
  Definition compiler_foreign_to_cloudant : foreign_to_cloudant
    := enhanced_foreign_to_cloudant.
  Definition compiler_nra_optimizer_logger : optimizer_logger string algenv
    := foreign_nra_optimizer_logger.
  Definition compiler_nrc_optimizer_logger : optimizer_logger string nrc
    := foreign_nrc_optimizer_logger.
  Definition compiler_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedRuntime.

Definition Float {br:brand_relation} : rtype := Foreign enhancedFloat.
Definition TimeScale {br:brand_relation} : rtype := Foreign enhancedTimeScale.
Definition TimeDuration {br:brand_relation} : rtype := Foreign enhancedTimeDuration.
Definition TimePoint {br:brand_relation} : rtype := Foreign enhancedTimePoint.

Definition isFloat {model : brand_model}  (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedFloat => true
  | _ => false
  end.

Definition isTimePoint {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedTimePoint => true
  | _ => false
  end.

Definition isTimeScale {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedTimeScale => true
  | _ => false
  end.

Definition isTimeDuration {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedTimeDuration => true
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

Inductive float_unary_op_has_type {model:brand_model} :
  float_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_float_neg : float_unary_op_has_type uop_float_neg Float Float
  | tuop_float_sqrt : float_unary_op_has_type uop_float_sqrt Float Float
  | tuop_float_exp : float_unary_op_has_type uop_float_exp Float Float
  | tuop_float_log : float_unary_op_has_type uop_float_log Float Float
  | tuop_float_log10 : float_unary_op_has_type uop_float_log10 Float Float
  | tuop_float_of_int : float_unary_op_has_type uop_float_of_int Nat Float
  | tuop_float_ceil : float_unary_op_has_type uop_float_ceil Float Float
  | tuop_float_floor : float_unary_op_has_type uop_float_floor Float Float
  | tuop_float_truncate : float_unary_op_has_type uop_float_truncate Float Nat
  | tuop_float_abs : float_unary_op_has_type uop_float_abs Float Float
  | tuop_float_sum : float_unary_op_has_type uop_float_sum (Coll Float) Float
  | tuop_float_arithmean : float_unary_op_has_type uop_float_arithmean (Coll Float) Float
  | tuop_float_listmin : float_unary_op_has_type uop_float_listmin (Coll Float) Float
  | tuop_float_listmax : float_unary_op_has_type uop_float_listmax (Coll Float) Float

.

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
    - exact (Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)). 
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

Definition float_unary_op_type_infer {model : brand_model} (op:float_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_float_neg
  | uop_float_sqrt
  | uop_float_exp
  | uop_float_log
  | uop_float_log10
  | uop_float_ceil
  | uop_float_floor
  | uop_float_abs =>
    if isFloat τ₁
    then Some Float
    else None
  | uop_float_of_int =>
    if isNat τ₁
    then Some Float
    else None
  | uop_float_truncate =>
    if isFloat τ₁
    then Some Nat
    else None
  | uop_float_sum
  | uop_float_arithmean
  | uop_float_listmin
  | uop_float_listmax =>
    match tuncoll τ₁ return (option rtype) with
    | Some τ =>
      if isFloat τ
      then Some Float
      else None
    | None => None
    end
  end.

Definition float_unary_op_type_infer_sub {model : brand_model} (op:float_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_float_neg
  | uop_float_sqrt
  | uop_float_exp
  | uop_float_log
  | uop_float_log10
  | uop_float_ceil
  | uop_float_floor
  | uop_float_abs =>
    enforce_unary_op_schema (τ₁,Float) Float
  | uop_float_of_int =>
    enforce_unary_op_schema (τ₁,Nat) Float
  | uop_float_truncate =>
    enforce_unary_op_schema (τ₁,Float) Nat
  | uop_float_sum
  | uop_float_arithmean
  | uop_float_listmin
  | uop_float_listmax =>
    enforce_unary_op_schema (τ₁,Coll Float) Float
  end.

Lemma rondcollfloat_typed_some
      {model:brand_model}
      (f: list FLOAT -> FLOAT)
      (d:data) :
    d ▹ Coll Float ->
    exists z,
      rondcollfloat f d = Some z
      /\  z ▹ Float.
Proof.
  intros dt.
  invcs dt.
  assert (eqq:r = Foreign enhancedFloat)
    by (apply rtype_fequal; simpl; trivial).
  clear H.
  subst.
  revert H1.
  unfold rondcollfloat, lift; simpl; unfold lift; simpl.
  induction dl; simpl; intros F.
  - eexists; split; try reflexivity; repeat econstructor.
  - invcs F.
    invcs H1.
    invcs H3.
    simpl.
    destruct (IHdl H2) as [? [eqq typ]]; clear IHdl H2.
    unfold lift.
    destruct (rmap (fun z : data => ondfloat id z) dl); simpl;
      invcs eqq.
    eexists; split; try reflexivity; repeat econstructor.
Qed.

Lemma float_unary_op_typing_sound {model : brand_model}
      (fu : float_unary_op) (τin τout : rtype) :
  float_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      float_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
      try invcs H0;
      try invcs H3;
      simpl; unfold rondcollfloat, rondfloat; simpl;
      eexists; split; try reflexivity;
    repeat constructor
             | intros; simpl;
               apply (rondcollfloat_typed_some _ _ H0)].
Qed.

Inductive time_unary_op_has_type {model:brand_model} :
  time_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_time_to_scale : time_unary_op_has_type uop_time_to_scale TimePoint TimeScale
  | tuop_time_from_string : time_unary_op_has_type uop_time_from_string RType.String TimePoint
  | tuop_time_duration_from_string : time_unary_op_has_type uop_time_duration_from_string RType.String TimeDuration
.

Definition time_unary_op_type_infer {model : brand_model} (op:time_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_time_to_scale =>
    if isTimePoint τ₁ then Some TimeScale else None
  | uop_time_from_string =>
    if isString τ₁ then Some TimePoint else None
  | uop_time_duration_from_string =>
    if isString τ₁ then Some TimeDuration else None
  end.

Definition time_unary_op_type_infer_sub {model : brand_model} (op:time_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_time_to_scale =>
    enforce_unary_op_schema (τ₁,TimePoint) TimeScale
  | uop_time_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) TimePoint
  | uop_time_duration_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) TimeDuration
  end.

Lemma time_unary_op_typing_sound {model : brand_model}
      (fu : time_unary_op) (τin τout : rtype) :
  time_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      time_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
      try invcs H0;
      try invcs H3;
      simpl; unfold rondcollfloat, denhancedtimeduration, rondfloat; simpl;
      eexists; split; try reflexivity;
      repeat constructor].
Qed.

  Inductive enhanced_unary_op_has_type {model:brand_model} : enhanced_unary_op -> rtype -> rtype -> Prop
    :=
    | tenhanced_unary_float_op fu τin τout:
        float_unary_op_has_type fu τin τout ->
        enhanced_unary_op_has_type (enhanced_unary_float_op fu) τin τout
    | tenhanced_unary_time_op fu τin τout:
        time_unary_op_has_type fu τin τout ->
        enhanced_unary_op_has_type (enhanced_unary_time_op fu) τin τout.

  Definition enhanced_unary_op_typing_infer {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option rtype :=
    match fu with
    | enhanced_unary_float_op op => float_unary_op_type_infer op τ
    | enhanced_unary_time_op op => time_unary_op_type_infer op τ
    end.

  Lemma enhanced_unary_op_typing_infer_correct
        {model:brand_model}
        (fu:foreign_unary_op_type)
        {τ₁ τout} :
    enhanced_unary_op_typing_infer fu τ₁ = Some τout ->
    enhanced_unary_op_has_type fu τ₁ τout.
  Proof.
    intros.
    destruct fu; simpl.
    - destruct f; simpl in *;
      destruct τ₁; simpl in *; try congruence;
      destruct x; simpl in *; try congruence;
      unfold isFloat, isNat in *;
      try (destruct ft; simpl in *; try congruence;
      inversion H; subst; clear H; constructor;
      rewrite Foreign_canon;
      constructor);
      try (destruct x; simpl in *; try congruence;
      destruct ft; simpl in *; try congruence;
      inversion H; subst; clear H;
      constructor;
      assert ((exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true)
                     (Coll₀ (Foreign₀ enhancedFloat)) e) = Coll Float)
        by (apply rtype_fequal; reflexivity);
      rewrite H; clear H; constructor).
      + rewrite Nat_canon;
        inversion H; subst; clear H;
        constructor;
        constructor;
        reflexivity.
    - destruct t; simpl in *.
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
  Qed.

  Lemma enhanced_unary_op_typing_infer_least
        {model:brand_model}
        (fu:foreign_unary_op_type)
        {τ₁ τout₁ τout₂} :
    enhanced_unary_op_typing_infer fu τ₁ = Some τout₁ ->
    enhanced_unary_op_has_type fu τ₁ τout₂ ->
    τout₁ ≤ τout₂.
  Proof.
    intros.
    destruct fu; simpl in *.
    - destruct f; simpl in *;
      destruct τ₁; simpl in *; try congruence;
      destruct x; simpl in *; try congruence;
      unfold isFloat, isNat in *;
      try (destruct ft; simpl in *; try congruence;
      inversion H; subst; clear H;
      rewrite Foreign_canon in H0;
      inversion H0; subst; clear H0;
      inversion H1; subst; clear H1;
      reflexivity);
      try (destruct x; simpl in *; try congruence;
        destruct ft; simpl in *; try congruence;
        inversion H; subst; clear H;
        inversion H0; subst; clear H0;
        inversion H1; subst; clear H1;
        reflexivity).
      + inversion H; subst; clear H.
        inversion H0; subst; clear H0.
        inversion H1; subst; clear H1.
        reflexivity.
    - destruct t; simpl in *;
      destruct τ₁; simpl in *; try congruence;
      destruct x; simpl in *; try congruence;
      unfold isFloat, isNat in *.
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
  Qed.

  Lemma enhanced_unary_op_typing_infer_complete
        {model:brand_model}
        (fu:foreign_unary_op_type)
        {τ₁ τout} : 
    enhanced_unary_op_typing_infer fu τ₁ = None ->
    ~ enhanced_unary_op_has_type fu τ₁ τout.
  Proof.
    intros.
    destruct fu; simpl in *.
    - destruct f; simpl in *;
      destruct τ₁; simpl in *; try congruence;
      destruct x; simpl in *; try congruence;
      unfold isFloat, isNat in *;
      unfold not; intros;
      inversion H0; subst; simpl in *;
      inversion H2; subst; simpl in *;
      congruence.
    - destruct t; simpl in *;
      destruct τ₁; simpl in *; try congruence;
      destruct x; simpl in *; try congruence;
      unfold isFloat, isNat in *;
      unfold not; intros;
      inversion H0; subst; clear H0;
      inversion H2; subst; clear H2.
      + simpl in H; congruence.
  Qed.

  Definition enhanced_unary_op_typing_infer_sub {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option (rtype*rtype) :=
    match fu with
    | enhanced_unary_float_op op => float_unary_op_type_infer_sub op τ
    | enhanced_unary_time_op op => time_unary_op_type_infer_sub op τ
    end.

    
Lemma enhanced_unary_op_typing_sound {model : brand_model}
      (fu : foreign_unary_op_type) (τin τout : rtype) :
  enhanced_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      enhanced_unary_op_interp brand_relation_brands fu din = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply float_unary_op_typing_sound; eauto.
  - eapply time_unary_op_typing_sound; eauto.
Qed.

Instance enhanced_foreign_unary_op_typing
        {model:brand_model} :
  @foreign_unary_op_typing
    enhanced_foreign_data
    enhanced_foreign_unary_op
    enhanced_foreign_type
    enhanced_foreign_data_typing
    model
  := { foreign_unary_op_typing_has_type := enhanced_unary_op_has_type
       ; foreign_unary_op_typing_sound := enhanced_unary_op_typing_sound
       ; foreign_unary_op_typing_infer := enhanced_unary_op_typing_infer
       ; foreign_unary_op_typing_infer_correct := enhanced_unary_op_typing_infer_correct
       ; foreign_unary_op_typing_infer_least := enhanced_unary_op_typing_infer_least
       ; foreign_unary_op_typing_infer_complete := enhanced_unary_op_typing_infer_complete
       ; foreign_unary_op_typing_infer_sub := enhanced_unary_op_typing_infer_sub
     }.

Inductive float_binary_op_has_type {model:brand_model} :
  float_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tbop_float_plus :
      float_binary_op_has_type bop_float_plus Float Float Float 
  | tbop_float_minus :
      float_binary_op_has_type bop_float_minus Float Float Float 
  | tbop_float_mult :
      float_binary_op_has_type bop_float_mult  Float Float Float 
  | tbop_float_div :
      float_binary_op_has_type bop_float_div Float Float Float 
  | tbop_float_pow :
      float_binary_op_has_type bop_float_pow Float Float Float 
  | tbop_float_min :
      float_binary_op_has_type bop_float_min Float Float Float 
  | tbop_float_max :
      float_binary_op_has_type bop_float_max Float Float Float 
  | tbop_float_ne :
      float_binary_op_has_type bop_float_ne Float Float Bool 
  | tbop_float_lt :
      float_binary_op_has_type bop_float_lt Float Float Bool 
  | tbop_float_le :
      float_binary_op_has_type bop_float_le Float Float Bool 
  | tbop_float_gt :
      float_binary_op_has_type bop_float_gt Float Float Bool 
  | tbop_float_ge :
      float_binary_op_has_type bop_float_ge Float Float Bool
.

Definition float_binary_op_type_infer {model : brand_model} (op:float_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | bop_float_plus
  | bop_float_minus
  | bop_float_mult
  | bop_float_div
  | bop_float_pow
  | bop_float_min
  | bop_float_max =>
    if isFloat τ₁ && isFloat τ₂
    then Some Float
    else None
  | bop_float_ne
  | bop_float_lt
  | bop_float_le
  | bop_float_gt
  | bop_float_ge =>
    if isFloat τ₁ && isFloat τ₂
    then Some Bool
    else None
  end.

Lemma float_binary_op_typing_sound {model : brand_model}
      (fb : float_binary_op) (τin₁ τin₂ τout : rtype) :
  float_binary_op_has_type fb τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      float_binary_op_interp fb din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
    inversion 1; subst;
      inversion 1; subst;
        inversion 1; subst;
      try invcs H0;
      try invcs H1;
      invcs H3;
      invcs H4;
      simpl; unfold rondfloat2; simpl;
        eexists; split; try reflexivity;
          repeat constructor.
Qed.

Definition float_binary_op_type_infer_sub {model : brand_model} (op:float_binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype):=
  match op with
  | bop_float_plus
  | bop_float_minus
  | bop_float_mult
  | bop_float_div
  | bop_float_pow
  | bop_float_min
  | bop_float_max =>
    enforce_binary_op_schema (τ₁, Float) (τ₂, Float) Float
  | bop_float_ne
  | bop_float_lt
  | bop_float_le
  | bop_float_gt
  | bop_float_ge =>
    enforce_binary_op_schema (τ₁, Float) (τ₂, Float) Bool
  end.

Inductive time_binary_op_has_type {model:brand_model} :
  time_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tbop_time_as :
      time_binary_op_has_type bop_time_as  TimePoint TimeScale TimePoint
  | tbop_time_shift :
      time_binary_op_has_type bop_time_shift TimePoint TimeDuration TimePoint 
  | tbop_time_ne :
      time_binary_op_has_type bop_time_ne TimePoint TimePoint Bool 
  | tbop_time_lt :
      time_binary_op_has_type bop_time_lt TimePoint TimePoint Bool 
  | tbop_time_le :
      time_binary_op_has_type bop_time_le TimePoint TimePoint Bool 
  | tbop_time_gt :
      time_binary_op_has_type bop_time_gt TimePoint TimePoint Bool 
  | tbop_time_ge :
      time_binary_op_has_type bop_time_ge TimePoint TimePoint Bool
  | tbop_time_duration_from_scale :
         time_binary_op_has_type bop_time_duration_from_scale TimeScale Nat TimeDuration
  | tbop_time_duration_between  :
      time_binary_op_has_type bop_time_duration_between TimePoint TimePoint TimeDuration
.

Definition time_binary_op_type_infer {model : brand_model} (op:time_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | bop_time_as =>
    if isTimePoint τ₁ && isTimeScale τ₂ then Some TimePoint else None
  | bop_time_shift =>
    if isTimePoint τ₁ && isTimeDuration τ₂ then Some TimePoint else None
  | bop_time_ne =>
    if isTimePoint τ₁ && isTimePoint τ₂ then Some Bool else None
  | bop_time_lt =>
    if isTimePoint τ₁ && isTimePoint τ₂ then Some Bool else None
  | bop_time_le =>
    if isTimePoint τ₁ && isTimePoint τ₂ then Some Bool else None
  | bop_time_gt =>
    if isTimePoint τ₁ && isTimePoint τ₂ then Some Bool else None
  | bop_time_ge =>
    if isTimePoint τ₁ && isTimePoint τ₂ then Some Bool else None
  | bop_time_duration_from_scale =>
    if isTimeScale τ₁ && isNat τ₂ then Some TimeDuration else None
  | bop_time_duration_between  =>
    if isTimePoint τ₁ && isTimePoint τ₂ then Some TimeDuration else None
  end.

Lemma time_binary_op_typing_sound {model : brand_model}
      (fb : time_binary_op) (τin₁ τin₂ τout : rtype) :
  time_binary_op_has_type fb τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      time_binary_op_interp fb din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
    inversion 1; subst;
      inversion 1; subst;
        inversion 1; subst;
      try invcs H0;
      try invcs H1;
      invcs H3;
      try invcs H4;
      simpl; unfold rondtimepoint2; simpl;
        eexists; split; try reflexivity;
          repeat constructor.
Qed.
           
Definition time_binary_op_type_infer_sub {model : brand_model} (op:time_binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
  match op with
  | bop_time_as =>
    enforce_binary_op_schema (τ₁,TimePoint) (τ₂,TimeScale) TimePoint
  | bop_time_shift =>
    enforce_binary_op_schema (τ₁,TimePoint) (τ₂,TimeDuration) TimePoint
  | bop_time_ne
  | bop_time_lt
  | bop_time_le
  | bop_time_gt
  | bop_time_ge =>
    enforce_binary_op_schema (τ₁,TimePoint) (τ₂,TimePoint) Bool
  | bop_time_duration_from_scale =>
    enforce_binary_op_schema (τ₁,TimeScale) (τ₂,Nat) TimeDuration
  | bop_time_duration_between  =>
    enforce_binary_op_schema (τ₁,TimePoint) (τ₂,TimePoint) TimeDuration
  end.

Inductive enhanced_binary_op_has_type {model:brand_model} :
  enhanced_binary_op -> rtype -> rtype -> rtype -> Prop
    :=
    | tenhanced_binary_float_op fb τin₁ τin₂ τout:
        float_binary_op_has_type fb τin₁ τin₂ τout ->
        enhanced_binary_op_has_type (enhanced_binary_float_op fb) τin₁ τin₂ τout
    | tenhanced_binary_time_op fb τin₁ τin₂ τout:
        time_binary_op_has_type fb τin₁ τin₂ τout ->
        enhanced_binary_op_has_type (enhanced_binary_time_op fb) τin₁ τin₂ τout.

Definition enhanced_binary_op_typing_infer {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_float_op fb => float_binary_op_type_infer fb τ₁ τ₂
  | enhanced_binary_time_op fb => time_binary_op_type_infer fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_infer_correct
      {model:brand_model}
      (fb:foreign_binary_op_type)
      {τ₁ τ₂ τout} :
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  intros.
  destruct fb; simpl.
  - destruct f; simpl in *;
    destruct τ₁; destruct τ₂; simpl in *; try discriminate
    ; unfold isFloat in *
    ; destruct x; simpl in H; try discriminate
    ; destruct ft; simpl in H; try discriminate
    ; destruct x0; simpl in H; try discriminate
    ; destruct ft; simpl in H; try discriminate
    ; invcs H
    ; constructor
    ; repeat rewrite Foreign_canon
    ; constructor.
  - destruct t; simpl in *;
    destruct τ₁; destruct τ₂; simpl in *; try discriminate;
         unfold isTimePoint, isTimeScale, isTimeDuration, isNat in *
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
      (fb:foreign_binary_op_type)
      {τ₁ τ₂ τout₁ τout₂} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout₁ ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fb; simpl.
  - destruct f; simpl in *;
    destruct τ₁; destruct τ₂; simpl in *; try discriminate
    ;  unfold isFloat in *
    ; destruct x; simpl in H; try discriminate
    ; destruct ft; simpl in H; try discriminate
    ; destruct x0; simpl in H; try discriminate
    ; try (destruct ft; simpl in H; try discriminate)
    ; invcs H
    ; repeat rewrite Foreign_canon in H0
    ; invcs H0
    ; invcs H1
    ; reflexivity.
  - destruct t; simpl in *;
    destruct τ₁; destruct τ₂; simpl in *; try discriminate
    ; unfold isTimePoint, isTimeScale, isTimeDuration, isNat in *
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
      (fb:foreign_binary_op_type)
      {τ₁ τ₂ τout} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = None ->
  ~ enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  destruct fb; simpl; intros.
  - intro HH; invcs HH.
    destruct f; simpl in *; invcs H1; simpl in H; try discriminate.
  - intro HH; invcs HH.
    destruct t; simpl in *; invcs H1; simpl in H; try discriminate.
Qed.

Definition enhanced_binary_op_typing_infer_sub {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_float_op fb => float_binary_op_type_infer_sub fb τ₁ τ₂
  | enhanced_binary_time_op fb => time_binary_op_type_infer_sub fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_sound {model : brand_model}
      (fu : foreign_binary_op_type) (τin₁ τin₂ τout : rtype) :
  enhanced_binary_op_has_type fu τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      enhanced_binary_op_interp brand_relation_brands fu din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply float_binary_op_typing_sound; eauto.
  - eapply time_binary_op_typing_sound; eauto.
Qed.

Program Instance enhanced_foreign_binary_op_typing
        {model:brand_model} :
  @foreign_binary_op_typing
    enhanced_foreign_data
    enhanced_foreign_binary_op
    enhanced_foreign_type
    enhanced_foreign_data_typing
    model
  := { foreign_binary_op_typing_has_type := enhanced_binary_op_has_type
       ; foreign_binary_op_typing_sound := enhanced_binary_op_typing_sound
       ; foreign_binary_op_typing_infer := enhanced_binary_op_typing_infer
       ; foreign_binary_op_typing_infer_correct := enhanced_binary_op_typing_infer_correct
       ; foreign_binary_op_typing_infer_least := enhanced_binary_op_typing_infer_least
       ; foreign_binary_op_typing_infer_complete := enhanced_binary_op_typing_infer_complete
       ; foreign_binary_op_typing_infer_sub := enhanced_binary_op_typing_infer_sub
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
       enhanced_foreign_unary_op_typing
       enhanced_foreign_binary_op_typing.

Instance enhanced_basic_model {model:brand_model} :
  basic_model
  := mk_basic_model
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_typing.


Module EnhancedForeignType <: CompilerForeignType.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
End EnhancedForeignType.

Require Import ZArith.
Module EnhancedModel(bm:CompilerBrandModel(EnhancedForeignType)) <: CompilerModel.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_basic_model : @basic_model
    := @enhanced_basic_model bm.compiler_brand_model.
  Definition compiler_model_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_model_foreign_to_javascript : foreign_to_javascript
    := enhanced_foreign_to_javascript.
  Definition compiler_model_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_model_foreign_to_JSON : foreign_to_JSON
    := enhanced_foreign_to_JSON.
  Definition compiler_model_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_model_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_model_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_model_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_model_foreign_cloudant : foreign_cloudant
    := enhanced_foreign_cloudant.
  Definition compiler_model_foreign_to_cloudant : foreign_to_cloudant
    := enhanced_foreign_to_cloudant.
  Definition compiler_model_nra_optimizer_logger : optimizer_logger string algenv
    := foreign_nra_optimizer_logger.
  Definition compiler_model_nrc_optimizer_logger : optimizer_logger string nrc
    := foreign_nrc_optimizer_logger.
  Definition compiler_model_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedModel.

Module CompEnhanced.
  Module Enhanced.
  Module Model.
    Definition basic_model (bm:brand_model) : basic_model
      := @enhanced_basic_model bm.

    Definition foreign_type : foreign_type
      := enhanced_foreign_type.

    Definition foreign_typing (bm:brand_model) : foreign_typing
      := @enhanced_foreign_typing bm.

  End Model.

    Module Data.
      Definition dfloat (f : FLOAT) : data
        := dforeign (enhancedfloat f).
      Definition dstringblob (s : STRING) : data
        := dforeign (enhancedstring s).

      Definition jfloat (f : FLOAT) : json
        := jforeign (enhancedfloat f).
      Definition jstringblob (s : STRING) : json
        := jforeign (enhancedstring s).

      Definition scale_kind := time_scale.

      (* intended for generated coq code, to stand out and be more
          easily distinguished from variables (hackily distinguished
          that is) *)
      
      Definition SECOND : scale_kind
        := ts_second.
      Definition MINUTE : scale_kind
        := ts_minute.
      Definition HOUR : scale_kind
        := ts_hour.
      Definition DAY : scale_kind
        := ts_day.
      Definition WEEK : scale_kind
        := ts_week.
      Definition MONTH : scale_kind
        := ts_month.
      Definition YEAR  : scale_kind
        := ts_year.

      (* for use in ocaml code *)
      Definition second : scale_kind
        := ts_second.
      Definition minute : scale_kind
        := ts_minute.
      Definition hour : scale_kind
        := ts_hour.
      Definition day : scale_kind
        := ts_day.
      Definition week : scale_kind
        := ts_week.
      Definition month : scale_kind
        := ts_month.
      Definition year  : scale_kind
        := ts_year.

      Definition dtime_scale (kind:scale_kind)
        := dforeign (enhancedtimescale kind).
      
      Definition dtime_duration (td:TIME_DURATION)
        := dforeign (enhancedtimeduration td).

      Definition dtimepoint (tp:TIME_POINT) : data
        := dforeign (enhancedtimepoint tp).

    End Data.

    Module Ops.
      Module Unary.
        Definition float_neg
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_neg).
        Definition float_sqrt
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_sqrt).
        Definition float_exp
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_exp).
        Definition float_log
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_log).
        Definition float_log10
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_log10).
        Definition float_of_int
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_of_int).
        Definition float_ceil
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_ceil).
        Definition float_floor
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_floor).
        Definition float_truncate
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_truncate).
        Definition float_abs
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_abs).

        Definition float_sum
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_sum).
        Definition float_arithmean
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_arithmean).
        Definition float_listmin
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_listmin).
        Definition float_listmax
          := AForeignUnaryOp (enhanced_unary_float_op uop_float_listmax).

        Definition time_to_scale
          := AForeignUnaryOp (enhanced_unary_time_op uop_time_to_scale).
        Definition time_from_string
          := AForeignUnaryOp (enhanced_unary_time_op uop_time_from_string).
        Definition time_duration_from_string
          := AForeignUnaryOp (enhanced_unary_time_op uop_time_duration_from_string).

        (* for coq style syntax *)
        Definition AFloatNeg := float_neg.
        Definition AFloatSqrt := float_sqrt.
        Definition AFloatExp := float_exp.
        Definition AFloatLog := float_log.
        Definition AFloatLog10 := float_log10.
        Definition AFloatOfInt := float_of_int.
        Definition AFloatCeil := float_ceil.
        Definition AFloatFloor := float_floor.
        Definition AFloatTruncate := float_truncate.
        Definition AFloatAbs := float_abs.

        Definition AFloatSum := float_sum.
        Definition AFloatArithMean := float_arithmean.
        Definition AFloatListMin := float_listmin.
        Definition AFloatListMax := float_listmax.

        Definition ATimeToSscale := time_to_scale.
        Definition ATimeFromString := time_from_string.
        Definition ATimeDurationFromString := time_duration_from_string.

      End Unary.
      
      Module Binary.
        Definition float_plus
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_plus).
        Definition float_minus
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_minus).
        Definition float_mult 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_mult).
        Definition float_div 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_div).
        Definition float_pow 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_pow).
        Definition float_min 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_min).
        Definition float_max 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_max).
        Definition float_ne 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_ne).
        Definition float_lt 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_lt).
        Definition float_le 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_le).
        Definition float_gt 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_gt).
        Definition float_ge 
          := AForeignBinaryOp (enhanced_binary_float_op bop_float_ge).

        (* for ocaml *)
        Definition time_as
          := AForeignBinaryOp (enhanced_binary_time_op bop_time_as).
        Definition time_shift
          := AForeignBinaryOp (enhanced_binary_time_op bop_time_shift).
        Definition time_ne 
          := AForeignBinaryOp (enhanced_binary_time_op bop_time_ne).
        Definition time_lt 
          := AForeignBinaryOp (enhanced_binary_time_op bop_time_lt).
        Definition time_le 
          := AForeignBinaryOp (enhanced_binary_time_op bop_time_le).
        Definition time_gt 
          := AForeignBinaryOp (enhanced_binary_time_op bop_time_gt).
        Definition time_ge 
          := AForeignBinaryOp (enhanced_binary_time_op bop_time_ge).

        Definition time_duration_from_scale 
          := AForeignBinaryOp (enhanced_binary_time_op (bop_time_duration_from_scale)).               
        Definition time_duration_between 
          := AForeignBinaryOp (enhanced_binary_time_op (bop_time_duration_between)).
        
        (* for coq style syntax *)
        Definition AFloatPlus := float_plus.
        Definition AFloatMinus := float_minus.
        Definition AFloatMult  := float_mult .
        Definition AFloatDiv  := float_div .
        Definition AFloatPow  := float_pow .
        Definition AFloatMin  := float_min .
        Definition AFloatMax  := float_max .
        Definition AFloatNe  := float_ne .
        Definition AFloatLt  := float_lt .
        Definition AFloatLe  := float_le .
        Definition AFloatGt  := float_gt .
        Definition AFloatGe  := float_ge .

        Definition ATimeAs := time_as.
        Definition ATimeShift := time_shift.
        Definition ATimeNe := time_ne.
        Definition ATimeLt := time_lt.
        Definition ATimeLe := time_le.
        Definition ATimeGt := time_gt.
        Definition ATimeGe := time_ge.

        Definition ATimeDurationFromScale := time_duration_from_scale.
        Definition ATimeDurationBetween := time_duration_between.
        
      End Binary.
    End Ops.
  End Enhanced.
End CompEnhanced.  

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
