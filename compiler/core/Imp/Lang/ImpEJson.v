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

(** Imp with the Json data model *)

Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import EJsonRuntime.
Require Import Imp.

Section ImpEJson.
  Context {ftoejson:foreign_ejson}.
  Context {fejruntime:foreign_ejson_runtime}.

  Section Syntax.
    Definition imp_ejson_model := ejson.
    Definition imp_ejson_constant := cejson.

    (* XXX This should contain at least:
       - all JS operators/expressions used in translation from NNRSimp to JsAst
       - all JS operators/expressions used to manipulate values in data but not in json (brands, nat, left, right, foreign)
       imp_ejson_op constructors names are based on JsAst names
       imp_ejson_runtime_op constructors names are in the JS Qcert runtime
     *)
    Definition imp_ejson_op := ejson_op. (* See ./EJson/Operators/EJsonOperators.v *)
    Definition imp_ejson_runtime_op := ejson_runtime_op.  (* See ./EJson/Operators/EJsonRuntimeOperators.v *)
    Definition imp_ejson_expr := @imp_expr imp_ejson_constant imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson_stmt := @imp_stmt imp_ejson_constant imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson_function := @imp_function imp_ejson_constant imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson := @imp imp_ejson_constant imp_ejson_op imp_ejson_runtime_op.

  End Syntax.

  Section dec.
    (** Equality is decidable for json *)
    Lemma cejson_eq_dec : forall x y:cejson, {x=y}+{x<>y}.
    Proof.
      induction x; destruct y; try solve[right; inversion 1].
      - left; trivial.
      - destruct (float_eq_dec f f0).
        + left; f_equal; trivial.
        + right;intro;apply c;inversion H; reflexivity.
      - destruct (Z.eq_dec z z0).
        + left; f_equal; trivial.
        + right;intro;apply n;inversion H; trivial.
      - destruct (bool_dec b b0).
        + left; f_equal; trivial.
        + right;intro;apply n;inversion H; trivial. 
      - destruct (string_dec s s0).
        + left; f_equal; trivial.
        + right;intro;apply n;inversion H; trivial.
      - destruct (foreign_ejson_dec f f0).
        + left. f_equal; apply e.
        + right. inversion 1; congruence.
    Defined.

    (* begin hide *)
    Global Instance cejson_eqdec : EqDec cejson eq := cejson_eq_dec.
    (* begin hide *)

    Global Instance imp_ejson_constant_eqdec : EqDec imp_ejson_constant eq.
    Proof.
      apply cejson_eqdec.
    Qed.

    Global Instance imp_ejson_op_eqdec : EqDec imp_ejson_op eq.
    Proof.
      change (forall x y : imp_ejson_op,  {x = y} + {x <> y}).
      decide equality.
      - revert l0; induction l; intros; destruct l0; simpl in *; try solve[right; inversion 1].
        left; reflexivity.
        elim (IHl l0); intros; clear IHl.
        + subst; destruct (string_dec a s); subst; [left; reflexivity| right; congruence].
        + right; congruence.
      - apply string_eqdec.
      - apply string_eqdec.
    Qed.

    Global Instance imp_ejson_runtime_op_eqdec : EqDec imp_ejson_runtime_op eq.
    Proof.
      change (forall x y : imp_ejson_runtime_op,  {x = y} + {x <> y}).
      decide equality.
      apply foreign_ejson_runtime_op_dec.
    Qed.

    Global Instance imp_ejson_expr_eqdec : EqDec imp_ejson_expr eq.
    Proof.
      apply (@imp_expr_eqdec imp_ejson_constant imp_ejson_op imp_ejson_runtime_op).
      apply imp_ejson_constant_eqdec.
      apply imp_ejson_op_eqdec.
      apply imp_ejson_runtime_op_eqdec.
    Qed.
  End dec.

End ImpEJson.
