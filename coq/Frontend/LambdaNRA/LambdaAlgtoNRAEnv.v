Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.

Require Import Utils BasicRuntime.

Section LambdaNRAtoNRAEnv.

  Require Import LambdaAlg NRAEnvRuntime.

  Context {fruntime:foreign_runtime}.

  Fixpoint algenv_of_lalg (op:lalg) : algenv :=
    match op with
    | LAVar x => ANUnop (ADot x) ANEnv
    | LAConst d => ANConst d
    | LABinop b op1 op2 => ANBinop b (algenv_of_lalg op1) (algenv_of_lalg op2)
    | LAUnop u op1 => ANUnop u (algenv_of_lalg op1)
    | LAMap lop1 op2 => ANMap (algenv_of_lalg_lambda lop1) (algenv_of_lalg op2)
    | LAMapConcat lop1 op2 => ANMapConcat (algenv_of_lalg_lambda lop1) (algenv_of_lalg op2)
    | LAProduct op1 op2 => ANProduct (algenv_of_lalg op1) (algenv_of_lalg op2)
    | LASelect lop1 op2 => ANSelect (algenv_of_lalg_lambda lop1) (algenv_of_lalg op2)
    end
  with algenv_of_lalg_lambda (lop:lalg_lambda) : algenv :=
    match lop with
    | LALambda x op =>
      ANAppEnv (algenv_of_lalg op) (ANBinop AConcat ANEnv (ANUnop (ARec x) ANID))
    end.

  Context (h:brand_relation_t).
    
  Theorem algenv_of_lalg_lambda_correct (env:bindings) (lop:lalg_lambda) (d:data) :
    fun_of_lalg_lambda h env lop d = fun_of_algenv h nil (algenv_of_lalg_lambda lop) (drec env) d.
  Proof.
    destruct lop.
    revert env s d.
    lalg_cases (induction l) Case
    ; intros; simpl in *
    ; autorewrite with lalg.
    - Case "LAVar"%string.
      unfold edot, rec_concat_sort.
      rewrite assoc_lookupr_drec_sort.
      trivial.
    - Case "LAConst"%string.
      trivial.
    - Case "LABinop"%string.
      rewrite <- IHl1, <- IHl2.
      trivial.
    - Case "LAUnop"%string.
      rewrite <- IHl.
      trivial.
    - Case "LAMap"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply rmap_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
    - Case "LAMapConcat"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply rmap_concat_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
    - Case "LAProduct"%string.
      rewrite <- IHl1, <- IHl2.
      trivial.
    - Case "LASelect"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply lift_filter_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
  Qed.
      
  Definition eval_nraenv_q (Qe:algenv) (input:data) : option data :=
    fun_of_algenv h nil Qe (drec nil) input.

  Theorem eval_nraenv_q_correct (Q:lalg -> lalg) (input:data) :
    eval_q h Q input = eval_nraenv_q (algenv_of_lalg_lambda (q_to_lambda Q)) input.
  Proof.
    unfold eval_q, eval_nraenv_q.
    rewrite algenv_of_lalg_lambda_correct.
    reflexivity.
  Qed.

End LambdaNRAtoNRAEnv.

  (* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
