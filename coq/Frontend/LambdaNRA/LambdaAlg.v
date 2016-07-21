Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.

Require Import Utils BasicRuntime.
Section LambdaNRA.

  Context {fruntime:foreign_runtime}.

  Unset Elimination Schemes.

  (* Lambda NRA *)
  Inductive lalg : Set :=
  | LAVar : string -> lalg (* Variable access *)
  | LAConst : data -> lalg
  | LABinop : binOp -> lalg -> lalg -> lalg
  | LAUnop : unaryOp -> lalg -> lalg
  | LAMap : lalg_lambda -> lalg -> lalg (* 'dependent operators' use lambdas *)
  | LAMapConcat : lalg_lambda -> lalg -> lalg
  | LAProduct : lalg -> lalg -> lalg
  | LASelect : lalg_lambda -> lalg -> lalg
  with lalg_lambda : Set :=
  | LALambda : string -> lalg -> lalg_lambda (* Lambda is (\var.alg) *)
  .

  Tactic Notation "lalg_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LAVar"%string
  | Case_aux c "LAConst"%string
  | Case_aux c "LABinop"%string
  | Case_aux c "LAUnop"%string
  | Case_aux c "LAMap"%string
  | Case_aux c "LAMapConcat"%string
  | Case_aux c "LAProduct"%string
  | Case_aux c "LASelect"%string
  ].
  
  Set Elimination Schemes.

  (* The language is defined via mutual recursion, but it is easier to 
     unfold it for reasoning. *)
  Definition  lalg_rect
              (P : lalg -> Type)
              (fvar : forall s : string, P (LAVar s))
              (fconst : forall d : data, P (LAConst d))
              (fbinop : forall (b : binOp) (l : lalg), P l -> forall l0 : lalg, P l0 -> P (LABinop b l l0))
              (funop : forall (u : unaryOp) (l : lalg), P l -> P (LAUnop u l))
              (fmap : forall (s:string) (l0 l1 : lalg), P l0 -> P l1 -> P (LAMap (LALambda s l0) l1))
              (fmapconcat : forall (s:string) (l0 l1 : lalg), P l0 -> P l1 -> P (LAMapConcat (LALambda s l0) l1))
              (fproduct : forall l : lalg, P l -> forall l0 : lalg, P l0 -> P (LAProduct l l0))
              (fselect : forall (s:string) (l0 l1 : lalg), P l0 -> P l1 -> P (LASelect (LALambda s l0) l1)) :
    forall l, P l
    := 
      fix F (l : lalg) : P l :=
        match l as l0 return (P l0) with
        | LAVar s => fvar s
        | LAConst d => fconst d
        | LABinop b l0 l1 => fbinop b l0 (F l0) l1 (F l1)
        | LAUnop u l0 => funop u l0 (F l0)
        | LAMap (LALambda s l0) l1 => fmap s l0 l1 (F l0) (F l1)
        | LAMapConcat (LALambda s l0) l1 => fmapconcat s l0 l1 (F l0) (F l1)
        | LAProduct l0 l1 => fproduct l0 (F l0) l1 (F l1)
        | LASelect (LALambda s l0) l1 => fselect s l0 l1 (F l0) (F l1)
        end.

  Definition lalg_ind (P : lalg -> Prop) := lalg_rect P.
  Definition lalg_rec (P:lalg->Set) := lalg_rect P.

  Context (h:brand_relation_t).

  Fixpoint fun_of_lalg (env: bindings) (op:lalg) : option data :=
    match op with
    | LAVar x => edot env x
    | LAConst d => Some (normalize_data h d)
    | LABinop b op1 op2 => olift2 (fun d1 d2 => fun_of_binop h b d1 d2) (fun_of_lalg env op1) (fun_of_lalg env op2)
    | LAUnop u op1 =>
      olift (fun d1 => fun_of_unaryop h u d1) (fun_of_lalg env op1)
    | LAMap lop1 op2 =>
        let aux_map d :=
            lift_oncoll (fun c1 => lift dcoll (rmap (fun_of_lalg_lambda env lop1) c1)) d
        in olift aux_map (fun_of_lalg env op2)
    | LAMapConcat lop1 op2 =>
      let aux_mapconcat d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun_of_lalg_lambda env lop1) c1)) d
      in olift aux_mapconcat (fun_of_lalg env op2)
    | LAProduct op1 op2 =>
      (* Note: it's even clearer from this formulation that both branches take the same environment *)
      let aux_product d :=
          lift_oncoll (fun c1 => lift dcoll (rmap_concat (fun _ => fun_of_lalg env op2) c1)) d
      in olift aux_product (fun_of_lalg env op1)
    | LASelect lop1 op2 =>
      let pred x' :=
          match fun_of_lalg_lambda env lop1 x' with
          | Some (dbool b) => Some b
          | _ => None
          end
      in
      let aux_select d :=
          lift_oncoll (fun c1 => lift dcoll (lift_filter pred c1)) d
      in
      olift aux_select (fun_of_lalg env op2)
    end
  with fun_of_lalg_lambda (env:bindings) (lop:lalg_lambda) (d:data) : option data :=
    match lop with
    | LALambda x op =>
      (fun_of_lalg (env++((x,d)::nil)) op)
    end.

  (* For top-level: Parametric query *)
  Definition q_to_lambda (Q:lalg -> lalg) :=
    (LALambda "input" (Q (LAVar "input"))).

  Definition eval_q (Q:lalg -> lalg) (input:data) : option data :=
    fun_of_lalg_lambda nil (q_to_lambda Q) input.

End LambdaNRA.

Tactic Notation "lalg_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "LAVar"%string
  | Case_aux c "LAConst"%string
  | Case_aux c "LABinop"%string
  | Case_aux c "LAUnop"%string
  | Case_aux c "LAMap"%string
  | Case_aux c "LAMapConcat"%string
  | Case_aux c "LAProduct"%string
  | Case_aux c "LASelect"%string
  ].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
