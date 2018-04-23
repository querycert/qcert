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
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.

Section OQL.
  Context {fruntime:foreign_runtime}.

  Definition oql_env := list (string * data).

  Unset Elimination Schemes.
  
  Inductive oql_expr : Set :=
  | OConst : data -> oql_expr
  | OVar : string -> oql_expr
  | OTable : string -> oql_expr
  | OBinop : binary_op -> oql_expr -> oql_expr -> oql_expr
  | OUnop : unary_op -> oql_expr -> oql_expr
  | OSFW : oql_select_expr -> (list oql_in_expr) -> oql_where_expr -> oql_order_by_expr -> oql_expr
  with oql_select_expr : Set :=
  | OSelect : oql_expr -> oql_select_expr
  | OSelectDistinct : oql_expr -> oql_select_expr
  with oql_in_expr : Set :=
  | OIn : string -> oql_expr -> oql_in_expr
  | OInCast : string -> string -> oql_expr -> oql_in_expr
  with oql_where_expr : Set :=
  | OTrue : oql_where_expr
  | OWhere : oql_expr -> oql_where_expr
  with oql_order_by_expr : Set :=
  | ONoOrder : oql_order_by_expr
  | OOrderBy : oql_expr -> SortDesc -> oql_order_by_expr
  .

  Set Elimination Schemes.

  Inductive oql_query_program : Set :=
  | ODefineQuery : string -> oql_expr -> oql_query_program -> oql_query_program
  | OUndefineQuery : string -> oql_query_program -> oql_query_program
  | OQuery : oql_expr -> oql_query_program
  .

  Definition oql : Set := oql_query_program.
  
  Definition oselect_expr (ie:oql_select_expr) : oql_expr :=
    match ie with
    | OSelect e => e
    | OSelectDistinct e => e
    end.
  
  Definition oin_expr (ie:oql_in_expr) : oql_expr :=
    match ie with
    | OIn _ e => e
    | OInCast _ _ e => e
    end.
  
  (** Induction principles used as backbone for inductive proofs on oql *)
  Definition oql_expr_rect (P : oql_expr -> Type)
             (fconst : forall d : data, P (OConst d))
             (fvar : forall v : string, P (OVar v))
             (ftable : forall t : string, P (OTable t))
             (fbinop : forall b : binary_op,
                 forall e1 e2 : oql_expr, P e1 -> P e2 -> P (OBinop b e1 e2))
             (funop : forall u : unary_op,
                 forall e1 : oql_expr, P e1 -> P (OUnop u e1))
             (fswf1 : forall e1 : oql_select_expr, forall el : list oql_in_expr,
                   P (oselect_expr e1) -> Forallt (fun ab => P (oin_expr ab)) el -> P (OSFW e1 el OTrue ONoOrder))
             (fswf2 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall ew : oql_expr,
                   P (oselect_expr e1) -> Forallt (fun ab => P (oin_expr ab)) el -> P ew -> P (OSFW e1 el (OWhere ew) ONoOrder))
             (fswf3 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall eob : oql_expr, forall sc : SortDesc,
                   P (oselect_expr e1) -> Forallt (fun ab => P (oin_expr ab)) el -> P eob -> P (OSFW e1 el OTrue (OOrderBy eob sc)))
             (fswf4 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall ew : oql_expr, forall eob : oql_expr, forall sc : SortDesc,
                   P (oselect_expr e1) -> Forallt (fun ab => P (oin_expr ab)) el -> P ew -> P eob -> P (OSFW e1 el (OWhere ew) (OOrderBy eob sc)))
    :=
      fix F (e : oql_expr) : P e :=
    match e as e0 return (P e0) with
      | OConst d => fconst d
      | OVar v => fvar v
      | OTable t => ftable t
      | OBinop b e1 e2 => fbinop b _ _ (F e1) (F e2)
      | OUnop u e1 => funop u _ (F e1)
      | OSFW e1 el OTrue ONoOrder =>
        fswf1 _ el (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forallt (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forallt_nil _
                  | cons sd c0 => @Forallt_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
      | OSFW e1 el (OWhere ew) ONoOrder =>
        fswf2 _ el _ (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forallt (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forallt_nil _
                  | cons sd c0 => @Forallt_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
              (F ew)
      | OSFW e1 el OTrue (OOrderBy eob sc) =>
        fswf3 _ el _ _ (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forallt (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forallt_nil _
                  | cons sd c0 => @Forallt_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
              (F eob)
      | OSFW e1 el (OWhere ew) (OOrderBy eob sc) =>
        fswf4 _ el _ _ _ (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forallt (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forallt_nil _
                  | cons sd c0 => @Forallt_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
              (F ew)
              (F eob)
    end.

  Definition oql_expr_ind (P : oql_expr -> Prop)
             (fconst : forall d : data, P (OConst d))
             (fvar : forall v : string, P (OVar v))
             (ftable : forall t : string, P (OTable t))
             (fbinop : forall b : binary_op,
                 forall e1 e2 : oql_expr, P e1 -> P e2 -> P (OBinop b e1 e2))
             (funop : forall u : unary_op,
                 forall e1 : oql_expr, P e1 -> P (OUnop u e1))
             (fswf1 : forall e1 : oql_select_expr, forall el : list oql_in_expr,
                   P (oselect_expr e1) -> Forall (fun ab => P (oin_expr ab)) el -> P (OSFW e1 el OTrue ONoOrder))
             (fswf2 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall ew : oql_expr,
                   P (oselect_expr e1) -> Forall (fun ab => P (oin_expr ab)) el -> P ew -> P (OSFW e1 el (OWhere ew) ONoOrder))
             (fswf3 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall eob : oql_expr, forall sc : SortDesc,
                   P (oselect_expr e1) -> Forall (fun ab => P (oin_expr ab)) el -> P eob -> P (OSFW e1 el OTrue (OOrderBy eob sc)))
             (fswf4 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall ew : oql_expr, forall eob : oql_expr, forall sc : SortDesc,
                   P (oselect_expr e1) -> Forall (fun ab => P (oin_expr ab)) el -> P ew -> P eob -> P (OSFW e1 el (OWhere ew) (OOrderBy eob sc)))
    :=
      fix F (e : oql_expr) : P e :=
    match e as e0 return (P e0) with
      | OConst d => fconst d
      | OVar v => fvar v
      | OTable t => ftable t
      | OBinop b e1 e2 => fbinop b _ _ (F e1) (F e2)
      | OUnop u e1 => funop u _ (F e1)
      | OSFW e1 el OTrue ONoOrder =>
        fswf1 _ el (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forall (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forall_nil _
                  | cons sd c0 => @Forall_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
      | OSFW e1 el (OWhere ew) ONoOrder =>
        fswf2 _ el _ (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forall (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forall_nil _
                  | cons sd c0 => @Forall_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
              (F ew)
      | OSFW e1 el OTrue (OOrderBy eob sc) =>
        fswf3 _ el _ _ (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forall (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forall_nil _
                  | cons sd c0 => @Forall_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
              (F eob)
      | OSFW e1 el (OWhere ew) (OOrderBy eob sc) =>
        fswf4 _ el _ _ _ (F (oselect_expr e1))
              ((fix F1 (r : list oql_in_expr) : Forall (fun ab => P (oin_expr ab)) r :=
                  match r as c0 with
                  | nil => Forall_nil _
                  | cons sd c0 => @Forall_cons _ (fun ab => P (oin_expr ab)) sd c0 (F (oin_expr sd)) (F1 c0)
                  end) el)
              (F ew)
              (F eob)
    end.

  Definition oql_expr_rec (P:oql_expr->Set) := oql_expr_rect P.
  
  Lemma oql_expr_ind2 (P : oql_expr -> Prop)
             (fconst : forall d : data, P (OConst d))
             (fvar : forall v : string, P (OVar v))
             (ftable : forall t : string, P (OTable t))
             (fbinop : forall b : binary_op,
                 forall e1 e2 : oql_expr, P e1 -> P e2 -> P (OBinop b e1 e2))
             (funop : forall u : unary_op,
                 forall e1 : oql_expr, P e1 -> P (OUnop u e1))
             (fswf1 : forall e1 : oql_select_expr, forall el : list oql_in_expr,
                   P (oselect_expr e1) -> (forall ab, In ab el -> P (oin_expr ab)) -> P (OSFW e1 el OTrue ONoOrder))
             (fswf2 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall ew : oql_expr,
                     P (oselect_expr e1) -> (forall ab, In ab el -> P (oin_expr ab)) -> P ew -> P (OSFW e1 el (OWhere ew) ONoOrder))
             (fswf3 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall eob : oql_expr, forall sc : SortDesc,
                   P (oselect_expr e1) -> (forall ab, In ab el -> P (oin_expr ab)) -> P eob -> P (OSFW e1 el OTrue (OOrderBy eob sc)))
             (fswf4 : forall e1 : oql_select_expr, forall el : list oql_in_expr, forall ew : oql_expr, forall eob : oql_expr, forall sc : SortDesc,
                     P (oselect_expr e1) -> (forall ab, In ab el -> P (oin_expr ab)) -> P ew -> P eob -> P (OSFW e1 el (OWhere ew) (OOrderBy eob sc))) :
    forall e, P e.
  Proof.
    intros.
    apply oql_expr_ind; trivial.
    - intros. rewrite Forall_forall in H0.
      auto.
    - intros. rewrite Forall_forall in H0.
      auto.
    - intros. rewrite Forall_forall in H0.
      auto.
    - intros. rewrite Forall_forall in H0.
      auto.
  Qed.

  Global Instance oql_expr_eqdec : EqDec oql_expr eq.  
  Proof.
    change (forall x y : oql_expr,  {x = y} + {x <> y}).
    induction x; destruct y; try solve[right; inversion 1].
    - destruct (data_eqdec d d0).
      + left; rewrite e; reflexivity.
      + right; congruence.
    - destruct (string_dec v s).
      + subst. left; trivial.
      + right; congruence.
    - destruct (string_dec t s).
      + subst. left; trivial.
      + right; congruence.
    - destruct (b == b0); unfold equiv, complement in *.
      + subst; destruct (IHx1 y1); destruct (IHx2 y2); subst.
        * left; congruence.
        * right; congruence.
        * right; congruence.
        * right; congruence.
      + right; congruence.
    - destruct (u == u0); unfold equiv, complement in *.
      + subst; destruct (IHx y); [left|right]; congruence.
      + right; congruence.
    - destruct o0; simpl; [|right; congruence].
      destruct e1; destruct o; simpl in *; try (right; congruence).
      + destruct (IHx o); try (right; congruence); subst; clear IHx.
        revert l; induction el; intros; destruct l; simpl in *; try solve[right; inversion 1].
        destruct o1; [left; reflexivity|right; congruence].
        inversion H; subst; simpl in *.
        specialize (IHel H3); clear H.
        destruct a; destruct o0; simpl in *;
        destruct (H2 o0); subst; try (right;congruence).
        * destruct (string_dec s s0); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
        * destruct (string_dec s s1); destruct (string_dec s0 s2); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
      + destruct (IHx o); try (right; congruence); subst; clear IHx.
        revert l; induction el; intros; destruct l; simpl in *; try solve[right; inversion 1].
        destruct o1; [left; reflexivity|right; congruence].
        inversion H; subst; simpl in *.
        specialize (IHel H3); clear H.
        destruct a; destruct o0; simpl in *;
        destruct (H2 o0); subst; try (right;congruence).
        * destruct (string_dec s s0); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
        * destruct (string_dec s s1); destruct (string_dec s0 s2); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
    - destruct o0; simpl; try (right; congruence).
      destruct (IHx0 o0); try (right; congruence); subst.
      destruct e1; destruct o; simpl in *; try (right; congruence).
      + destruct (IHx o); try (right; congruence); subst; clear IHx.
        revert l; induction el; intros; destruct l; simpl in *; try solve[right; inversion 1].
        destruct o1; [left; reflexivity|right; congruence].
        inversion H; subst; simpl in *.
        specialize (IHel H3); clear H.
        destruct a; destruct o2; simpl in *;
        destruct (H2 o2); subst; try (right;congruence).
        * destruct (string_dec s s0); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
        * destruct (string_dec s s1); destruct (string_dec s0 s2); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
      + destruct (IHx o); try (right; congruence); subst; clear IHx.
        revert l; induction el; intros; destruct l; simpl in *; try solve[right; inversion 1].
        destruct o1; [left; reflexivity|right; congruence].
        inversion H; subst; simpl in *.
        specialize (IHel H3); clear H.
        destruct a; destruct o2; simpl in *;
        destruct (H2 o2); subst; try (right;congruence).
        * destruct (string_dec s s0); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
        * destruct (string_dec s s1); destruct (string_dec s0 s2); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
    - destruct o0; simpl; [|right; congruence].
      destruct e1; destruct o; simpl in *; try (right; congruence).
      + destruct (IHx o); try (right; congruence); subst; clear IHx.
        revert l; induction el; intros; destruct l; simpl in *; try solve[right; inversion 1].
        destruct o1; [right;congruence|].
        destruct s; destruct sc; try (right; congruence).
        destruct (IHx0 o0); try (right; congruence); subst; clear IHx0; left; reflexivity.
        destruct (IHx0 o0); try (right; congruence); subst; clear IHx0; left; reflexivity.
        inversion H; subst; simpl in *.
        specialize (IHel H3); clear H.
        destruct a; destruct o0; simpl in *;
        destruct (H2 o0); subst; try (right;congruence).
        * destruct (string_dec s s0); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
        * destruct (string_dec s s1); destruct (string_dec s0 s2); subst; 
          destruct (IHel l); try (inversion e; subst; left; reflexivity);
          right; congruence.
      + destruct (IHx o); try (right; congruence); subst; clear IHx.
        revert l; induction el; intros; destruct l; simpl in *; try solve[right; inversion 1].
        destruct o1; [right;congruence|].
        destruct s; destruct sc; try (right; congruence).
        destruct (IHx0 o0); try (right; congruence); subst; clear IHx0; left; reflexivity.
        destruct (IHx0 o0); try (right; congruence); subst; clear IHx0; left; reflexivity.
        destruct o1; [right;congruence|].
        destruct s; destruct sc; try (right; congruence).
        * destruct (IHx0 o1); try (right; congruence); subst; clear IHx0.
          inversion H; subst; simpl in *.
          specialize (IHel H3); clear H.
          destruct a; destruct o0; simpl in *;
          destruct (H2 o0); subst; try (right;congruence);
          [destruct (string_dec s s0); subst; 
           destruct (IHel l); try (inversion e; subst; left; reflexivity);
           right; congruence|
           destruct (string_dec s s1); destruct (string_dec s0 s2); subst; 
           destruct (IHel l); try (inversion e; subst; left; reflexivity);
           right; congruence].
        * destruct (IHx0 o1); try (right; congruence); subst; clear IHx0.
          inversion H; subst; simpl in *.
          specialize (IHel H3); clear H.
          destruct a; destruct o0; simpl in *;
          destruct (H2 o0); subst; try (right;congruence);
          [destruct (string_dec s s0); subst; 
           destruct (IHel l); try (inversion e; subst; left; reflexivity);
           right; congruence|
           destruct (string_dec s s1); destruct (string_dec s0 s2); subst; 
           destruct (IHel l); try (inversion e; subst; left; reflexivity);
           right; congruence].
    - destruct o0; simpl; try (right; congruence).
      assert (dec1:{e1 = o} + {e1 <> o}).
      {
        destruct e1; destruct o; try solve [right; inversion 1; congruence].
        - destruct (IHx1 (oselect_expr (OSelect o))); simpl in *.
          + subst; auto.
          + right; inversion 1; congruence.
        - destruct (IHx1 (oselect_expr (OSelect o))); simpl in *.
          + subst; auto.
          + right; inversion 1; congruence.
      }
      destruct dec1; try solve [right; inversion 1; congruence]; subst.

      assert (dec2:{el = l} + {el <> l}).
         {
           apply list_Forallt_eq_dec.
           apply (forallt_impl H).
           apply forallt_weaken; intros.
           destruct x; destruct y; try solve [right; discriminate].
           - simpl in H0
             ; destruct (string_dec s s0); try solve [right; inversion 1; congruence]
             ; subst
             ; destruct (H0 o3); [left|right;inversion 1]; congruence.
           - simpl in H0
            ; destruct (string_dec s s1); try solve [right; inversion 1; congruence]
            ; destruct (string_dec s0 s2); try solve [right; inversion 1; congruence]
            ; subst
            ; destruct (H0 o3); [left|right;inversion 1]; congruence.
         }
         destruct dec2; try solve [right; inversion 1; congruence]; subst.
         
         destruct (IHx2 o0); try solve [right; inversion 1; congruence]; subst.

         destruct o1; try solve [right; inversion 1; congruence].
         destruct (IHx3 o1); try solve [right; inversion 1; congruence]; subst.
         destruct (sort_desc_eq_dec sc s); try solve [right; inversion 1; congruence]; subst.
         left; trivial.
  Defined.

  Global Instance oql_select_expr_eqdec : EqDec oql_select_expr eq.
  Proof.
    red; destruct x; destruct y; try solve [right; congruence].
    - destruct (o == o0); [left|right]; congruence.
    - destruct (o == o0); [left|right]; congruence.
  Defined.

  Global Instance oql_in_expr_eqdec : EqDec oql_in_expr eq.
  Proof.
    red; destruct x; destruct y; try solve [right; congruence].
    - destruct (string_dec s s0); try solve [right; inversion 1; congruence]; subst.
      destruct (o == o0); [left|right]; congruence.
    - destruct (string_dec s s1); try solve [right; inversion 1; congruence]; subst.
      destruct (string_dec s0 s2); try solve [right; inversion 1; congruence]; subst.
      destruct (o == o0); [left|right]; congruence.
  Defined.

  Global Instance oql_where_expr_eqdec : EqDec oql_where_expr eq.
  Proof.
    red; destruct x; destruct y; try solve [right; congruence].
    - left; reflexivity.
    - destruct (o == o0); [left|right]; congruence.
  Defined.

  Global Instance oql_order_by_expr_eqdec : EqDec oql_order_by_expr eq.
  Proof.
    red; destruct x; destruct y; try solve [right; congruence].
    - left; reflexivity.
    - destruct (o == o0); try solve [right; inversion 1; congruence]; subst.
      destruct (s == s0); [left|right]; congruence.
  Defined.

  Global Instance oql_query_program_eqdec : EqDec oql_query_program eq.
  Proof.
    red; induction x; destruct y; try solve [right; congruence].
    - destruct (s == s0); [ | right; congruence].
      destruct (o == o0); [ | right; congruence].
      destruct (IHx y); [ | right; congruence].
      left; congruence.
    - destruct (s == s0); [ | right; congruence].
      destruct (IHx y); [ | right; congruence].
      left; congruence.
    - destruct (o == o0); [left|right]; congruence.
  Defined.

  Global Instance oql_eqdec : EqDec oql eq.
  Proof.
    apply oql_query_program_eqdec.
  Defined.

  (** Semantics of OQL *)

  Context (h:brand_relation_t).
  Section sem.
  Context (constant_env:list (string*data)).

  Definition env_map_concat_single (a:oql_env) (xl:list oql_env) : list oql_env :=
    map (fun x => rec_concat_sort a x) xl.

  Definition oenv_map_concat_single
             (v:string)
             (f:oql_env -> option data)
             (a:oql_env) : option (list oql_env) :=
    match f a with
      | Some (dcoll y) => Some (env_map_concat_single a (map (fun x => ((v,x)::nil)) y))
      | _ => None
    end.

  Definition filter_cast (b:brands) (l:list data) :=
    let apply_cast x :=
        match x with
        | dbrand b' _ =>
          if (sub_brands_dec h b' b)
          then Some (x :: nil)
          else Some nil
        | _ => None
        end
    in
    lift_flat_map apply_cast l.

  Definition oenv_map_concat_single_with_cast
             (v:string)
             (brand_name:string)
             (f:oql_env -> option data)
             (a:oql_env) : option (list oql_env) :=
    match f a with
    | Some (dcoll y) =>
      match filter_cast (brand_name::nil) y with
      | Some y =>
        Some (env_map_concat_single a (map (fun x => ((v,x)::nil)) y))
      | None => None
      end
    | _ => None
    end.

  Definition env_map_concat
             (v:string)
             (f:oql_env -> option data)
             (d:list oql_env) : option (list oql_env) :=
    lift_flat_map (oenv_map_concat_single v f) d.

  Definition env_map_concat_cast
             (v:string)
             (brand_name:string)
             (f:oql_env -> option data)
             (d:list oql_env) : option (list oql_env) :=
    lift_flat_map (oenv_map_concat_single_with_cast v brand_name f) d.

  Fixpoint oql_expr_interp (q:oql_expr) (env:oql_env) : option data :=
    match q with
    | OConst d => Some (normalize_data h d)
    | OVar n => edot env n
    | OTable t => edot constant_env t
    | OBinop bop q1 q2 =>
      olift2 (fun d1 d2 => binary_op_eval h bop d1 d2)
             (oql_expr_interp q1 env)
             (oql_expr_interp q2 env)
    | OUnop uop q1 =>
      olift (fun d1 => unary_op_eval h uop d1) (oql_expr_interp q1 env)
    | OSFW select_clause from_clause where_clause order_by_clause =>
      let init_env := Some (env :: nil) in
      let from_interp (envl:option (list oql_env)) (from_in_expr : oql_in_expr) :=
          match from_in_expr with
          | OIn in_v from_expr =>
            match envl with
            | None => None
            | Some envl' =>
              env_map_concat in_v (oql_expr_interp from_expr) envl'
            end
          | OInCast in_v brand_name from_expr =>
            match envl with
            | None => None
            | Some envl' =>
              env_map_concat_cast in_v brand_name (oql_expr_interp from_expr) envl'
            end
          end
      in
      let from_result := fold_left from_interp from_clause init_env in
      let pred (where_expr:oql_expr) (x':oql_env) :=
          match oql_expr_interp where_expr x' with
          | Some (dbool b) => Some b
          | _ => None
          end
      in
      let where_result :=
          match where_clause with
          | OTrue => from_result
          | OWhere where_expr => olift (lift_filter (pred where_expr)) from_result
          end
      in
      let order_by_result :=
          match order_by_clause with
          | ONoOrder => where_result
          | OOrderBy scl e => where_result
          end
      in
      let select_result :=
          match select_clause with
          | OSelect select_expr =>
            olift (fun x => lift dcoll (lift_map (oql_expr_interp select_expr) x))
                  order_by_result
          | OSelectDistinct select_expr =>
            let select_dup :=
                olift (fun x => (lift_map (oql_expr_interp select_expr) x))
                      order_by_result
            in
            lift (fun x => dcoll ((@bdistinct data data_eq_dec) x)) select_dup
          end
      in
      select_result
    end.

  End sem.

  Section sem2.
    Context (constant_env:list (string*data)).
    Fixpoint oql_query_program_interp (defls:list (string*data))
             (oq:oql_query_program) (env:oql_env) : option data :=
      match oq with
      | ODefineQuery s e rest =>
        olift
          (fun d => oql_query_program_interp (rec_concat_sort defls ((s,d)::nil)) rest env)
          (oql_expr_interp (rec_concat_sort constant_env defls) e env)
      | OUndefineQuery s rest =>
        oql_query_program_interp (rremove defls s) rest env
    | OQuery e => oql_expr_interp (rec_concat_sort constant_env defls) e env
      end.

  Definition oql_interp (e:oql) : option data
    := oql_query_program_interp nil e nil.

  End sem2. 
  Section OQLScope.

    Fixpoint oql_free_vars (e:oql_expr) :=
      match e with
      | OConst d => nil
      | OVar v => v :: nil
      | OTable t => nil
      | OBinop bop e1 e2 => oql_free_vars e1 ++ oql_free_vars e2
      | OUnop uop e1 => oql_free_vars e1
      | OSFW se el we oe =>
        let one_step_scope (in_expr : oql_in_expr) previous_free_vars :=
            match in_expr with
            | OIn x e1 => oql_free_vars e1 ++ remove string_eqdec x previous_free_vars
            | OInCast x _ e1 => oql_free_vars e1 ++ remove string_eqdec x previous_free_vars
            end
        in
        fold_right one_step_scope
                   (oql_select_free_vars se
                                         ++ oql_where_free_vars we
                                         ++ oql_order_free_vars oe) el
      end
    with oql_select_free_vars (se:oql_select_expr) :=
      match se with
      | OSelect e => oql_free_vars e
      | OSelectDistinct e => oql_free_vars e
      end
    with oql_where_free_vars (we:oql_where_expr) :=
      match we with
      | OTrue => nil
      | OWhere e => oql_free_vars e
      end
    with oql_order_free_vars (oe:oql_order_by_expr) :=
      match oe with
      | ONoOrder => nil
      | OOrderBy e _ => oql_free_vars e
      end.

    (* capture avoiding substitution *)
    Fixpoint oql_subst (e:oql_expr) (x:string) (e':oql_expr) : oql_expr :=
      match e with
      | OConst d => OConst d
      | OVar y => if y == x then e' else OVar y
      | OTable t => OTable t
      | OBinop bop e1 e2 => OBinop bop
                                   (oql_subst e1 x e') 
                                   (oql_subst e2 x e')
      | OUnop uop e1 => OUnop uop (oql_subst e1 x e')
      | OSFW se el we oe =>
        let for_vars := map (fun x => match x with OIn v _ | OInCast v _ _ => v end) el in
        let el' := 
            (fix F (el:list oql_in_expr) (x:string) (e':oql_expr) :=
              match el with
              | nil => nil
              | (OIn y e) :: el' =>
                if (y == x)
                then (OIn y (oql_subst e x e')) :: el'
                else (OIn y (oql_subst e x e')) :: (F el' x e')
              | (OInCast y brand_name e) :: el' =>
                if (y == x)
                then (OInCast y brand_name (oql_subst e x e')) :: el'
                else (OInCast y brand_name (oql_subst e x e')) :: (F el' x e')
              end) el x e'
        in
        if in_dec string_dec x for_vars
        then OSFW se el' we oe
        else OSFW (oql_select_subst se x e') el'
                  (oql_where_subst we x e')
                  (oql_order_subst oe x e')
      end
    with oql_select_subst (se:oql_select_expr) (x:string) (e':oql_expr) :=
      match se with
      | OSelect e => OSelect (oql_subst e x e')
      | OSelectDistinct e => OSelectDistinct (oql_subst e x e')
      end
    with oql_where_subst (we:oql_where_expr) (x:string) (e':oql_expr) :=
      match we with
      | OTrue => OTrue
      | OWhere e => OWhere (oql_subst e x e')
      end
    with oql_order_subst (we:oql_order_by_expr) (x:string) (e':oql_expr) :=
      match we with
      | ONoOrder => ONoOrder
      | OOrderBy e sc => OOrderBy (oql_subst e x e') sc
      end.
    
  Fixpoint oql_query_program_defls
             (oq:oql_query_program)  : list string :=
      match oq with
      | ODefineQuery s e rest => s::(oql_query_program_defls rest)
      | OUndefineQuery s rest => s::(oql_query_program_defls rest)
      | OQuery e => nil
      end.

  End OQLScope.

  Section Top.
    Definition oql_eval_top (q:oql) (cenv:bindings) : option data :=
      oql_interp (rec_sort cenv) q.
  End Top.
End OQL.


(* begin hide *)
Notation "‵‵ c" := (OConst (dconst c))  (at level 0) : oql_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (OConst c)  (at level 0) : oql_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (OConst (dcoll nil))  (at level 0) : oql_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (OConst (drec nil)) (at level 50) : oql_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (OBinop OpAnd r1 r2) (right associativity, at level 65): oql_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (OBinop OpOr r1 r2) (right associativity, at level 70): oql_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (OBinop OpEqual r1 r2) (right associativity, at level 70): oql_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (OBinop OpLe r1 r2) (no associativity, at level 70): oql_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (OBinop OpBagUnion r1 r2) (right associativity, at level 70): oql_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (OBinop OpBagDiff r1 r2) (right associativity, at level 70): oql_scope.  (* − = \minus *)
Notation "r1 ♯min r2" := (OBinop OpBagMin r1 r2) (right associativity, at level 70): oql_scope. (* ♯ = \sharp *)
Notation "r1 ♯max r2" := (OBinop OpBagMax r1 r2) (right associativity, at level 70): oql_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((OBinop OpRecConcat) p r) (at level 70) : oql_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((OBinop OpRecMerge) p r) (at level 70) : oql_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (OUnop OpNeg r1) (right associativity, at level 70): oql_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (OUnop OpDistinct r1) (right associativity, at level 70): oql_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (OUnop OpCount r1) (right associativity, at level 70): oql_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (OUnop OpFlatten d) (at level 50) : oql_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((OUnop OpBag) d)  (at level 50) : oql_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((OUnop (OpRec s)) r) (at level 50) : oql_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((OUnop (OpRecRemove s1)) r) (at level 50) : oql_scope.          (* ¬ = \neg and π = \pi *)
Notation "p · r" := ((OUnop (OpDot r)) p) (left associativity, at level 40): oql_scope.      (* · = \cdot *)

Notation "'$' v" := (OVar v%string) (at level 50, format "'$' v") : oql_scope.
Notation "'$$' v" := (OTable v%string) (at level 50, format "'$$' v") : oql_scope.

Notation "'SELECT' e1 'FROM' e2 'WHERE' e3" := (OSFW (OSelect e1) e2 e3) (at level 50, format "'SELECT' e1 'FROM' e2 'WHERE' e3") : oql_scope.
Notation "'SELECT' 'DISTINCT' e1 'FROM' e2 'WHERE' e3" := (OSFW (OSelectDistinct e1) e2 e3) (at level 50, format "'SELECT' 'DISTINCT' e1 'FROM' e2 'WHERE' e3") : oql_scope.
Notation "e 'IN' x" := (OIn e x) (at level 50, format "e 'IN' x") : oql_scope.

Tactic Notation "oql_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "OConst"%string
  | Case_aux c "OVar"%string
  | Case_aux c "OTable"%string
  | Case_aux c "OBinop"%string
  | Case_aux c "OUnop"%string
  | Case_aux c "OSFW"%string ].

(* end hide *)

