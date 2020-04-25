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

Require Import String.
Require Import List.
Require Import Arith.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import DataSystem.
Require Import DNNRCBase.

Section TDNNRCBase.

  Context {m:basic_model}.
  Section tplug.
      
    Class TAlgPlug {plug_type:Set} {plug:AlgPlug plug_type} :=
      mkTAlgPlug {
          plug_typing : plug_type -> tbindings -> rtype -> Prop;
        }.
    
  End tplug.

  (* Global Arguments TAlgPlug plug_type {plug} : clear implicits.  *)

  (** Typing rules for NNRC *)
  Section typ.
    Context (τconstants:tdbindings).

    (* When applying the parameters to an algebra closure, we need to check that
         those parameters are distributed *)
    Fixpoint tcombine (l:list string) (l':list drtype) {struct l} : option tbindings :=
      match l with
      | [] => Some []
      | x :: tl =>
        match l' with
        | [] => Some []
        | (Tlocal _) :: _ => None
        | (Tdistr y) :: tl' =>
          match tcombine tl tl' with
          | Some tl'' => Some ((x,y) :: tl'')
          | None => None
          end
        end
      end.

    Inductive dnnrc_base_type `{tplug: TAlgPlug} {A} : tdbindings -> @dnnrc_base _ A plug_type -> drtype -> Prop :=
    | TDNNRCGetConstant {τout} tenv s :
        forall (a:A),
          tdot τconstants s = Some τout ->
          dnnrc_base_type tenv (DNNRCGetConstant a s) τout
    | TDNNRCVar {τout} tenv v :
        forall (a:A),
          lookup equiv_dec tenv v = Some τout ->
          dnnrc_base_type tenv (DNNRCVar a v) τout
    | TDNNRCConst {τout} tenv c :
        forall (a:A),
          data_type (normalize_data brand_relation_brands c) τout ->
          dnnrc_base_type tenv (DNNRCConst a c) (Tlocal τout)
    | TDNNRCBinop  {τ₁ τ₂ τout} tenv b e1 e2 :
        forall (a:A),
          binary_op_type b τ₁ τ₂ τout ->
          dnnrc_base_type tenv e1 (Tlocal τ₁) ->
          dnnrc_base_type tenv e2 (Tlocal τ₂) ->
          dnnrc_base_type tenv (DNNRCBinop a b e1 e2) (Tlocal τout)
    | TDNNRCUnop {τ₁ τout} tenv u e1 :
        forall (a:A), 
          unary_op_type u τ₁ τout ->
          dnnrc_base_type tenv e1 (Tlocal τ₁) ->
          dnnrc_base_type tenv (DNNRCUnop a u e1) (Tlocal τout)
    | TDNNRCLet {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A), 
          dnnrc_base_type tenv e1 τ₁ ->
          dnnrc_base_type ((v,τ₁)::tenv) e2 τ₂ ->
          dnnrc_base_type tenv (DNNRCLet a v e1 e2) τ₂
    | TDNNRCForLocal {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A),
          dnnrc_base_type tenv e1 (Tlocal (Coll τ₁)) ->
          dnnrc_base_type ((v,(Tlocal τ₁))::tenv) e2 (Tlocal τ₂) ->
          dnnrc_base_type tenv (DNNRCFor a v e1 e2) (Tlocal (Coll τ₂))
    | TDNNRCForDist {τ₁ τ₂} v tenv e1 e2 :
        forall (a:A),
          dnnrc_base_type tenv e1 (Tdistr τ₁) ->
          dnnrc_base_type ((v,(Tlocal τ₁))::tenv) e2 (Tlocal τ₂) ->
          dnnrc_base_type tenv (DNNRCFor a v e1 e2) (Tdistr τ₂)
    | TDNNRCIf {τout} tenv e1 e2 e3 :
        forall (a:A), 
          dnnrc_base_type tenv e1 (Tlocal Bool) ->
          dnnrc_base_type tenv e2 τout ->
          dnnrc_base_type tenv e3 τout ->
          dnnrc_base_type tenv (DNNRCIf a e1 e2 e3) τout
    | TDNNRCEither {τout τl τr} tenv ed xl el xr er :
        forall (a:A), 
          dnnrc_base_type tenv ed (Tlocal (Either τl τr)) ->
          dnnrc_base_type ((xl,(Tlocal τl))::tenv) el τout ->
          dnnrc_base_type ((xr,(Tlocal τr))::tenv) er τout ->
          dnnrc_base_type tenv (DNNRCEither a ed xl el xr er) τout
    | TDNNRCCollect {τ} tenv e :
        forall (a:A),
          dnnrc_base_type tenv e (Tdistr τ) ->
          dnnrc_base_type tenv (DNNRCCollect a e) (Tlocal (Coll τ))
    | TDNNRCDispatch {τ} tenv e :
        forall (a:A),
          dnnrc_base_type tenv e (Tlocal (Coll τ)) ->
          dnnrc_base_type tenv (DNNRCDispatch a e) (Tdistr τ)
    (* Note: algebra 'plugged' expression is only well typed within distributed
         NNNRC if it returns a collection *)
    | TDNNRCAlg {τout} tenv tbindings op nl :
        forall (a:A),
          Forall2 (fun n τ => fst n = fst τ
                              /\ dnnrc_base_type tenv (snd n) (Tdistr (snd τ)))
                  nl tbindings ->
          plug_typing op tbindings (Coll τout) -> 
          dnnrc_base_type tenv (DNNRCAlg a op nl) (Tdistr τout)
    .

    (* Print dnnrc_base_type_ind. We will need a special inductive principle because of the list of expressions in TDNRAlg *)
  End typ.


End TDNNRCBase.

(* Global Arguments TAlgPlug {m} plug_type {plug} : clear implicits.  *)

