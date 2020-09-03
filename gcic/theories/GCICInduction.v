(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Import utils.
From MetaCoq.GCIC Require Import GCICAst.
Set Asymmetric Patterns.

(** * Deriving a compact induction principle for terms

  *WIP*

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Type,
    (forall n : nat, P (gRel n)) ->
    (forall i : ident, P (gVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (gEvar n l)) ->
    (forall s, P (gSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (gProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (gLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (gLetIn n t t0 t1)) ->
    (forall t u : term, P t -> P u -> P (gApp t u)) ->
    (forall (s : kername) (u : list Level.t), P (gConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (gInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (gConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsProp P l -> P (gCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (gProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (gFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (gCoFix m n)) ->
    (forall (A : term), P A -> P (gUkn A)) ->
    (forall (A : term), P A -> forall t : term, P t -> P (gCast A t)) ->
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert brs.
  fix auxl' 1.
  destruct brs; constructor; [|apply auxl'].
  apply auxt.

  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  split; apply auxt.
  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  split; apply auxt.
Defined.
