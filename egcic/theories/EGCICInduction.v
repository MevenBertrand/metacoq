(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Import utils.
From MetaCoq.EGCIC Require Import EGCICAst.
Set Asymmetric Patterns.

(** * Deriving a compact induction principle for terms

  *WIP*

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Type,
    (forall n : nat, P (eRel n)) ->
    (forall i : ident, P (eVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (eEvar n l)) ->
    (forall s, P (eSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (eProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (eLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (eLetIn n t t0 t1)) ->
    (forall t u : term, P t -> P u -> P (eApp t u)) ->
    (forall (s : kername) (u : list Level.t), P (eConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (eInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (eConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsProp P l -> P (eCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (eProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (eFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (eCoFix m n)) ->
    (forall (e : err_type) (A : term), P A -> P (eErr e A)) ->
    (forall (A : term), P A -> forall B : term, P B -> forall t : term, P t -> P (eCast A B t)) ->
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
