From Coq Require Import Ascii String Bool OrderedType Arith.
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Export PCUICReflect.
From MetaCoq.GCIC Require Import GCICAst GCICInduction.
Import List.ListNotations.
Require Import ssreflect.

From Equations Require Import Equations.

Set Asymmetric Patterns.

Open Scope gcic.

(** Notion of reflection for Type-based properties *)

Local Obligation Tactic := idtac.

Local Ltac finish :=
  let h := fresh "h" in
  right ;
  match goal with
  | e : ?t <> ?u |- _ =>
    intro h ; apply e ; now inversion h
  end.

Local Ltac fcase c :=
  let e := fresh "e" in
  case c ; intro e ; [ subst ; try (left ; reflexivity) | finish ].

Local Ltac term_dec_tac term_dec :=
  repeat match goal with
         | t : term, u : term |- _ => fcase (term_dec t u)
         | u : Universe.t , u' : Universe.t |- _ => fcase (eq_dec u u')
         | l : Level.t , l' : Level.t |- _ => fcase (eq_dec l l')
         | x : Instance.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | x : list Level.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (string_dec i i')
         | i : kername, i' : kername |- _ => fcase (kername_eq_dec i i')
         | i : string, i' : kername |- _ => fcase (string_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         end.

Derive NoConfusionHom for term.

Instance EqDec_term : EqDec term.
Proof.
  intro x; induction x using term_forall_list_ind ; intro t ;
    destruct t ; try (right ; discriminate).
  all: term_dec_tac term_dec.
  - revert l0. rename X into H ; induction H ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHAll l0) ; nodec.
        destruct (p t) ; nodec.
        subst. left. inversion e. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    destruct (IHx3 t3) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. revert brs. clear IHx1 IHx2.
    induction X ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX l0) ; nodec.
        destruct (p (snd p0)) ; nodec.
        destruct (eq_dec (fst x) (fst p0)) ; nodec.
        destruct x, p0.
        left.
        cbn in *. subst. inversion e. reflexivity.
  - destruct (IHx t) ; nodec.
    left. subst. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
  - destruct (IHx t) ; nodec.
    subst. left. reflexivity. 
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
Defined.

Instance reflect_term : ReflectEq term :=
  let h := EqDec_ReflectEq term in _.

Definition eqb_context_decl (x y : context_decl) :=
  let (na, b, ty) := x in
  let (na', b', ty') := y in
  eqb na na' && eqb b b' && eqb ty ty'.

Instance eq_ctx : ReflectEq context_decl.
Proof.
  refine {| eqb := eqb_context_decl |}.
  intros.
  destruct x as [na b ty], y as [na' b' ty']. cbn -[eqb].
  destruct (eqb_spec na na'); subst;
    destruct (eqb_spec b b'); subst;
      destruct (eqb_spec ty ty'); subst; constructor; congruence.
Qed.

Instance eqb_ctx : ReflectEq context := _.
