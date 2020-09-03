(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List.
From MetaCoq.Template Require Import utils.
From MetaCoq.GCIC Require Import GCICAst GCICInduction GCICLiftSubst.
Local Open Scope string_scope.
Set Asymmetric Patterns.

(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)


Instance subst_instance_constr : UnivSubst term :=
  fix subst_instance_constr u c {struct c} : term :=
  match c with
  | gRel _ | gVar _  => c
  | gEvar ev args => gEvar ev (List.map (subst_instance_constr u) args)
  | gSort s => gSort (subst_instance_univ u s)
  | gConst c u' => gConst c (subst_instance_instance u u')
  | gInd i u' => gInd i (subst_instance_instance u u')
  | gConstruct ind k u' => gConstruct ind k (subst_instance_instance u u')
  | gLambda na T M => gLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | gApp f v => gApp (subst_instance_constr u f) (subst_instance_constr u v)
  | gProd na A B => gProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | gLetIn na b ty b' => gLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | gCase ind p c brs =>
    let brs' := List.map (on_snd (subst_instance_constr u)) brs in
    gCase ind (subst_instance_constr u p) (subst_instance_constr u c) brs'
  | gProj p c => gProj p (subst_instance_constr u c)
  | gFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    gFix mfix' idx
  | gCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    gCoFix mfix' idx
  | gUkn A => gUkn (subst_instance_constr u A)
  | gCast A t => gCast (subst_instance_constr u A) (subst_instance_constr u t)
  end.

Instance subst_instance_decl : UnivSubst context_decl
  := map_decl ∘ subst_instance_constr.

Instance subst_instance_context : UnivSubst context
  := map_context ∘ subst_instance_constr.

Lemma lift_subst_instance_constr u c n k :
  lift n k (subst_instance_constr u c) = subst_instance_constr u (lift n k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    try solve [f_equal; eauto; solve_all; eauto].
Qed.

Lemma subst_instance_constr_mkApps u f a :
  subst_instance_constr u (mkApps f a) =
  mkApps (subst_instance_constr u f) (map (subst_instance_constr u) a).
Proof.
  induction a in f |- *; auto.
  simpl map. simpl. now rewrite IHa.
Qed.

Lemma subst_instance_constr_it_mkProd_or_LetIn u ctx t :
  subst_instance_constr u (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_instance_context u ctx) (subst_instance_constr u t).
Proof.
  induction ctx in u, t |- *; simpl; unfold mkProd_or_LetIn; try congruence.
  rewrite IHctx.  f_equal; unfold mkProd_or_LetIn.
  destruct a as [na [b|] ty]; simpl; eauto.
Qed.

Lemma subst_instance_context_length u ctx
  : #|subst_instance_context u ctx| = #|ctx|.
Proof. unfold subst_instance_context, map_context. now rewrite map_length. Qed.

Lemma subst_subst_instance_constr u c N k :
  subst (map (subst_instance_constr u) N) k (subst_instance_constr u c)
  = subst_instance_constr u (subst N k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    try solve [f_equal; eauto; solve_all; eauto].

  elim (Nat.leb k n). rewrite nth_error_map.
  destruct (nth_error N (n - k)). simpl.
  apply lift_subst_instance_constr. reflexivity. reflexivity.
Qed.

Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all. now destruct H as [n [-> _]].
Qed.

  (** Tests that the term is closed over [k] universe variables *)

  Fixpoint closedu (k : nat) (t : term) : bool :=
  match t with
  | gSort univ => closedu_universe k univ
  | gInd _ u => closedu_instance k u
  | gConstruct _ _ u => closedu_instance k u
  | gConst _ u => closedu_instance k u
  | gRel i => true
  | gEvar ev args => forallb (closedu k) args
  | gLambda _ T M | gProd _ T M => closedu k T && closedu k M
  | gApp u v => closedu k u && closedu k v
  | gLetIn na b t b' => closedu k b && closedu k t && closedu k b'
  | gCase ind p c brs =>
    let brs' := forallb (test_snd (closedu k)) brs in
    closedu k p && closedu k c && brs'
  | gProj p c => closedu k c
  | gFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | gCoFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | gUkn A => closedu k A
  | gCast A t => closedu k A && closedu k t
  | x => true
  end.

  Lemma closedu_subst_instance_constr u t : closedu 0 t -> subst_instance_constr u t = t.
  Proof.
    induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
      try f_equal; rtoProp ; eauto with substu; unfold test_def in *;
        try solve [f_equal; eauto; repeat (rtoProp; solve_all)].
  Qed.

Lemma subst_instance_constr_closedu (u : Instance.t) (Hcl : closedu_instance 0 u) t:
    closedu #|u| t -> closedu 0 (subst_instance_constr u t).
  Proof.
    induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?forallb_map;
    try f_equal; auto with substu;
    unfold test_def, map_def in *;
    try solve [f_equal; eauto; repeat (rtoProp; solve_all); intuition auto with substu].
  Qed.
