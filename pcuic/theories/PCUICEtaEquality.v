(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Template Require Import LibHypsNaming config utils Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICSize PCUICUtils PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICReflect PCUICContextRelation PCUICEquality.

Require Import ssreflect.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Implicit Types (cf : checker_flags).

(** ** Syntactic equality up-to universes and eta-expansion *)

(** This extends eq_term_upto_univ with new cases to treat eta equality
    To obtain a transitive relation even in an untyped setting, type annotations
    on abstractions are ignored *)

Definition global_variance Σ gr :=
  match gr with
  | IndRef ind =>
    match lookup_inductive Σ ind with
    | Some (mdecl, idecl) => 
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => mdecl.(ind_variance)
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor Σ ind k with
    | Some (mdecl, idecl, cdecl) => Some []
        (** Fully applied constructors are always compared at the same supertype, 
          which implies that no universe equality needs to be checked here. *)
    | _ => None
    end
  | _ => None
  end.

Definition R_global_instance Σ Re Rle gr :=
  R_opt_variance Re Rle (global_variance Σ gr).

Lemma R_global_instance_refl Σ Re Rle gr u : 
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  R_global_instance Σ Re Rle gr u u.
Proof.
  intros rRE rRle.
  rewrite /R_global_instance.
  destruct global_variance as [v|] eqn:lookup.
  - induction u in v |- *; simpl; auto;
    unfold R_opt_variance in IHu; destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
  - apply Forall2_same; eauto.
Qed.

Lemma R_global_instance_sym Σ Re Rle gr u u' : 
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  R_global_instance Σ Re Rle gr u' u ->
  R_global_instance Σ Re Rle gr u u'.
Proof.
  intros rRE rRle.
  rewrite /R_global_instance.
  destruct global_variance as [v|] eqn:lookup.
  - induction u in u', v |- *; destruct u'; simpl; auto;
    destruct v as [|v vs]; unfold R_opt_variance in IHu; simpl; auto.
    intros [Ra Ru']. split.
    destruct v; simpl; auto.
    apply IHu; auto.
  - apply Forall2_symP; eauto.
Qed.

Instance R_global_instance_trans Σ Re Rle gr :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.Transitive (R_global_instance Σ Re Rle gr).
Proof.
  intros he hle x y z.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance as [v|].
  clear -he hle.
  induction x in y, z, v |- *; destruct y, z, v; simpl; auto => //. eauto.
  intros [Ra Rxy] [Rt Ryz].
  split; eauto.
  destruct t1; simpl in *; auto.
  now etransitivity; eauto.
  now etransitivity; eauto.
  eapply Forall2_trans; auto.
Qed.

Inductive eq_term_upto_univ_eta
  Σ (Re Rle : Universe.t -> Universe.t -> Prop) :
  term -> term -> Type :=

| eq_Rel n :
  eq_term_upto_univ_eta Σ Re Rle (tRel n) (tRel n)

| eq_Evar e args args' :
  All2 (eq_term_upto_univ_eta Σ Re Re) args args' ->
  eq_term_upto_univ_eta Σ Re Rle (tEvar e args) (tEvar e args')

| eq_Var id :
  eq_term_upto_univ_eta Σ Re Rle (tVar id) (tVar id)

| eq_Sort s s' :
  Rle s s' ->
  eq_term_upto_univ_eta Σ Re Rle (tSort s) (tSort s')

| eq_App t t' u u' :
  eq_term_upto_univ_eta Σ Re Rle t t' ->
  eq_term_upto_univ_eta Σ Re Re u u' ->
  eq_term_upto_univ_eta Σ Re Rle (tApp t u) (tApp t' u')

| eq_Const c u u' :
  R_universe_instance Re u u' ->
  eq_term_upto_univ_eta Σ Re Rle (tConst c u) (tConst c u')

| eq_Ind i u u' :
  R_global_instance Σ Re Rle (IndRef i) u u' ->
  eq_term_upto_univ_eta Σ Re Rle (tInd i u) (tInd i u')

| eq_Construct i k u u' :
  R_global_instance Σ Re Rle (ConstructRef i k) u u' ->
  eq_term_upto_univ_eta Σ Re Rle (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
  (* Domains are ignored **)
  (* eq_binder_annot na na' ->
      eq_term_upto_univ_eta Σ Re Re 0 ty ty' -> *)
  eq_term_upto_univ_eta Σ Re Rle t t' ->
  eq_term_upto_univ_eta Σ Re Rle (tLambda na ty t) (tLambda na' ty' t')

| eq_Eta_l f g na A :
  eq_term_upto_univ_eta Σ Re Rle (tApp (lift0 1 f) (tRel 0)) g ->
  eq_term_upto_univ_eta Σ Re Rle f (tLambda na A g)

| eq_Eta_r f g na A :
  eq_term_upto_univ_eta Σ Re Rle f (tApp (lift0 1 g) (tRel 0)) ->
  eq_term_upto_univ_eta Σ Re Rle (tLambda na A f) g

| eq_Prod na na' a a' b b' :
  eq_binder_annot na na' ->
  eq_term_upto_univ_eta Σ Re Re a a' ->
  eq_term_upto_univ_eta Σ Re Rle b b' ->
  eq_term_upto_univ_eta Σ Re Rle (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
  eq_binder_annot na na' ->
  eq_term_upto_univ_eta Σ Re Re t t' ->
  eq_term_upto_univ_eta Σ Re Re ty ty' ->
  eq_term_upto_univ_eta Σ Re Rle u u' ->
  eq_term_upto_univ_eta Σ Re Rle (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case indn p p' c c' brs brs' :
  (* todo *)
  eq_predicate (eq_term_upto_univ_eta Σ Re Re) Re p p' ->
  eq_term_upto_univ_eta Σ Re Re c c' ->
  All2 (fun x y =>
    eq_context_gen eq eq (bcontext x) (bcontext y) ×
    eq_term_upto_univ_eta Σ Re Re (bbody x) (bbody y)
  ) brs brs' ->
  eq_term_upto_univ_eta Σ Re Rle (tCase indn p c brs) (tCase indn p' c' brs')

| eq_Proj p c c' :
  eq_term_upto_univ_eta Σ Re Re c c' ->
  eq_term_upto_univ_eta Σ Re Rle (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
  All2 (fun x y =>
    eq_term_upto_univ_eta Σ Re Re x.(dtype) y.(dtype) *
    eq_term_upto_univ_eta Σ Re Re x.(dbody) y.(dbody) *
    (x.(rarg) = y.(rarg)) ×
    eq_binder_annot x.(dname) y.(dname)
  )%type mfix mfix' ->
  eq_term_upto_univ_eta Σ Re Rle (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
  All2 (fun x y =>
    eq_term_upto_univ_eta Σ Re Re x.(dtype) y.(dtype) ×
    eq_term_upto_univ_eta Σ Re Re x.(dbody) y.(dbody) ×
    (x.(rarg) = y.(rarg)) *
    eq_binder_annot x.(dname) y.(dname)
  ) mfix mfix' ->
  eq_term_upto_univ_eta Σ Re Rle (tCoFix mfix idx) (tCoFix mfix' idx)
  
| eq_Prim i : eq_term_upto_univ_eta Σ Re Rle (tPrim i) (tPrim i).


Lemma eq_term_upto_univ_eta_list_ind
  Σ Re P :

  (forall Rle f g na A,
    (* ~ isLambda f -> *)
    eq_term_upto_univ_eta Σ Re Rle (tApp (lift0 1 f) (tRel 0)) g ->
    P Rle (tApp (lift0 1 f) (tRel 0)) g ->
    P Rle f (tLambda na A g)) ->

  (forall Rle f g na A,
    (* ~ isLambda g -> *)
    eq_term_upto_univ_eta Σ Re Rle f (tApp (lift0 1 g) (tRel 0)) ->
    P Rle f (tApp (lift0 1 g) (tRel 0)) ->
    P Rle (tLambda na A f) g) ->

  (forall Rle n,
    P Rle (tRel n) (tRel n)) ->

  (forall Rle e args args',
    All2 (eq_term_upto_univ_eta Σ Re Re) args args' ->
    All2 (P Re) args args' ->
    P Rle (tEvar e args) (tEvar e args')) ->

  (forall Rle id,
    P Rle (tVar id) (tVar id)) ->

  (forall (Rle : Universe.t -> Universe.t -> Prop) s s',
    Rle s s' ->
    P Rle (tSort s) (tSort s')) ->

  (forall Rle t t' u u',
    eq_term_upto_univ_eta Σ Re Rle t t' ->
    P Rle t t' ->
    eq_term_upto_univ_eta Σ Re Re u u' ->
    P Re u u' ->
    P Rle (tApp t u) (tApp t' u')) ->

  (forall Rle c u u',
    R_universe_instance Re u u' ->
    P Rle (tConst c u) (tConst c u')) ->

  (forall Rle i u u',
    R_global_instance Σ Re Rle (IndRef i) u u' ->
    P Rle (tInd i u) (tInd i u') ) ->

  (forall Rle i k u u',
    R_global_instance Σ Re Rle (ConstructRef i k) u u' ->
    P Rle (tConstruct i k u) (tConstruct i k u') ) ->

  (forall Rle na na' ty ty' t t',
    eq_term_upto_univ_eta Σ Re Rle t t' ->
    P Rle t t' ->
    P Rle (tLambda na ty t) (tLambda na' ty' t')) ->

  (forall Rle na na' a a' b b',
    eq_binder_annot na na' ->
    eq_term_upto_univ_eta Σ Re Re a a' ->
    P Re a a' ->
    eq_term_upto_univ_eta Σ Re Rle b b' ->
    P Rle b b' ->
    P Rle (tProd na a b) (tProd na' a' b') ) ->

  (forall Rle na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    eq_term_upto_univ_eta Σ Re Re t t' ->
    P Re t t' ->
    eq_term_upto_univ_eta Σ Re Re ty ty' ->
    P Re ty ty' ->
    eq_term_upto_univ_eta Σ Re Rle u u' ->
    P Rle u u' ->
    P Rle (tLetIn na t ty u) (tLetIn na' t' ty' u')) ->

  (forall Rle indn p p' c c' brs brs',
    eq_predicate (fun u v =>
     (eq_term_upto_univ_eta Σ Re Re u v) × P Re u v)
    Re p p' ->
    eq_term_upto_univ_eta Σ Re Re c c' ->
    P Re c c' ->
    All2 (fun x y =>
      eq_context_gen eq eq (bcontext x) (bcontext y) ×
      eq_term_upto_univ_eta Σ Re Re (bbody x) (bbody y) ×
      P Re (bbody x) (bbody y)
    ) brs brs' ->
    P Rle (tCase indn p c brs) (tCase indn p' c' brs') ) ->

  (forall Rle p c c',
    eq_term_upto_univ_eta Σ Re Re c c' ->
    P Re c c' ->
    P Rle (tProj p c) (tProj p c') ) ->

  (forall Rle mfix mfix' idx,
    All2 (fun x y =>
      eq_term_upto_univ_eta Σ Re Re x.(dtype) y.(dtype) ×
      P Re x.(dtype) y.(dtype) ×
      eq_term_upto_univ_eta Σ Re Re x.(dbody) y.(dbody) ×
      P Re x.(dbody) y.(dbody) ×
      x.(rarg) = y.(rarg) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    P Rle (tFix mfix idx) (tFix mfix' idx) ) ->

  (forall Rle mfix mfix' idx,
    All2 (fun x y =>
      eq_term_upto_univ_eta Σ Re Re x.(dtype) y.(dtype) ×
      P Re x.(dtype) y.(dtype) ×
      eq_term_upto_univ_eta Σ Re Re x.(dbody) y.(dbody) ×
      P Re x.(dbody) y.(dbody) ×
      x.(rarg) = y.(rarg) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    P Rle (tCoFix mfix idx) (tCoFix mfix' idx) ) ->
    
  (forall Rle i,
    P Rle (tPrim i) (tPrim i) ) ->
  
  forall Rle u v,
    eq_term_upto_univ_eta Σ Re Rle u v -> P Rle u v.
Proof.
  intros until Rle. revert Rle.
  fix auxe 4.
  move auxe at top.
  intros Rle u v h.
  destruct h ;
  match goal with
      H : _ |- _ => apply H ; auto
  end.
  4,5: generalize dependent (fix_context mfix) ; intros.
  all:
    match goal with
    | H : All2 _ ?args ?args' |- All2 _ ?args ?args' =>
        dependent induction H ; constructor ; intuition auto
    | _ => idtac
    end.
  unfold eq_predicate in *.
  intuition auto.
  clear - a0 auxe.
  induction a0.
  all: constructor.
  2: assumption.
  split.
  2: apply auxe.
  all: assumption.
Defined.

(* ** Syntactic conversion up-to universes *)

Definition eq_term_eta `{checker_flags} Σ φ :=
  eq_term_upto_univ_eta Σ (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Definition leq_term_eta `{checker_flags} Σ φ :=
  eq_term_upto_univ_eta Σ (eq_universe φ) (leq_universe φ).

Instance eq_term_upto_univ_eta_refl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_term_upto_univ_eta Σ Re Rle).
Proof.
  intros hRe hRle t.
  induction t in Rle, hRle |- * using term_forall_list_ind.
  all: simpl.
  all: constructor ; eauto.
  - eapply All_All2 ; eauto.
  - eapply Forall2_same ; eauto.
  - apply R_global_instance_refl ; auto.
  - apply R_global_instance_refl; auto.
  - destruct X as [? [? ?]].
    unfold eq_predicate; solve_all.
    eapply All_All2; eauto. reflexivity.
    eapply onctx_eq_ctx in a0; eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
    eapply onctx_eq_ctx in a; eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
Qed.

Instance eq_term_eta_refl `{checker_flags} Σ φ : Reflexive (eq_term_eta Σ φ).
Proof.
  apply eq_term_upto_univ_eta_refl. all: exact _.
Qed.

Instance leq_term_eta_refl `{checker_flags} Σ φ : Reflexive (leq_term_eta Σ φ).
Proof.
  apply eq_term_upto_univ_eta_refl; exact _.
Qed.

Derive Signature for eq_term_upto_univ_eta.

Instance eq_term_upto_univ_eta_sym Σ Re Rle :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_term_upto_univ_eta Σ Re Rle).
Proof.
  intros he hle u v e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction e using eq_term_upto_univ_eta_list_ind.
  all: intros ; try solve [
    econstructor ; eauto using R_global_instance_sym ;
    try eapply Forall2_symP ; eauto
  ].
  - econstructor.
    apply All2_sym.
    eapply All2_impl.
    1: eassumption.
    auto.
  - econstructor.
    + unfold eq_predicate in *.
      intuition.
      apply All2_sym.
      eapply All2_impl.
      1: eassumption.
      intuition.
    + auto.
    + apply All2_sym. eapply All2_impl. 1: eassumption. intuition.
  - econstructor.
    apply All2_sym.
    eapply All2_impl. 1: eassumption. intuition.
    destruct X0 as (?&?&?&?&[]&?).
    reflexivity.
  - econstructor.
    apply All2_sym.
    eapply All2_impl. 1: eassumption. intuition.
    destruct X0 as (?&?&?&?&[]&?).
    reflexivity.
Qed.

Instance eq_predicate_sym Re Ru :
  CRelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Ru ->
  CRelationClasses.Symmetric (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now symmetry.
Qed.

Instance eq_term_eta_sym `{checker_flags} Σ φ : Symmetric (eq_term_eta Σ φ).
Proof.
  eapply eq_term_upto_univ_eta_sym. all: exact _.
Qed.

Instance eq_predicate_trans Re Ru :
  CRelationClasses.Transitive Re ->
  RelationClasses.Transitive Ru ->
  CRelationClasses.Transitive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now etransitivity.
  eapply All2_trans; tea.
  etransitivity; tea.
Qed.

Lemma eq_term_upto_univ_eta_lift Σ Re Rle n k:
  Proper (eq_term_upto_univ_eta Σ Re Rle ==> eq_term_upto_univ_eta Σ Re Rle) (lift n k).
Proof.
  intros t t' eq.
  revert k.
  dependent induction eq using eq_term_upto_univ_eta_list_ind.
  all: cbn ; intros ; constructor ; auto.
  - rewrite permute_lift.
    1: by lia.
    replace (k + 1) with (S k) by lia.
    by apply IHeq.
  - rewrite permute_lift.
    1: by lia.
    replace (k + 1) with (S k) by lia.
    by apply IHeq.
  - apply All2_map.
    eapply All2_impl ; eauto.
  - unfold eq_predicate in *.
    intuition.
    + apply All2_map.
      eapply All2_impl.
      1: eassumption.
      intuition.
    + clear -a1 b0.
      destruct p, p'; cbn in *.
      by apply All2_fold_length in a1 as []. 
  - apply All2_map.
    eapply All2_impl ; eauto.
    cbn ; intros ? ? (a&?&?).
    split ; auto.
    by apply All2_fold_length in a as [].
  - apply All2_map.
    eapply All2_impl ; eauto.
    intros [] [] (?&?&?&?&?&?).
    repeat split ; cbn in * ; auto.
    by apply All2_length in X as [].
  - apply All2_map.
    eapply All2_impl ; eauto.
    intros [] [] (?&?&?&?&?&?).
    repeat split ; cbn in * ; auto.
    by apply All2_length in X as [].
Qed.

Lemma lift_eq_term_eta {cf:checker_flags} Σ φ n k T U :
  eq_term_eta Σ φ T U -> eq_term_eta Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_eta_lift.
Qed.

Lemma lift_leq_term_eta {cf:checker_flags} Σ φ n k T U :
  leq_term_eta Σ φ T U -> leq_term_eta Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_eta_lift.
Qed.

Lemma eq_term_upto_univ_eta_unlift Σ Re Rle t u n k:
  eq_term_upto_univ_eta Σ Re Rle (lift n k t) (lift n k u) ->
  eq_term_upto_univ_eta Σ Re Rle t u.
Proof.
  intros eq_lift.
  dependent induction eq_lift using eq_term_upto_univ_eta_list_ind.
  all:
  repeat match goal with
    | H : (lift _ _ ?t) = _ _ |- _ => destruct t ; inversion H ; subst ; clear H
  end ;
  try constructor ;
  try solve [
    match goal with 
      IH : _ |- _ => solve [eapply IH ; repeat f_equal ; auto]
    end ].
  - eapply IHeq_lift.
    repeat f_equal.
    cbn.
    f_equal.
    symmetry.
    replace (S k) with (k + 1) by lia.
    apply permute_lift.
    lia.
  - eapply IHeq_lift.
    repeat f_equal.
    cbn.
    f_equal.
    symmetry.
    replace (S k) with (k + 1) by lia.
    apply permute_lift.
    lia.
  - suff ? : n = n1 by (subst ; constructor).
    destruct (Nat.leb_spec0 k n) ; destruct (Nat.leb_spec0 k n1).
    all: lia.
  - eapply All2_impl.
    1: eapply All2_map_inv ; eassumption.
    intros ? ? H ; eapply H.
    repeat f_equal.
  - unfold eq_predicate in *.
    destruct X as (?&?&?&?&?).
    repeat split ; eauto.
    + clear - a.
      destruct p1, p0 ; cbn in *.
      eapply All2_impl.
      1: eapply All2_map_inv ; eassumption.
      intros ? ? H ; eapply H.
      repeat f_equal.
    + clear - e0 a0.
      destruct p1, p0 ; cbn in *.
      eapply e0.
      apply All2_fold_length in a0 as [].
      repeat f_equal.
  - eapply All2_impl.
    1: eapply All2_map_inv ; eassumption.
    cbn in *.
    intros ? ? (?&?&?).
    split ; auto.
    eapply e0.
    unfold id in a ; apply All2_fold_length in a as [].
    repeat f_equal.
  - eapply All2_impl.
    1: eapply All2_map_inv ; eassumption.
    cbn in *.
    intros ? ? (?&?&?&?&?&?).
    repeat split ; auto.
    + eapply e0.
      repeat f_equal.
    + apply All2_length in X.
      rewrite !map_length in X.
      destruct X.
      eapply e2.
      repeat f_equal.
  - eapply All2_impl.
    1: eapply All2_map_inv ; eassumption.
    cbn in *.
    intros ? ? (?&?&?&?&?&?).
    repeat split ; auto.
    + eapply e0.
      repeat f_equal.
    + apply All2_length in X.
      rewrite !map_length in X.
      destruct X.
      eapply e2.
      repeat f_equal.
Qed.

Lemma eq_term_admissible Σ Re Rle t u :
  eq_term_upto_univ_eta Σ Re Rle (tApp (lift0 1 t) (tRel 0)) (tApp (lift0 1 u) (tRel 0)) ->
  eq_term_upto_univ_eta Σ Re Rle t u.
Proof.
  intros H.
  inversion_clear H.
  clear X0.
  eapply eq_term_upto_univ_eta_unlift.
  eassumption.
Qed.

Fixpoint lift_applies (n : nat) (l : list nat) (t : term) :=
  match l with
  | [] => lift0 n t
  | m :: l' => tApp (lift_applies n l' t) (tRel m)
  end.

Lemma lift_lift_applies (n : nat) (l : list nat) (t : term) :
  (lift0 1 (lift_applies n l t)) = lift_applies (S n) (map S l) t.
Proof.
  induction l.
  - cbn.
    symmetry.
    apply simpl_lift0.
  - cbn.
    rewrite IHl.
    reflexivity.
Qed.

(* Fixpoint count_lambdas t :=
  match t with
  | tLambda _ _ t' => S (count_lambdas t')
  | _ => 0
  end.

Lemma right_lex' {T U} {RT : T -> T -> Prop} {RU : U -> U -> Prop} {t t' u u'} :
  t = t' -> RU u u' -> (RT ⊗ RU) (t,u) (t',u').
Proof.
  intros [].
  by right.
Qed. *)

Fixpoint size_lambda t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size_lambda args)
  | tLambda na T M => 5 + (size_lambda T + size_lambda M)
  | tApp u v => S (size_lambda u + size_lambda v)
  | tProd na A B => S (size_lambda A + size_lambda B)
  | tLetIn na b t b' => S (size_lambda b + size_lambda t + size_lambda b')
  | tCase ind p c brs => S (predicate_size size_lambda p +
    size_lambda c + list_size (branch_size size_lambda) brs)
  | tProj p c => S (size_lambda c)
  | tFix mfix idx => S (mfixpoint_size size_lambda mfix)
  | tCoFix mfix idx => S (mfixpoint_size size_lambda mfix)
  | x => 1
  end.

Lemma size_lambda_lift n k t : size_lambda (lift n k t) = size_lambda t.
  Proof.
    revert n k t.
    fix size_lambda_lift 3.
    destruct t; simpl; rewrite ?list_size_map_hom; try lia.
    all:try now rewrite !size_lambda_lift.
    all:try intros; auto.
    - destruct x. simpl. unfold branch_size; cbn.
      f_equal.
      symmetry.
      apply size_lambda_lift.
    - f_equal. f_equal. f_equal.
      unfold predicate_size; cbn.
      2:apply size_lambda_lift.
      f_equal; [|apply size_lambda_lift].
      f_equal. cbn.
      apply list_size_map_hom. intros. symmetry; auto.
    - unfold mfixpoint_size.
      f_equal.
      apply list_size_map_hom. intros.
      simpl. destruct x. simpl. unfold def_size. simpl.
      f_equal; symmetry; apply size_lambda_lift.
    - unfold mfixpoint_size.
      f_equal.
      apply list_size_map_hom. intros.
      simpl. destruct x. simpl. unfold def_size. simpl.
      f_equal; symmetry; apply size_lambda_lift.
  Qed.

Definition isEta {Σ Re Rle t t'} (e : eq_term_upto_univ_eta Σ Re Rle t t') :=
  match e with
  | eq_Eta_l _ _ _ _ _ | eq_Eta_r _ _ _ _ _ => true
  | _ => false
  end.

Lemma lift_applies_eta Σ Re Rle t t' :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  ~ isLambda t ->
  ~ isLambda t' ->
  forall w,
  (forall w' n (e : eq_term_upto_univ_eta Σ Re Rle (lift0 n t') w'),
    size_lambda w' <= size_lambda w -> ~ isEta e ->
    eq_term_upto_univ_eta Σ Re Rle (lift0 n t) w') ->
  eq_term_upto_univ_eta Σ Re Rle t' w ->
  eq_term_upto_univ_eta Σ Re Rle t w.
Proof.
  intros he hle iLt iLt' w base.
  replace t' with (lift_applies 0 [] t') by apply lift0_id.
  replace t with (lift_applies 0 [] t) by apply lift0_id.
  generalize 0, (@nil nat).
  intros n l e.
  induction w in base, n, l, e |- *.
  all: try solve [destruct l ; cbn in * ;
    [ eapply (base _ _ e) ; [cbn in * ; lia | idtac] ; destruct t' ; cbn in * ; by dependent inversion e| by inversion e]].
  - constructor.
    rewrite lift_lift_applies.
    change (tApp _ _) with (lift_applies (S n) (0 :: map S l) t).
    apply IHw2.
    + intros.
      apply (base _ _ e0) ; auto.
      cbn ; lia. 
    + inversion e ; subst.
      1,3: destruct l, t' ; cbn in * ; congruence.
      rewrite lift_lift_applies in X.
      assumption.
  - destruct l.
    + cbn in *.
      apply (base _ _ e).
      1: cbn ; lia.
      destruct t' ; cbn in * ; auto.
      all: dependent inversion e ; cbn ; auto.
    + cbn in *.
      inversion e ; subst.
      constructor ; intuition.
Qed.

Definition eta_size ttt := size_lambda ttt.1 + size_lambda ttt.2.1 + size_lambda ttt.2.2.

Instance eq_term_upto_univ_eta_trans Σ Re Rle:
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  Transitive (eq_term_upto_univ_eta Σ Re Rle).
Proof.
  intros he hle u v w e.
  revert Rle hle e.
  pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
  change u with (u,(v,w)).1.
  change v with (u,(v,w)).2.1 at 2 3.
  change w with (u,(v,w)).2.2 at 4 6.
  pattern (u,(v,w)).
  apply (@Fix_F _ (precompose lt eta_size)).
  clear u v w.
  2: by apply wf_precompose, lt_wf.
  intros (u&v&w) IH Rle hle e ; cbn in *.
  inversion e ; subst ; clear e.

  - eapply lift_applies_eta ; auto.

  - eapply lift_applies_eta ; auto.
    intros w' n e' s.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; try solve [cbn ; congruence].
    intros _.
    constructor.
    induction args in args', args'0, s, X, a, IH |- *.
    + inversion X ; subst.
      cbn in a ; inversion a ; subst.
      cbn ; constructor.
    + cbn in *.
      inversion X ; subst ; clear X.
      cbn in a ; inversion a ; subst ; clear a ; cbn in s.
      constructor.
      * eapply (IH (_,(_,_))) ; rewrite /eta_size /= -/lift ; tea.
        2: by apply eq_term_upto_univ_eta_lift.
        rewrite !size_lambda_lift.
        lia.
      * eapply IHargs ; eauto.
        2: lia.
        intros ; apply IH ; auto.
        cbn ; lia.
  
  - eapply lift_applies_eta ; auto.

  - eapply lift_applies_eta ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion_clear e' ; try solve [cbn ; congruence].
    intros _.
    constructor ; eauto.

  - eapply lift_applies_eta ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    all: eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
    2,4: by apply eq_term_upto_univ_eta_lift.
    all: rewrite /eta_size /= !size_lambda_lift ; lia.

  - eapply lift_applies_eta ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    etransitivity ; eauto.
    
  - eapply lift_applies_eta ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    etransitivity ; eauto.

  - eapply lift_applies_eta ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    etransitivity ; eauto.

  - intros e'.
    inversion e' ; subst.
    + constructor.
      eapply (IH (_,(_,_))) ; cbn ; tea.
      lia.
    + apply eq_Eta_l.
      eapply (IH (_,(_,_))) ; cbn ; tea.
      2: constructor ; constructor ; by apply eq_term_upto_univ_eta_lift.
      rewrite /= !size_lambda_lift.
      lia.
    + constructor ; auto.
      eapply (IH (_,(_,_))) ; cbn ; tea.
      rewrite /= !size_lambda_lift.
      lia.

  - intros e'.
    inversion e' ; subst ; clear e'.
    + constructor ; auto.
      eapply (IH (_,(_,_))) ; cbn ; tea.
      rewrite /eta_size /= size_lambda_lift.
      lia.
    + constructor.
      eapply lift_applies_eta ; tea.
      1,2: cbn ; congruence.
      intros until e.
      dependent inversion e ; subst ; clear e ; cbn in *.
      2:  congruence.
      intros ? _.
      constructor ; auto.
      eapply (IH (_,(_,_))) ; rewrite -/lift /= ; tea.
      1: rewrite /eta_size /= !size_lambda_lift ; lia.
      rewrite -/(lift0 n (tLambda _ _ _)).
      apply eq_term_upto_univ_eta_lift.
      constructor.
      rewrite permute_lift0 -/(lift 1 1 (tApp _ (tRel 0))).
      by apply eq_term_upto_univ_eta_lift.
    + apply eq_term_admissible.
      eapply (IH (_,(_,_))) ; cbn ; tea.
      rewrite /eta_size /= !size_lambda_lift.
      lia.

  - intros e'.
    constructor.
    eapply (IH (_,(_,_))) ; cbn ; tea.
    2: repeat constructor ; by apply eq_term_upto_univ_eta_lift.
    rewrite /= !size_lambda_lift.
    lia.

  - eapply lift_applies_eta ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    + eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
      2: by apply eq_term_upto_univ_eta_lift.
      rewrite /eta_size /= !size_lambda_lift.
      lia.
    + eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
      2: by apply eq_term_upto_univ_eta_lift.
      rewrite /eta_size !size_lambda_lift /=.
      lia.

  - eapply lift_applies_eta ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    + eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
      2: by apply eq_term_upto_univ_eta_lift.
      rewrite /eta_size /= !size_lambda_lift.
      lia.
    + eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
      2: by apply eq_term_upto_univ_eta_lift.
      rewrite /eta_size !size_lambda_lift /=.
      lia.
    + eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
      2: by apply eq_term_upto_univ_eta_lift.
      rewrite /eta_size /= !size_lambda_lift.
      lia.
  
  - eapply lift_applies_eta ; auto.
    intros w' n e' s.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    + unfold eq_predicate in *.
      destruct e as (?&?&?&?), X as (?&?&?&?).
      repeat split.
      * destruct p, p', p'0 ; cbn in *.
        induction pparams in pparams0, pparams1, s, a2, a0, IH |- *.
        -- inversion a2 ; subst.
           cbn in a0 ; inversion a0 ; subst.
           cbn ; constructor.
        -- cbn in *.
           inversion a2 ; subst ; clear a2.
           cbn in a0 ; inversion a0 ; subst ; clear a0 ; cbn in s.
           constructor.
           ++ eapply (IH (_,(_,_))) ; rewrite /eta_size /= -/lift ; tea.
              2: by apply eq_term_upto_univ_eta_lift.
              rewrite !size_lambda_lift.
              lia.
           ++ eapply IHpparams ; eauto.
              2: lia.
              intros ; apply IH ; auto.
              cbn ; lia.
      * destruct p ; cbn in *.
        etransitivity ; eauto. 
      * etransitivity ; eauto.
      * destruct p, p' ; cbn in *.
        eapply (IH (_,(_,_))) ; rewrite -/lift /= ; tea.
        2: by rewrite (All2_fold_length a3) ; apply eq_term_upto_univ_eta_lift.
        rewrite /eta_size /= !size_lambda_lift ; cbn.
        ring_simplify.
        destruct p'0 ; cbn in *.
        lia.
      
    + eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
      2: by apply eq_term_upto_univ_eta_lift.
      rewrite /eta_size /= !size_lambda_lift.
      lia.
    + induction brs in brs', brs'0, s, X1, a, IH |- *.
      * inversion X1 ; subst.
        cbn in a ; inversion a ; subst.
        cbn ; constructor.
      * cbn in *.
        inversion X1 ; subst ; clear X1.
        destruct X2.
        cbn in a ; inversion a ; subst ; clear a ; cbn in s.
        destruct X1.
        constructor.
        -- split.
           1: etransitivity ; tea.
           eapply (IH (_,(_,_))) ; rewrite /eta_size /= -/lift ; tea.
           2: cbn ; rewrite (All2_fold_length a1) ; by apply eq_term_upto_univ_eta_lift.
           destruct y0 ; cbn in *.
           rewrite !size_lambda_lift /branch_size /=.
           lia.
        -- eapply IHbrs ; eauto.
           2: lia.
           intros ; apply IH ; auto.
           cbn ; lia.
  
  - eapply lift_applies_eta ; auto.
    intros w' n e' s.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
    2: by apply eq_term_upto_univ_eta_lift.
    rewrite /eta_size /= !size_lambda_lift.
    lia.

  - eapply lift_applies_eta ; auto.
    intros w' n e' s.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    rewrite (All2_length X).
    generalize dependent (#|mfix'| + 0) ; intros.
    induction mfix in mfix', mfix'0, s, X, a, IH |- *.
    + inversion X ; subst.
      cbn in a ; inversion a ; subst.
      cbn ; constructor.
    + cbn in *.
      inversion X ; subst ; clear X.
      cbn in a ; inversion a ; subst ; clear a ; cbn in s.
      constructor.
      * intuition auto.
        -- eapply (IH (_,(_,_))) ; rewrite /eta_size /= -/lift ; tea.
           2: by apply eq_term_upto_univ_eta_lift.
           rewrite !size_lambda_lift /def_size.
           destruct y0 ; cbn in *.
           lia.
        -- eapply (IH (_,(_,_))) ; rewrite /eta_size /= -/lift ; tea.
           2: by apply eq_term_upto_univ_eta_lift.
           rewrite !size_lambda_lift /def_size.
           destruct y0 ; cbn in *.
           lia.
        -- etransitivity ; tea.
        -- etransitivity ; tea.
      * eapply IHmfix ; eauto.
        2: rewrite /mfixpoint_size ; lia.
        intros ; apply IH ; auto.
        rewrite /mfixpoint_size in H0.
        cbn.
        lia.

  - eapply lift_applies_eta ; auto.
    intros w' n e' s.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    rewrite (All2_length X).
    generalize dependent (#|mfix'| + 0) ; intros.
    induction mfix in mfix', mfix'0, s, X, a, IH |- *.
    + inversion X ; subst.
      cbn in a ; inversion a ; subst.
      cbn ; constructor.
    + cbn in *.
      inversion X ; subst ; clear X.
      cbn in a ; inversion a ; subst ; clear a ; cbn in s.
      constructor.
      * intuition auto.
        -- eapply (IH (_,(_,_))) ; rewrite /eta_size /= -/lift ; tea.
            2: by apply eq_term_upto_univ_eta_lift.
            rewrite !size_lambda_lift /def_size.
            destruct y0 ; cbn in *.
            lia.
        -- eapply (IH (_,(_,_))) ; rewrite /eta_size /= -/lift ; tea.
            2: by apply eq_term_upto_univ_eta_lift.
            rewrite !size_lambda_lift /def_size.
            destruct y0 ; cbn in *.
            lia.
        -- etransitivity ; tea.
        -- etransitivity ; tea.
      * eapply IHmfix ; eauto.
        2: rewrite /mfixpoint_size ; lia.
        intros ; apply IH ; auto.
        rewrite /mfixpoint_size in H0.
        cbn.
        lia.
    
  - eapply lift_applies_eta ; auto.

Qed.

Lemma eta_expansion_eq_term Σ Re Rle f na A :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  eq_term_upto_univ_eta Σ Re Rle f (tLambda na A (tApp (lift0 1 f) (tRel 0))).
Proof.
  repeat constructor.
  reflexivity.
Qed.

Lemma admissible_application Σ Re Rle f g :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  eq_term_upto_univ_eta Σ Re Rle (tApp (lift0 1 f) (tRel 0)) (tApp (lift0 1 g) (tRel 0)) ->
  eq_term_upto_univ_eta Σ Re Rle f g.
Proof.
  intros.
  etransitivity.
  1: constructor.
  2: constructor.
  1: eassumption.
  reflexivity.
  Unshelve.
  all: repeat constructor.
Qed.

Instance eq_term_eta_trans {cf:checker_flags} Σ φ : Transitive (eq_term_eta Σ φ).
Proof.
  eapply eq_term_upto_univ_eta_trans. all: exact _.
Qed.

Instance leq_term_eta_trans {cf:checker_flags} Σ φ : Transitive (leq_term_eta Σ φ).
Proof.
  eapply eq_term_upto_univ_eta_trans ; exact _.
Qed.

Instance eq_term_upto_univ_eta_equiv Σ Re (hRe : RelationClasses.Equivalence Re)
  : Equivalence (eq_term_upto_univ_eta Σ Re Re).
Proof.
  constructor. all: exact _.
Defined.

Instance eq_context_equiv {cf} Σ φ : Equivalence (eq_context_gen (eq_term_eta Σ φ) (eq_term_eta Σ φ)).
Proof.
  constructor; try exact _.
Qed.

Instance leq_context_preord {cf} Σ φ : PreOrder (eq_context_gen (eq_term_eta Σ φ) (leq_term_eta Σ φ)).
Proof.
  constructor; try exact _.
Qed.

Instance eq_term_eta_equiv {cf:checker_flags} Σ φ : Equivalence (eq_term_eta Σ φ) :=
  {| Equivalence_Reflexive := eq_term_eta_refl _ _;
     Equivalence_Symmetric := eq_term_eta_sym _ _;
     Equivalence_Transitive := eq_term_eta_trans _ _ |}.

Instance leq_term_eta_preorder {cf:checker_flags} Σ φ : PreOrder (leq_term_eta Σ φ) :=
  {| PreOrder_Reflexive := leq_term_eta_refl _ _;
     PreOrder_Transitive := leq_term_eta_trans _ _ |}.

Instance R_global_instance_equiv Σ R (hR : RelationClasses.Equivalence R) gr
  : RelationClasses.Equivalence (R_global_instance Σ R R gr).
Proof.
  split.
  - intro. apply R_global_instance_refl; typeclasses eauto.
  - intros x y xy. eapply R_global_instance_sym; auto; typeclasses eauto.
  - intros x y z xy yz. eapply R_global_instance_trans; eauto; typeclasses eauto.
Qed.

Instance R_global_instance_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) gr :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_global_instance Σ Re Re gr) (R_global_instance Σ Re Rle gr).
Proof.
  intros hR u v.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance; auto.
  induction u in l, v |- *; destruct v, l; simpl; auto.
  intros [at' uv] [ta vu]. split; auto.
  destruct t0; simpl in *; auto.
Qed.

(*
  Lemma eq_term_upto_univ_eta_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) :
    RelationClasses.Antisymmetric _ Re Rle ->
    Antisymmetric (eq_term_upto_univ_eta Σ Re Re) (eq_term_upto_univ_eta Σ Re Rle).
  Proof.

  Qed.

  Instance leq_term_eta_antisym {cf:checker_flags} Σ φ
    : Antisymmetric (eq_term_eta Σ φ) (leq_term_eta Σ φ).
  Proof.
    eapply eq_term_upto_univ_eta_antisym; exact _.
  Qed.
*)

Instance R_global_instance_impl Σ Re Re' Rle Rle' gr :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (R_global_instance Σ Re Rle gr) (R_global_instance Σ Re' Rle' gr).
Proof.
  intros he hle t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:glob.
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  now eapply R_universe_instance_impl'.
Qed.

Lemma global_variance_empty gr : global_variance [] gr = None.
Proof.
  destruct gr; auto.
Qed.

(** Pure syntactic equality, without cumulative inductive types subtyping *)

Instance R_global_instance_empty_impl Σ Re Re' Rle Rle' gr :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance [] Re Rle gr) (R_global_instance Σ Re' Rle' gr).
Proof.
  intros he hle hele t t'.
  rewrite /R_global_instance /R_opt_variance. simpl.
  rewrite global_variance_empty.
  destruct global_variance as [v|]; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; intros H; inv H; auto.
  simpl.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Lemma onctx_eq_ctx_impl P ctx ctx' eq_term eq_term' :
  onctx P ctx ->
  (forall x, P x -> forall y, eq_term x y -> eq_term' x y) ->
  eq_context_gen eq_term eq_term ctx ctx' ->
  eq_context_gen eq_term' eq_term' ctx ctx'.
Proof.
  intros onc HP H1.
  induction H1; depelim onc; constructor; eauto; intuition auto; simpl in *.
  destruct o; depelim p; constructor; auto.
Qed.

Instance eq_term_upto_univ_eta_impl Σ Re Re' Rle Rle' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (eq_term_upto_univ_eta Σ Re Rle) (eq_term_upto_univ_eta Σ Re' Rle').
Proof.
  intros he hle hele t t' e.
  induction e in Rle', hle, hele |- * using eq_term_upto_univ_eta_list_ind.
  all: try solve [constructor;
         eauto using R_universe_instance_impl'].
  - constructor.
    eapply All2_impl; tea ; auto.
  - constructor.
    eapply R_global_instance_impl.
    3: eauto. all:auto.
  - constructor.
    eapply R_global_instance_impl.
    3:eauto. all:eauto.
  - constructor; unfold eq_predicate in *; eauto; solve_all.
    eapply R_universe_instance_impl'; eauto.
  - constructor.
    eapply All2_impl; tea.
    cbn. intros x y (?&?&?&?&?&?). repeat split; eauto.
  - constructor.
    eapply All2_impl; tea.
    cbn. intros x y (?&?&?&?&?&?). repeat split; eauto.
Qed.

Instance eq_term_upto_univ_eta_leq Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  subrelation (eq_term_upto_univ_eta Σ Re Re) (eq_term_upto_univ_eta Σ Re Rle).
Proof.
  intros H. eapply eq_term_upto_univ_eta_impl; exact _.
Qed.

Instance eq_term_leq_term_eta {cf:checker_flags} Σ φ
  : subrelation (eq_term_eta Σ φ) (leq_term_eta Σ φ).
Proof.
  eapply eq_term_upto_univ_eta_leq; auto; exact _.
Qed.

(*
  Instance leq_term_partial_order {cf:checker_flags} Σ φ
    : PartialOrder (eq_term_eta Σ φ) (leq_term_eta Σ φ).
  Proof.
    split. intros eqxy; split; now eapply eq_term_leq_term_eta.
    intros [xy yx].
    now eapply leq_term_eta_antisym.
Qed.
*)

Hint Constructors compare_decls : pcuic.


(* Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> eq_term_upto_univ _ _ ?u _ -> _ -> _
    |- eq_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
  end. *)  

Lemma eq_term_upto_univ_eta_substs Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_term_upto_univ_eta Σ Re Rle u v ->
    All2 (eq_term_upto_univ_eta Σ Re Re) l l' ->
    eq_term_upto_univ_eta Σ Re Rle (subst l n u) (subst l' n v).
Proof.
  unfold RelationClasses.subrelation; intros hR u v n l l' hu hl.
  induction hu in n, l, l', hl, hR |- * using eq_term_upto_univ_eta_list_ind.
  all: try solve [cbn ; constructor ; eauto].
  - cbn.
    constructor.
    rewrite -commut_lift_subst.
    apply IHhu ; auto.
  - cbn.
    constructor.
    rewrite -commut_lift_subst.
    apply IHhu ; auto.

  - cbn. destruct (Nat.leb_spec0 n n0).
    + case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply eq_term_upto_univ_eta_lift.
        eapply eq_term_upto_univ_eta_leq.
        all: auto.  
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn.
    destruct X as (? & ? & e & ?).
    constructor ; unfold eq_predicate; simpl; solve_all.
    * rewrite -(All2_fold_length e). eapply b; eauto.
    * rewrite (All2_fold_length a1). now eapply b1.
  - cbn. constructor ; eauto.
    pose proof (All2_length X).
    solve_all. now rewrite H.
  - cbn. constructor ; eauto.
    pose proof (All2_length X).
    solve_all. now rewrite H.
Qed.

Lemma eq_term_upto_univ_eta_subst Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n x y,
    eq_term_upto_univ_eta Σ Re Rle u v ->
    eq_term_upto_univ_eta Σ Re Re x y ->
    eq_term_upto_univ_eta Σ Re Rle (u{n := x}) (v{n := y}).
Proof.
  intros hR u v n x y e1 e2.
  eapply eq_term_upto_univ_eta_substs; eauto.
Qed.

Lemma subst_eq_term_eta {cf:checker_flags} Σ φ l k T U :
  eq_term_eta Σ φ T U ->
  eq_term_eta Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_eta_substs; try easy.
  now eapply All2_same.
Qed.

Lemma subst_leq_term_eta {cf:checker_flags} Σ φ l k T U :
  leq_term_eta Σ φ T U ->
  leq_term_eta Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_eta_substs; try easy.
  intro; apply eq_universe_leq_universe.
  now eapply All2_same.
Qed.

(** ** Boolean version **  *)

(* Section BooleanEqTerm.

  Variables (Σ : global_env) (equ lequ : Universe.t -> Universe.t -> bool).

Definition compare_global_instance Σ equ lequ gr :=
  match global_variance Σ gr with
  | Some v => compare_universe_instance_variance equ lequ v
  | None => compare_universe_instance equ
  end.

Definition eqb_binder_annots (x y : list aname) : bool :=
  forallb2 eqb_binder_annot x y.


Equations? eqb_term_upto_univ_eta (u u' : term) : bool
  by wf (size_lambda u + size_lambda u') lt :=

  eqb_term_upto_univ_eta (tRel n) (tRel n') := eqb n n' ;

  eqb_term_upto_univ_eta (tEvar e args) (tEvar e' args') :=
    eqb e e' && forallb2 (fun x y => eqb_term_upto_univ_eta x y) args args' ;

  eqb_term_upto_univ_eta (tVar id) (tVar id') := eqb id id' ;

  eqb_term_upto_univ_eta (tSort u) (tSort u') := lequ u u' ;

  eqb_term_upto_univ_eta (tApp u v) (tApp u' v') :=
    eqb_term_upto_univ_eta u u' && eqb_term_upto_univ_eta v v' ;

  eqb_term_upto_univ_eta (tConst c u) (tConst c' u') :=
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u') ;

  eqb_term_upto_univ_eta (tInd i u) (tInd i' u') :=
    eqb i i' &&
    compare_global_instance Σ equ lequ (IndRef i) u u' ;

  eqb_term_upto_univ_eta (tConstruct i k u) (tConstruct i' k' u') :=
    eqb i i' &&
    eqb k k' &&
    compare_global_instance Σ equ lequ (ConstructRef i k) u u' ;

  eqb_term_upto_univ_eta (tLambda na A t) (tLambda na' A' t') :=
    eqb_term_upto_univ_eta t t' ||
    eqb_term_upto_univ_eta (tApp (lift0 1 (tLambda na A t)) (tRel 0)) t' ||
    eqb_term_upto_univ_eta t (tApp (lift0 1 (tLambda na' A' t')) (tRel 0)) ;

  eqb_term_upto_univ_eta (tLambda na A t) v :=
    eqb_term_upto_univ_eta t (tApp (lift0 1 v) (tRel 0)) ;

  eqb_term_upto_univ_eta v (tLambda na A t) :=
    eqb_term_upto_univ_eta (tApp (lift0 1 v) (tRel 0)) t ;

  eqb_term_upto_univ_eta (tProd na A B) (tProd na' A' B') :=
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_eta A A' &&
    eqb_term_upto_univ_eta B B' ;

  eqb_term_upto_univ_eta (tLetIn na B b u) (tLetIn na' B' b' u') :=
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_eta B B' &&
    eqb_term_upto_univ_eta b b' &&
    eqb_term_upto_univ_eta u u' ;

  eqb_term_upto_univ_eta (tCase indp p c brs) (tCase indp' p' c' brs') :=
    eqb indp indp' &&
    eqb_predicate_gen
      (fun u u' => forallb2 equ (map Universe.make u) (map Universe.make u'))
      (bcompare_decls eqb eqb)
      (fun x y => eqb_term_upto_univ_eta x y) p p' &&
    eqb_term_upto_univ_eta c c' &&
    forallb2 (fun x y =>
      forallb2
        (bcompare_decls eqb eqb)
        x.(bcontext) y.(bcontext) &&
      eqb_term_upto_univ_eta (bbody x) (bbody y)
    ) brs brs' ;

  eqb_term_upto_univ_eta (tProj p c) (tProj p' c') :=
    eqb p p' &&
    eqb_term_upto_univ_eta c c' ;

  eqb_term_upto_univ_eta (tFix mfix idx) (tFix mfix' idx') :=
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_eta x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_eta x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ;

  eqb_term_upto_univ_eta (tCoFix mfix idx) (tCoFix mfix' idx') :=
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_eta x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_eta x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ;

  eqb_term_upto_univ_eta (tPrim p) (tPrim p') := eqb p p' ;

  eqb_term_upto_univ_eta v v' := false.
  Proof.
    all: try solve [cbn ; repeat rewrite size_lambda_lift ; lia].
    all: cbn ; ring_simplify.
    - admit.
    - rewrite list_size_map_hom.
      + symmetry ; apply size_lambda_lift.
      + lia.
    - rewrite list_size_map_hom.
      + symmetry ; apply size_lambda_lift.
      + lia.
    - rewrite /predicate_size /context_size !size_lambda_lift !list_size_map_hom.
      + symmetry ; apply size_lambda_lift.
      + by destruct x ; cbn ; rewrite size_lambda_lift. 
      + lia.
    - rewrite /mfixpoint_size !list_size_map_hom.
      + by intros [] ; cbn ; rewrite !size_lambda_lift.
      + lia.
    - rewrite /mfixpoint_size !list_size_map_hom.
      + by intros [] ; cbn ; rewrite !size_lambda_lift.
      + lia.
    - destruct p ; cbn.
      rewrite !size_lambda_lift !list_size_map_hom.
      + symmetry ; apply size_lambda_lift.
      + intros [] ; cbn ; by rewrite size_lambda_lift.  
      + lia.
    - admit.
    - admit.
    - rewrite /mfixpoint_size !list_size_map_hom.
      + by intros [] ; cbn ; rewrite !size_lambda_lift.
      + lia.
    - admit.
    - admit.
    - rewrite /mfixpoint_size !list_size_map_hom.
      + by intros [] ; cbn ; rewrite !size_lambda_lift.
      + lia.
    - admit.
    - admit.   
  Admitted.

End BooleanEqTerm. *)