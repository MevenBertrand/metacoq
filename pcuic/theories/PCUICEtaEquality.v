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

Lemma structural_transitivity Σ Re Rle t t' w:
   ~ isLambda t' ->
  (forall w' n (e : eq_term_upto_univ_eta Σ Re Rle (lift0 n t') w'),
    size_lambda w' <= size_lambda w -> ~ isEta e ->
    eq_term_upto_univ_eta Σ Re Rle (lift0 n t) w') ->
  eq_term_upto_univ_eta Σ Re Rle t' w ->
  eq_term_upto_univ_eta Σ Re Rle t w.
Proof.
  intros iLt base.
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

  - eapply structural_transitivity ; auto.

  - eapply structural_transitivity ; auto.
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
  
  - eapply structural_transitivity ; auto.

  - eapply structural_transitivity ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion_clear e' ; try solve [cbn ; congruence].
    intros _.
    constructor ; eauto.

  - eapply structural_transitivity ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    all: eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
    2,4: by apply eq_term_upto_univ_eta_lift.
    all: rewrite /eta_size /= !size_lambda_lift ; lia.

  - eapply structural_transitivity ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    etransitivity ; eauto.
    
  - eapply structural_transitivity ; auto.
    intros w' n e' ?.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    etransitivity ; eauto.

  - eapply structural_transitivity ; auto.
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
      eapply structural_transitivity ; tea.
      1: cbn ; congruence.
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

  - eapply structural_transitivity ; auto.
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

  - eapply structural_transitivity ; auto.
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
  
  - eapply structural_transitivity ; auto.
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
  
  - eapply structural_transitivity ; auto.
    intros w' n e' s.
    cbn in *.
    dependent inversion e' ; subst ; clear e' ; cbn in * ; try solve [congruence].
    intros _.
    constructor ; eauto.
    eapply (IH (_,(_,_))) ; rewrite -/lift /= ; eauto.
    2: by apply eq_term_upto_univ_eta_lift.
    rewrite /eta_size /= !size_lambda_lift.
    lia.

  - eapply structural_transitivity ; auto.
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

  - eapply structural_transitivity ; auto.
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
    
  - eapply structural_transitivity ; auto.

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

Section BooleanEqTerm.

Definition compare_global_instance Σ equ lequ gr :=
  match global_variance Σ gr with
  | Some v => compare_universe_instance_variance equ lequ v
  | None => compare_universe_instance equ
  end.

Definition eqb_binder_annots (x y : list aname) : bool :=
  forallb2 eqb_binder_annot x y.


Equations forallb2_In {A : Type} (l l' : list A) 
  (R : forall (x x' : A), In x l -> In x' l' -> bool) : bool :=
forallb2_In nil nil _ := true ;
forallb2_In (cons x xs) (cons x' xs') _ :=
  (R x x' _ _) && (forallb2_In xs xs' (fun x x' H H' => R x x' _ _)) ;
forallb2_In _ _ _ := false.

Lemma forallb2_In_spec {A : Type} (R : A -> A -> bool) (l l' : list A) :
  forallb2_In l l' (fun (x x' : A) (_ : In x l) (_ : In x' l') => R x x') = forallb2 R l l'.
Proof.
  remember (fun (x x' : A) (_ : In x l) (_ : In x' l') => R x x') as g.
  funelim (forallb2_In l l' g) => //=.
  rewrite <- (H R0) ; trivial.
Qed.

Lemma In_list_size {A : Type} (f : A -> nat) :
  forall x xs, In x xs -> f x < S (list_size f xs).
Proof.
  intros.
  induction xs.
  1: by destruct H.
  destruct H ; subst ; cbn.
  1: lia.
  specialize (IHxs H).
  lia.
Qed.

#[program] Definition forallb2_term t t'
  (eqb_term : forall x x', size_lambda x + size_lambda x' < size_lambda t + size_lambda t' -> bool)
  (l l' : list term)
  (H : list_size size_lambda l + list_size size_lambda l' < size_lambda t + size_lambda t') :=
    (forallb2_In l l' (fun x x' (H : In x l) (H' : In x' l') => eqb_term x x' _)).
  Next Obligation.
    apply (In_list_size size_lambda) in H.
    apply (In_list_size size_lambda) in H'.
    lia.
  Qed.

#[program] Definition forallb2_def t t'
  (eqb_term : forall x x',
    def_size size_lambda x + def_size size_lambda x' < size_lambda t + size_lambda t' -> bool)
  (l l' : list (def term))
  (H : mfixpoint_size size_lambda l + mfixpoint_size size_lambda l' < size_lambda t + size_lambda t') :=
    (forallb2_In l l' (fun x x' (H : In x l) (H' : In x' l') => eqb_term x x' _)).
  Next Obligation.
    apply (In_list_size (def_size size_lambda)) in H.
    apply (In_list_size (def_size size_lambda)) in H'.
    unfold mfixpoint_size in H0.
    lia.
  Qed.

#[program] Definition forallb2_brs t t'
  (eqb_term : forall x x',
    branch_size size_lambda x + branch_size size_lambda x' < size_lambda t + size_lambda t' -> bool)
  (l l' : list (branch term))
  (H : list_size (branch_size size_lambda) l + list_size (branch_size size_lambda) l'
    < size_lambda t + size_lambda t') :=
    (forallb2_In l l' (fun x x' (H : In x l) (H' : In x' l') => eqb_term x x' _)).
  Next Obligation.
    apply (In_list_size (branch_size size_lambda)) in H.
    apply (In_list_size (branch_size size_lambda)) in H'.
    lia.
  Qed.

#[program] Definition eqb_predicate_gen_size t t'
  (eqb_univ_instance : Instance.t -> Instance.t -> bool)
  (eqdecl : context_decl -> context_decl -> bool)
  (eqb_term : forall x x',
    size_lambda x + size_lambda x' < size_lambda t + size_lambda t'
    -> bool)
  (p p' : predicate term)
  (H : predicate_size size_lambda p + predicate_size size_lambda p' < size_lambda t + size_lambda t')
  :=
  forallb2_In (pparams p) (pparams p')
    (fun x x' (H : In x (pparams p)) (H' : In x' (pparams p')) => eqb_term x x' _) &&
  eqb_univ_instance (puinst p) (puinst p') &&
  forallb2 eqdecl (pcontext p) (pcontext p') &&
  eqb_term (preturn p) (preturn p') _.
  Next Obligation.
    apply (In_list_size size_lambda) in H.
    apply (In_list_size size_lambda) in H'.
    rewrite /predicate_size in H0.
    lia.
  Qed.
  Next Obligation.
    rewrite /predicate_size in H.
    lia.
  Qed.

Equations? eqb_term_upto_univ_eta Σ equ lequ
  (u u' : term) : bool
  by wf (size_lambda u + size_lambda u') lt :=

  eqb_term_upto_univ_eta Σ equ lequ (tRel n) (tRel n') := eqb n n' ;

  eqb_term_upto_univ_eta Σ equ lequ (tEvar e args) (tEvar e' args') :=
    eqb e e' && forallb2_term (tEvar e args) (tEvar e' args') (fun x y H => eqb_term_upto_univ_eta Σ equ equ x y) args args' _ ;

  eqb_term_upto_univ_eta Σ equ lequ (tVar id) (tVar id') := eqb id id' ;

  eqb_term_upto_univ_eta Σ equ lequ (tSort u) (tSort u') := lequ u u' ;

  eqb_term_upto_univ_eta Σ equ lequ (tApp u v) (tApp u' v') :=
    eqb_term_upto_univ_eta Σ equ lequ u u' && eqb_term_upto_univ_eta Σ equ lequ v v' ;

  eqb_term_upto_univ_eta Σ equ lequ (tConst c u) (tConst c' u') :=
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u') ;

  eqb_term_upto_univ_eta Σ equ lequ (tInd i u) (tInd i' u') :=
    eqb i i' &&
    compare_global_instance Σ equ lequ (IndRef i) u u' ;

  eqb_term_upto_univ_eta Σ equ lequ (tConstruct i k u) (tConstruct i' k' u') :=
    eqb i i' &&
    eqb k k' &&
    compare_global_instance Σ equ lequ (ConstructRef i k) u u' ;

  eqb_term_upto_univ_eta Σ equ lequ (tLambda na A t) (tLambda na' A' t') :=
    eqb_term_upto_univ_eta Σ equ lequ t t' ||
    eqb_term_upto_univ_eta Σ equ lequ (tApp (lift0 1 (tLambda na A t)) (tRel 0)) t' ||
    eqb_term_upto_univ_eta Σ equ lequ t (tApp (lift0 1 (tLambda na' A' t')) (tRel 0)) ;

  eqb_term_upto_univ_eta Σ equ lequ (tLambda na A t) v :=
    eqb_term_upto_univ_eta Σ equ lequ t (tApp (lift0 1 v) (tRel 0)) ;

  eqb_term_upto_univ_eta Σ equ lequ v (tLambda na A t) :=
    eqb_term_upto_univ_eta Σ equ lequ (tApp (lift0 1 v) (tRel 0)) t ;

  eqb_term_upto_univ_eta Σ equ lequ (tProd na A B) (tProd na' A' B') :=
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_eta Σ equ equ A A' &&
    eqb_term_upto_univ_eta Σ equ lequ B B' ;

  eqb_term_upto_univ_eta Σ equ lequ (tLetIn na B b u) (tLetIn na' B' b' u') :=
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_eta Σ equ equ B B' &&
    eqb_term_upto_univ_eta Σ equ lequ b b' &&
    eqb_term_upto_univ_eta Σ equ lequ u u' ;

  eqb_term_upto_univ_eta Σ equ lequ (tCase indp p c brs) (tCase indp' p' c' brs') :=
    eqb indp indp' &&
    eqb_predicate_gen_size (tCase indp p c brs) (tCase indp' p' c' brs')
      (fun u u' => forallb2 equ (map Universe.make u) (map Universe.make u'))
      (bcompare_decls eqb eqb)
      (fun x y H => eqb_term_upto_univ_eta Σ equ equ x y) p p' _ &&
    eqb_term_upto_univ_eta Σ equ equ c c' &&
    forallb2_brs (tCase indp p c brs) (tCase indp' p' c' brs') (fun x y H =>
      forallb2
        (bcompare_decls eqb eqb)
        x.(bcontext) y.(bcontext) &&
      eqb_term_upto_univ_eta Σ equ equ (bbody x) (bbody y)
    ) brs brs' _ ;

  eqb_term_upto_univ_eta Σ equ lequ (tProj p c) (tProj p' c') :=
    eqb p p' &&
    eqb_term_upto_univ_eta Σ equ equ c c' ;

  eqb_term_upto_univ_eta Σ equ lequ (tFix mfix idx) (tFix mfix' idx') :=
    eqb idx idx' &&
    forallb2_def (tFix mfix idx) (tFix mfix' idx') (fun x x' H =>
      eqb_term_upto_univ_eta Σ equ equ x.(dtype) x'.(dtype) &&
      eqb_term_upto_univ_eta Σ equ equ x.(dbody) x'.(dbody) &&
      eqb x.(rarg) x'.(rarg) &&
      eqb_binder_annot x.(dname) x'.(dname)
    ) mfix mfix' _ ;

  eqb_term_upto_univ_eta Σ equ lequ (tCoFix mfix idx) (tCoFix mfix' idx') :=
  eqb idx idx' &&
  forallb2_def (tFix mfix idx) (tFix mfix' idx') (fun x x' H =>
    eqb_term_upto_univ_eta Σ equ equ x.(dtype) x'.(dtype) &&
    eqb_term_upto_univ_eta Σ equ equ x.(dbody) x'.(dbody) &&
    eqb x.(rarg) x'.(rarg) &&
    eqb_binder_annot x.(dname) x'.(dname)
  ) mfix mfix' _ ;

  eqb_term_upto_univ_eta Σ equ lequ (tPrim p) (tPrim p') := eqb p p' ;

  eqb_term_upto_univ_eta Σ equ lequ v v' := false.
  Proof.
    all: try solve [cbn ; repeat rewrite size_lambda_lift ; lia].
    all: cbn ; ring_simplify.
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
    - rewrite {1 2}/branch_size in H.
      lia.
    - rewrite /mfixpoint_size !list_size_map_hom.
      + by intros [] ; cbn ; rewrite !size_lambda_lift.
      + lia.
    - rewrite /def_size /= in H.
      lia.
    - rewrite /def_size /= in H.
      lia.
    - rewrite /mfixpoint_size !list_size_map_hom.
      + by intros [] ; cbn ; rewrite !size_lambda_lift.
      + lia.
    - rewrite /def_size /= in H.
      lia.
    - rewrite /def_size /= in H.
      lia.
  Defined.

End BooleanEqTerm.

Lemma iffPT : forall P Q b, reflectT P b -> (P -> Q) -> (Q -> P) -> reflectT Q b.
Proof.
  intros.
  case X.
  all : intros ; constructor ; auto.
Qed.

Lemma reflect_eq_term_upto_univ_eta Σ equ lequ (Re Rle : Universe.t -> Universe.t -> Prop) :
  (forall u u', reflectT (Re u u') (equ u u')) ->
  (forall u u', reflectT (Rle u u') (lequ u u')) ->
  forall t t', reflectT (eq_term_upto_univ_eta Σ Re Rle t t')
                   (eqb_term_upto_univ_eta Σ equ lequ t t').
Proof.
  intros he hle t t'.
  revert Re Rle he hle.
  apply_funelim (eqb_term_upto_univ_eta Σ equ lequ t t') ;
  clear ; intros ;
  match goal with
    | |- reflectT _ false => constructor ; intros H ; inversion H
    | X : context [reflectT (eq_term_upto_univ_eta _ _ _ (tApp _ _) _)] |- 
      reflectT (eq_term_upto_univ_eta _ _ _ _ (tLambda _ _ _)) _ =>
      by edestruct X ; tea ; constructor ; [constructor | intros Heq ; inversion Heq ]
    | X : context [reflectT (eq_term_upto_univ_eta _ _ _ _ (tApp _ _))] |- 
      reflectT (eq_term_upto_univ_eta _ _ _ (tLambda _ _ _) _) _ =>
      by edestruct X ; tea ; constructor ; [constructor | intros Heq ; inversion Heq ]
    | |- _ => idtac
  end.
 
  - eqspecs.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs.
    cbn in *.
    rewrite /forallb2_term forallb2_In_spec.
    intros.
    eapply iffPT.
    1: by apply All2P.
    + intros. constructor.
      induction X0 ; constructor.
      * eapply elimT.
      1: eapply X ; eauto ; cbn ; lia.
      eassumption.
      * apply IHX0.
        intros.
        apply X ; auto.
        cbn ; lia.
    + intros H ; inversion H ; subst.
      induction X0 ; constructor.
      * eapply introT.
        1: eapply X ; eauto ; cbn ; lia.
        eassumption.
      * apply IHX0.
        2: by constructor.
        intros.
        apply X ; auto.
        cbn ; lia.
  - destruct (hle u u0) ; nodec.
    constructor. constructor. assumption.
  - destruct (eqb_annot_reflect na na0) ; cbn in * ; nodec.
    destruct (X _ _ he he) ; nodec.
    destruct (X0 _ _ he hle) ; nodec.
    constructor. constructor; assumption.
  - destruct (X _ _ he hle).
    1:{ by repeat constructor. }
    destruct (X0 _ _ he hle).
    1:{ constructor. by apply eq_Eta_l. }
    destruct (X1 _ _ he hle).
    1:{ constructor. by apply eq_Eta_r. }
    nodec.
Admitted. 
     
Lemma compare_global_instance_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) gr u,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    compare_global_instance Σ eqb leqb gr u u.
Proof.
  intros Σ eqb leqb gr u eqb_refl leqb_refl.
  rewrite /compare_global_instance.
  destruct global_variance as [v|].
  induction u in v |- *; destruct v; simpl; auto.
  rtoProp. split; auto.
  destruct t; simpl; auto.
  rewrite /compare_universe_instance.
  rewrite forallb2_map; eapply forallb2_refl; intro; apply eqb_refl.
Qed.

Lemma eqb_term_upto_univ_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) t,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    eqb_term_upto_univ_eta Σ eqb leqb t t.
Proof.
  intros Σ eqb leqb t eqb_refl leqb_refl.
  case: (reflect_eq_term_upto_univ_eta Σ eqb leqb eqb leqb _ _ t t) => //.
  * intros. eapply equiv_reflectT; auto.
  * intros. eapply equiv_reflectT; auto.
  * intros.
    unshelve epose proof (eq_term_upto_univ_eta_refl Σ eqb leqb _ _); eauto.
Qed.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma eq_term_upto_univ_eta_mkApps Σ Re Rle u1 l1 u2 l2 :
    eq_term_upto_univ_eta Σ Re Rle u1 u2 ->
    All2 (eq_term_upto_univ_eta Σ Re Re) l1 l2 ->
    eq_term_upto_univ_eta Σ Re Rle (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

(** ** Equality on contexts ** *)

Notation eq_context_upto_eta Σ Re Rle := 
  (eq_context_gen (eq_term_upto_univ_eta Σ Re Re) (eq_term_upto_univ_eta Σ Re Rle)).

Definition eq_decl_upto_eta_gen Σ Re Rle d d' : Type :=
  eq_binder_annot d.(decl_name) d'.(decl_name) ×
  rel_option (eq_term_upto_univ_eta Σ Re Re) d.(decl_body) d'.(decl_body) ×
  eq_term_upto_univ_eta Σ Re Rle d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto_eta Σ Re Rle :
  subrelation (All2 (eq_decl_upto_eta_gen Σ Re Rle)) (eq_context_upto_eta Σ Re Rle).
Proof.
  intros Γ Δ h.
  induction h.
  - constructor.
  - destruct r as (h1 & h2 & h3).
    destruct x as [na bo ty], y as [na' bo' ty'].
    simpl in h1, h2.
    destruct h2.
    + constructor ; eauto. constructor; auto.
    + constructor ; eauto. constructor; auto.
Qed.

Lemma eq_context_upto_eta_refl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_context_upto_eta Σ Re Rle).
Proof. exact _. Qed.

Lemma eq_context_upto_eta_sym Σ Re Rle :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_context_upto_eta Σ Re Rle).
Proof. exact _. Qed.

Lemma eq_context_upto_eta_cat Σ Re Rle Γ Δ Γ' Δ' :
  eq_context_upto_eta Σ Re Rle Γ Γ' ->
  eq_context_upto_eta Σ Re Rle Δ Δ' ->
  eq_context_upto_eta Σ Re Rle (Γ ,,, Δ) (Γ' ,,, Δ').
Proof. intros. eapply All2_fold_app; eauto. Qed.

Lemma eq_context_upto_rev Σ Re Rle Γ Δ :
  eq_context_upto_eta Σ Re Rle Γ Δ ->
  eq_context_upto_eta Σ Re Rle (rev Γ) (rev Δ).
Proof.
  induction 1.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_eta_cat ; eauto.
    constructor ; eauto. constructor.
Qed.

Lemma eq_context_upto_eta_rev' :
  forall Σ Γ Δ Re Rle,
    eq_context_upto_eta Σ Re Rle Γ Δ ->
    eq_context_upto_eta Σ Re Rle (List.rev Γ) (List.rev Δ).
Proof.
  intros Σ Γ Δ Re Rle h.
  induction h.
  - constructor.
  - simpl. eapply eq_context_upto_eta_cat.
    + repeat constructor; assumption.
    + assumption.
Qed.

Lemma eq_context_upto_eta_length :
  forall {Σ Re Rle Γ Δ},
    eq_context_upto_eta Σ Re Rle Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Σ Re Rle Γ Δ h.
  induction h. all: simpl ; auto.
Qed.

Lemma eq_context_upto_eta_subst_context Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_context_upto_eta Σ Re Rle u v ->
    All2 (eq_term_upto_univ_eta Σ Re Re) l l' ->
    eq_context_upto_eta Σ Re Rle (subst_context l n u) (subst_context l' n v).
Proof.
  intros re u v n l l'.
  induction 1; intros Hl.
  - rewrite !subst_context_nil. constructor.
  - rewrite !subst_context_snoc; constructor; eauto.
    depelim p ; constructor ; simpl; intuition auto ;
    rewrite -(length_of X);
    apply eq_term_upto_univ_eta_substs; auto. reflexivity.
Qed.

Hint Resolve All2_fold_nil : pcuic.

Lemma eq_context_upto_eta_smash_context Σ ctx ctx' x y :
  eq_context_upto_eta Σ eq eq ctx ctx' -> eq_context_upto_eta Σ eq eq x y -> 
  eq_context_upto_eta Σ eq eq (smash_context ctx x) (smash_context ctx' y).
Proof.
  induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl; 
    try split; auto; try constructor; auto. depelim X0 => /=.
  - apply IHx; auto. apply eq_context_upto_eta_cat; auto.
    constructor; pcuic.
  - apply IHx; auto. eapply eq_context_upto_eta_subst_context; eauto.
    typeclasses eauto.
Qed.

Lemma eq_context_upto_eta_nth_error Σ Re Rle ctx ctx' n :
  eq_context_upto_eta Σ Re Rle ctx ctx' -> 
  rel_option (eq_decl_upto_eta_gen Σ Re Rle) (nth_error ctx n) (nth_error ctx' n).
Proof.
  induction 1 in n |- *.
  - rewrite nth_error_nil. constructor.
  - destruct n; simpl; auto. 
    constructor. depelim p; constructor; intuition auto;
    now constructor.
Qed.

Lemma eq_context_impl :
  forall Σ Re Re' Rle Rle',
    RelationClasses.subrelation Re Re' ->
    RelationClasses.subrelation Rle Rle' ->
    RelationClasses.subrelation Re' Rle' ->
    subrelation (eq_context_upto_eta Σ Re Rle) (eq_context_upto_eta Σ Re' Rle').
Proof.
  intros Σ Re Re' Rle Rle' hR hR' hReRle' Γ Δ h.
  induction h.
  - constructor.
  - constructor; auto. 
    depelim p; constructor; auto.
    all:eapply eq_term_upto_univ_eta_impl.
    4,8,12:tea. all:eauto.
    all:now transitivity Re'.
Qed.

Lemma eq_term_upto_univ_eta_it_mkLambda_or_LetIn Σ Re Rle :
    RelationClasses.Reflexive Re ->
    Proper (eq_context_upto_eta Σ Re Re ==> eq_term_upto_univ_eta Σ Re Rle ==> eq_term_upto_univ_eta Σ Re Rle) it_mkLambda_or_LetIn.
Proof.
  intros he Γ Δ eq u v h.
  induction eq in u, v, h, he |- *.
  - assumption.
  - simpl. cbn. apply IHeq => //.
    destruct p; cbn; constructor ; tas; try reflexivity.
Qed.

Lemma eq_term_upto_univ_eta_it_mkLambda_or_LetIn_r Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ_eta Σ Re Rle) (eq_term_upto_univ_eta Σ Re Rle)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
Qed.

Lemma eq_term_eta_it_mkLambda_or_LetIn {cf:checker_flags} Σ φ Γ :
  respectful (eq_term_eta Σ φ) (eq_term_eta Σ φ)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  apply eq_term_upto_univ_eta_it_mkLambda_or_LetIn_r; exact _.
Qed.

Lemma eq_term_upto_univ_eta_it_mkProd_or_LetIn Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ_eta Σ Re Rle) (eq_term_upto_univ_eta Σ Re Rle)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
Qed.

Lemma eq_term_eta_it_mkProd_or_LetIn {cf:checker_flags} Σ φ Γ:
  respectful (eq_term_eta Σ φ) (eq_term_eta Σ φ)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  eapply eq_term_upto_univ_eta_it_mkProd_or_LetIn ; exact _.
Qed.

Definition compare_term_eta `{checker_flags} (le : bool) Σ φ (t u : term) :=
  if le then leq_term_eta Σ φ t u else eq_term_eta Σ φ t u.

Lemma lift_compare_term_eta `{checker_flags} le Σ ϕ n k t t' :
  compare_term_eta le Σ ϕ t t' -> compare_term_eta le Σ ϕ (lift n k t) (lift n k t').
Proof.
  destruct le; intros. now apply lift_leq_term_eta. now apply lift_eq_term_eta.
Qed.

Definition eq_decl_eta `{checker_flags} le Σ φ (d d' : context_decl) :=
  compare_decls (eq_term_eta Σ φ) (if le then leq_term_eta Σ φ else eq_term_eta Σ φ) d d'.

Definition eq_context_eta `{checker_flags} le Σ φ (Γ Δ : context) :=
  eq_context_gen (eq_term_eta Σ φ) (if le then leq_term_eta Σ φ else eq_term_eta Σ φ) Γ Δ.

Lemma lift_compare_decls `{checker_flags} le Σ ϕ n k d d' :
  eq_decl_eta le Σ ϕ d d' -> eq_decl_eta le Σ ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  intros []; destruct le; constructor; cbn; intuition auto using lift_compare_term_eta, lift_eq_term_eta, lift_leq_term_eta.
Qed.

Lemma lift_eq_context_eta `{checker_flags} le Σ φ l l' n k :
  eq_context_eta le Σ φ l l' ->
  eq_context_eta le Σ φ (lift_context n k l) (lift_context n k l').
Proof.
  unfold eq_context_eta.
  induction 1; rewrite -> ?lift_context_snoc0. constructor.
  constructor; auto. 
  eapply lift_compare_decls in p.
  now rewrite (All2_fold_length X).
Qed.

Lemma R_global_instance_flip Σ gr
  (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v:
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  R_global_instance Σ Re Rle gr u v ->
  R_global_instance Σ Re Rle' gr v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [vs|] eqn:var.  
  - induction u in vs, v |- *; destruct v; simpl; auto;
    destruct vs as [|v' vs]; simpl; auto.
    intros [Ra Ru']. split.
    destruct v'; simpl; auto.
    apply IHu; auto.
  - apply Forall2_symP; eauto.
Qed.

Lemma eq_term_upto_univ_eta_flip Σ (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  eq_term_upto_univ_eta Σ Re Rle u v ->
  eq_term_upto_univ_eta Σ Re Rle' v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl' H.
  assert (Resub : RelationClasses.subrelation Re Re).
  { typeclasses eauto. }
  revert Rerefl Rlerefl Resym Retrans Rletrans incl incl' Resub.
  revert Re Rle u v H Rle'.
  induction 1; intros; constructor; intuition auto.
  all:try solve [now symmetry].
  all:eauto using R_global_instance_flip.
  - eapply All2_sym. solve_all.
    * eapply eq_context_sym; try tc. tas. 
    * now symmetry.
  - eapply All2_sym. solve_all.
    all: now symmetry.
  - eapply All2_sym. solve_all.
    all: now symmetry.
Qed.