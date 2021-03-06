(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Template Require Import config utils Reflect Ast AstUtils Induction LiftSubst Reflect.

Require Import ssreflect.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly 
  match the instances, so as to keep syntactic equality an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition R_universe_variance (Re Rle : Universe.t -> Universe.t -> Prop) v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => Rle (Universe.make u) (Universe.make u')
  | Variance.Invariant => Re (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance Re Rle v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => R_universe_instance_variance Re Rle v us us' 
      (* Missing variance stands for irrelevance, we still check that the instances have
        the same length. *)
    | v :: vs => R_universe_variance Re Rle v u u' /\
        R_universe_instance_variance Re Rle vs us us'
    end
  | [], [] => True
  | _, _ => False
  end.

Definition lookup_minductive Σ mind :=
  match lookup_env Σ mind with
  | Some (InductiveDecl decl) => Some decl
  | _ => None
  end.

Definition lookup_inductive Σ ind :=
  match lookup_minductive Σ (inductive_mind ind) with
  | Some mdecl => 
    match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
    | Some idecl => Some (mdecl, idecl)
    | None => None
    end
  | None => None
  end.

Definition lookup_constructor Σ ind k :=
  match lookup_inductive Σ ind with
  | Some (mdecl, idecl) => 
    match nth_error idecl.(ind_ctors) k with
    | Some cdecl => Some (mdecl, idecl, cdecl)
    | None => None
    end
  | _ => None
  end.

Definition global_variance Σ gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive Σ ind with
    | Some (mdecl, idecl) => 
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then mdecl.(ind_variance)
        else None
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor Σ ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.2 + mdecl.(ind_npars))%nat <=? napp then
        (** Fully applied constructors are always compared at the same supertype, 
          which implies that no universe equality needs to be checked here. *)
        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Definition R_opt_variance Re Rle v :=
  match v with 
  | Some v => R_universe_instance_variance Re Rle v
  | None => R_universe_instance Re
  end.

Definition R_global_instance Σ Re Rle gr napp :=
  R_opt_variance Re Rle (global_variance Σ gr napp).

Lemma R_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (R_universe_instance R) (R_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

Lemma R_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', R_universe_instance R u u' -> R_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

(** ** Syntactic equality up-to universes
  We don't look at printing annotations *)

(** Equality is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)  

Inductive eq_term_upto_univ_napp Σ (Re Rle : Universe.t -> Universe.t -> Prop) (napp : nat) : term -> term -> Type :=
| eq_Rel n  :
    eq_term_upto_univ_napp Σ Re Rle napp (tRel n) (tRel n)

| eq_Evar e args args' :
    All2 (eq_term_upto_univ_napp Σ Re Re 0) args args' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ_napp Σ Re Rle napp (tVar id) (tVar id)

| eq_Sort s s' :
    Rle s s' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tSort s) (tSort s')

| eq_App t t' u u' :
    eq_term_upto_univ_napp Σ Re Rle (#|u| + napp) t t' ->
    All2 (eq_term_upto_univ_napp Σ Re Re 0) u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tApp t u) (tApp t' u')

| eq_Const c u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConst c u) (tConst c u')

| eq_Ind i u u' :
    R_global_instance Σ Re Rle (IndRef i) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    R_global_instance Σ Re Rle (ConstructRef i k) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 t t' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 a a' ->
    eq_term_upto_univ_napp Σ Re Rle 0 b b' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 t t' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case indn p p' c c' brs brs' :
    eq_term_upto_univ_napp Σ Re Re 0 p p' ->
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    All2 (fun x y =>
      (fst x = fst y) *
      eq_term_upto_univ_napp Σ Re Re 0 (snd x) (snd y)
    ) brs brs' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tCase indn p c brs) (tCase indn p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tCoFix mfix idx) (tCoFix mfix' idx)
    
| eq_Cast t1 c t2 t1' c' t2' :
  eq_term_upto_univ_napp Σ Re Re 0 t1 t1' ->
  eq_cast_kind c c' ->
  eq_term_upto_univ_napp Σ Re Re 0 t2 t2' ->
  eq_term_upto_univ_napp Σ Re Rle napp (tCast t1 c t2) (tCast t1' c' t2')

| eq_Int i : eq_term_upto_univ_napp Σ Re Rle napp (tInt i) (tInt i)
| eq_Float f : eq_term_upto_univ_napp Σ Re Rle napp (tFloat f) (tFloat f).

Notation eq_term_upto_univ Σ Re Rle := (eq_term_upto_univ_napp Σ Re Rle 0).

(* ** Syntactic conversion up-to universes *)

Definition eq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Definition leq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (leq_universe φ).

  Lemma R_global_instance_refl Σ Re Rle gr napp u : 
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  R_global_instance Σ Re Rle gr napp u u.
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

Instance eq_binder_annot_equiv {A} : RelationClasses.Equivalence (@eq_binder_annot A).
Proof.
  split. 
  - red. reflexivity.
  - red; now symmetry.
  - intros x y z; unfold eq_binder_annot.
    congruence.
Qed. 

Definition eq_binder_annot_refl {A} x : @eq_binder_annot A x x.
Proof. reflexivity. Qed.

Hint Resolve @eq_binder_annot_refl : core.

Lemma eq_term_upto_univ_refl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  forall napp t, eq_term_upto_univ_napp Σ Re Rle napp t t.
Proof.
  intros hRe hRle napp.
  induction t in napp, Rle, hRle |- * using term_forall_list_rect; simpl;
    try constructor; try apply Forall_Forall2; try apply All_All2 ; try easy;
      try now (try apply Forall_All ; apply Forall_True).
  - eapply All_All2. 1: eassumption.
    intros. simpl in X0. easy.
  - destruct c; constructor.
  - eapply All_All2. 1: eassumption.
    intros. easy.
  - now apply R_global_instance_refl.
  - now apply R_global_instance_refl.
  - red in X. eapply All_All2. 1:eassumption.
    intros; easy.
  - eapply All_All2. 1: eassumption.
    simpl.
    intros x [? ?]. repeat split ; auto.
  - eapply All_All2. 1: eassumption.
    intros x [? ?]. repeat split ; auto.
Qed.

Lemma eq_term_refl `{checker_flags} Σ φ t : eq_term Σ φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - intro; apply eq_universe_refl.
  - intro; apply eq_universe_refl.
Qed.


Lemma leq_term_refl `{checker_flags} Σ φ t : leq_term Σ φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - intro; apply eq_universe_refl.
  - intro; apply leq_universe_refl.
Qed.
(* 
Lemma eq_term_leq_term `{checker_flags} Σ φ napp t u :
  eq_term_upto_univ_napp Σ napp φ t u -> leq_term Σ φ t u.
Proof.
  induction t in u |- * using term_forall_list_rect; simpl; inversion 1;
    subst; constructor; try (now unfold eq_term, leq_term in * );
  try eapply Forall2_impl' ; try eapply All2_impl' ; try easy.
  now apply eq_universe_leq_universe.
  all: try (apply Forall_True, eq_universe_leq_universe).
  apply IHt.
Qed. *)


Instance R_global_instance_impl_same_napp Σ Re Re' Rle Rle' gr napp :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp).
Proof.
  intros he hle t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:glob.
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  now eapply R_universe_instance_impl'.
Qed.

Lemma eq_term_upto_univ_morphism0 Σ (Re Re' : _ -> _ -> Prop)
      (Hre : forall t u, Re t u -> Re' t u)
  : forall t u napp, eq_term_upto_univ_napp Σ Re Re napp t u -> eq_term_upto_univ_napp Σ Re' Re' napp t u.
Proof.
  fix aux 4.
  destruct 1; constructor; eauto.
  all: unfold R_universe_instance in *.
  all: try solve[ match goal with
       | H : All2 _ _ _ |- _ => clear -H aux; induction H; constructor; eauto
       | H : Forall2 _ _ _ |- _ => induction H; constructor; eauto
       end].
  - eapply R_global_instance_impl_same_napp; eauto.
  - eapply R_global_instance_impl_same_napp; eauto.
  - induction a; constructor; auto. intuition auto.
  - induction a; constructor; auto. intuition auto.
  - induction a; constructor; auto. intuition auto.
Qed.

Lemma eq_term_upto_univ_morphism Σ (Re Re' Rle Rle' : _ -> _ -> Prop)
      (Hre : forall t u, Re t u -> Re' t u)
      (Hrle : forall t u, Rle t u -> Rle' t u)
  : forall t u napp, eq_term_upto_univ_napp Σ Re Rle napp t u -> eq_term_upto_univ_napp Σ Re' Rle' napp t u.
Proof.
  fix aux 4.
  destruct 1; constructor; eauto using eq_term_upto_univ_morphism0.
  all: unfold R_universe_instance in *.
  all: try solve [match goal with
       | H : Forall2 _ _ _ |- _ => induction H; constructor;
                                   eauto using eq_term_upto_univ_morphism0
       | H : All2 _ _ _ |- _ => induction H; constructor;
                                eauto using eq_term_upto_univ_morphism0
       end].
  - clear X. induction a; constructor; eauto using eq_term_upto_univ_morphism0.
  - eapply R_global_instance_impl_same_napp; eauto.
  - eapply R_global_instance_impl_same_napp; eauto.
  - clear X1 X2. induction a; constructor; eauto using eq_term_upto_univ_morphism0.
    destruct r. split; eauto using eq_term_upto_univ_morphism0.
  - induction a; constructor; eauto using eq_term_upto_univ_morphism0.
    destruct r as [[[? ?] ?] ?].
    repeat split; eauto using eq_term_upto_univ_morphism0.
  - induction a; constructor; eauto using eq_term_upto_univ_morphism0.
    destruct r as [[[? ?] ?] ?].
    repeat split; eauto using eq_term_upto_univ_morphism0.
Qed.


Lemma global_variance_napp_mon {Σ gr napp napp' v} : 
  napp <= napp' ->
  global_variance Σ gr napp = Some v ->
  global_variance Σ gr napp' = Some v.
Proof.
  intros hnapp.
  rewrite /global_variance.
  destruct gr; try congruence.
  - destruct lookup_inductive as [[mdecl idec]|] => //.
    destruct destArity as [[ctx s]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
  - destruct lookup_constructor as [[[mdecl idecl] cdecl]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
Qed.

Instance R_global_instance_impl Σ Re Re' Rle Rle' gr napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Re Rle' ->
  RelationClasses.subrelation Rle Rle' ->
  napp <= napp' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp').
Proof.
  intros he hle hele hnapp t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:glob.
  rewrite (global_variance_napp_mon hnapp glob).
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  destruct (global_variance _ _ napp') as [v|] eqn:glob'; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; auto; intros H; inv H.
  eauto.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Instance eq_term_upto_univ_impl Σ Re Re' Rle Rle' napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ Re Rle napp) (eq_term_upto_univ_napp Σ Re' Rle' napp').
Proof.
  intros he hle hele hnapp t t'.
  induction t in napp, napp', hnapp, t', Rle, Rle', hle, hele |- * using term_forall_list_rect;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply IHt. 4:eauto. all:auto with arith. eauto.
    solve_all.
  - inversion 1; subst; constructor.
    eapply R_global_instance_impl. 5:eauto. all:auto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_impl. 5:eauto. all:eauto.
  - inversion 1; subst; constructor; eauto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x ? y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
Qed.


Lemma eq_term_leq_term `{checker_flags} Σ φ t u :
  eq_term Σ φ t u -> leq_term Σ φ t u.
Proof.
  eapply eq_term_upto_univ_morphism. auto.
  intros.
  now apply eq_universe_leq_universe.
Qed.

Lemma eq_term_upto_univ_App `{checker_flags} Σ Re Rle napp f f' :
  eq_term_upto_univ_napp Σ Re Rle napp f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_App `{checker_flags} Σ φ f f' :
  eq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps `{checker_flags} Σ Re Rle napp f l f' l' :
  eq_term_upto_univ_napp Σ Re Rle (#|l| + napp) f f' ->
  All2 (eq_term_upto_univ Σ Re Re) l l' ->
  eq_term_upto_univ_napp Σ Re Rle napp (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - pose proof (eq_term_upto_univ_App _ _ _ _ _ _ e).
    case_eq (isApp f).
    + intro X; rewrite X in H0.
      destruct f; try discriminate.
      destruct f'; try discriminate.
      cbn. inversion_clear e. constructor.
      rewrite app_length /= -Nat.add_assoc //.
      apply All2_app. assumption.
      now constructor.
    + intro X; rewrite X in H0.
      rewrite !mkApps_tApp; eauto.
      intro; discriminate.
      intro; discriminate.
      constructor. simpl. now simpl in e.
      now constructor.
Qed.

Lemma leq_term_mkApps `{checker_flags} Σ φ f l f' l' :
  leq_term Σ φ f f' ->
  All2 (eq_term Σ φ) l l' ->
  leq_term Σ φ (mkApps f l) (mkApps f' l').
Proof.
  intros.
  eapply eq_term_upto_univ_mkApps.
  eapply eq_term_upto_univ_impl. 5:eauto. 4:auto with arith.
  1-3:typeclasses eauto.
  apply X0.
Qed.

Lemma leq_term_App `{checker_flags} Σ φ f f' :
  leq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.