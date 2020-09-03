(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program Arith Lia CRelationClasses.
From MetaCoq.Template Require Import config utils monad_utils EnvironmentTyping Universes.
From MetaCoq.PCUIC Require Import PCUICUtils.
From MetaCoq.EGCIC Require Import EGCICAst EGCICAstUtils
EGCICLiftSubst EGCICUnivSubst EGCICEquality EGCICPosition EGCICConsistency.

From MetaCoq Require Export LibHypsNaming.

Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
From Equations Require Import Equations.
Import MonadNotation.

Module EGCICLookup := Lookup EGCICTerm EGCICEnvironment.
Include EGCICLookup.

Module EGCICEnvTyping := EnvTyping EGCICTerm EGCICEnvironment.
Include EGCICEnvTyping.

(** ** Reduction *)

(** *** Helper functions for reduction *)

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => eFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => eCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.

Lemma fix_subst_length mfix : #|fix_subst mfix| = #|mfix|.
Proof.
  unfold fix_subst. generalize (eFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (eCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.rev_length mapi_length. Qed.

Definition eDummy := eVar String.EmptyString.

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, eDummy))) (List.skipn npar args)).


(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Local Open Scope type_scope.
Arguments OnOne2 {A} P%type l l'.

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
(** Reductions *)
(** Beta *)
| red_beta na t b a :
    red1 Σ Γ (eApp (eLambda na t b) a) (subst10 a b)

| red_beta_err na A B e a :
    red1 Σ Γ (eApp (eErr e (eProd na A B)) a) (eErr e (subst10 a B))

(** Let *)
| red_zeta na b t b' :
    red1 Σ Γ (eLetIn na b t b') (subst10 b b')

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    red1 Σ Γ (eRel i) (lift0 (S i) body)

(** Case *)
| red_iota ind pars c u args p brs :
    red1 Σ Γ (eCase (ind, pars) p (mkApps (eConstruct ind c u) args) brs)
         (iota_red pars c args brs)

(*| red_iota ind pars u p l e brs :
    red1 Σ Γ (eCase (ind, pars) p (eErr l e (mkApps (eInd ind u) args)) brs)
            eErr l e 
missing : red_iota_err *)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (mkApps (eFix mfix idx) args) (mkApps fn args)

(** CoFix-case unfolding *)
| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (eCase ip p (mkApps (eCoFix mfix idx) args) brs)
         (eCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (eProj p (mkApps (eCoFix mfix idx) args))
         (eProj p (mkApps fn args))

(** Constant unfolding *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Γ (eConst c u) (subst_instance_constr u body)

(** Proj *)
| red_proj i pars narg args k u arg:
    nth_error args (pars + narg) = Some arg ->
    red1 Σ Γ (eProj (i, pars, narg) (mkApps (eConstruct i k u) args)) arg

(** TODO: cast reduction *)    

| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (eLambda na M N) (eLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (eLambda na N M) (eLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (eLetIn na b t b') (eLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (eLetIn na b t b') (eLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (eLetIn na b t b') (eLetIn na b t r)

| case_red_pred ind p p' c brs : red1 Σ Γ p p' -> red1 Σ Γ (eCase ind p c brs) (eCase ind p' c brs)
| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (eCase ind p c brs) (eCase ind p c' brs)
| case_red_brs ind p c brs brs' :
    OnOne2 (on_Trel_eq (red1 Σ Γ) snd fst) brs brs' ->
    red1 Σ Γ (eCase ind p c brs) (eCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (eProj p c) (eProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (eApp M1 M2) (eApp N1 M2)
| app_red_r M2 N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (eApp M1 M2) (eApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (eProd na M1 M2) (eProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (eProd na M1 M2) (eProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (eEvar ev l) (eEvar ev l')

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (eFix mfix0 idx) (eFix mfix1 idx)

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix0 mfix1 ->
    red1 Σ Γ (eFix mfix0 idx) (eFix mfix1 idx)

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (eCoFix mfix0 idx) (eCoFix mfix1 idx)

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (eCoFix mfix0 idx) (eCoFix mfix1 idx).

Lemma red1_ind_all :
  forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : name) (t b a : term),
        P Γ (eApp (eLambda na t b) a) (b {0 := a})) ->

      (forall (Γ : context) (e : err_type) (na : name) (A B a : term),
        P Γ (eApp (eErr e (eProd na A B)) a) (eErr e (subst10 a B))) ->

       (forall (Γ : context) (na : name) (b t b' : term), P Γ (eLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (eRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ind : inductive) (pars c : nat) (u : Instance.t) (args : list term)
          (p : term) (brs : list (nat * term)),
        P Γ (eCase (ind, pars) p (mkApps (eConstruct ind c u) args) brs) (iota_red pars c args brs)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (eFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) (ip : inductive * nat) (p : term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (nat * term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (eCase ip p (mkApps (eCoFix mfix idx) args) brs) (eCase ip p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (eProj p (mkApps (eCoFix mfix idx) args)) (eProj p (mkApps fn args))) ->

       (forall (Γ : context) (c : kername) (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (eConst c u) (subst_instance_constr u body)) ->

       (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (k : nat) (u : Instance.t)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P Γ (eProj (i, pars, narg) (mkApps (eConstruct i k u) args)) arg) ->

       (forall (Γ : context) (na : name) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (eLambda na M N) (eLambda na M' N)) ->

       (forall (Γ : context) (na : name) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (eLambda na N M) (eLambda na N M')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (eLetIn na b t b') (eLetIn na r t b')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (eLetIn na b t b') (eLetIn na b r b')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (eLetIn na b t b') (eLetIn na b t r)) ->

       (forall (Γ : context) (ind : inductive * nat) (p p' c : term) (brs : list (nat * term)),
        red1 Σ Γ p p' -> P Γ p p' -> P Γ (eCase ind p c brs) (eCase ind p' c brs)) ->

       (forall (Γ : context) (ind : inductive * nat) (p c c' : term) (brs : list (nat * term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (eCase ind p c brs) (eCase ind p c' brs)) ->

       (forall (Γ : context) (ind : inductive * nat) (p c : term) (brs brs' : list (nat * term)),
           OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) snd fst) brs brs' ->
           P Γ (eCase ind p c brs) (eCase ind p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (eProj p c) (eProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : term), red1 Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                         P Γ (eApp M1 M2) (eApp N1 M2)) ->

       (forall (Γ : context) (M2 N2 : term) (M1 : term), red1 Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                         P Γ (eApp M1 M2) (eApp M1 N2)) ->

       (forall (Γ : context) (na : name) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (eProd na M1 M2) (eProd na N1 M2)) ->

       (forall (Γ : context) (na : name) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (eProd na M1 M2) (eProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (eEvar ev l) (eEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (eFix mfix0 idx) (eFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (eFix mfix0 idx) (eFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (eCoFix mfix0 idx) (eCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (eCoFix mfix0 idx) (eCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Proof.
  intros. rename X27 into Xlast. revert Γ t t0 Xlast.
  fix aux 4. intros Γ t T.
  move aux at top.
  destruct 1; match goal with
              | |- P _ (eFix _ _) (eFix _ _) => idtac
              | |- P _ (eCoFix _ _) (eCoFix _ _) => idtac
              | |- P _ (mkApps (eFix _ _) _) _ => idtac
              | |- P _ (eCase _ _ (mkApps (eCoFix _ _) _) _) _ => idtac
              | |- P _ (eProj _ (mkApps (eCoFix _ _) _)) _ => idtac
              | H : _ |- _ => eapply H; eauto
              end.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.

  - revert brs brs' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. intuition auto. constructor. intuition auto.

  - revert l l' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.

  - eapply X23.
    revert mfix0 mfix1 o; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X24.
    revert o. generalize (fix_context mfix0). intros c Xnew.
    revert mfix0 mfix1 Xnew; fix auxl 3; intros l l' Hl;
    destruct Hl; constructor; try split; auto; intuition.

  - eapply X25.
    revert mfix0 mfix1 o.
    fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X26.
    revert o. generalize (fix_context mfix0). intros c new.
    revert mfix0 mfix1 new; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
Defined.


(** *** Reduction

  The reflexive-transitive closure of 1-step reduction. *)

Inductive red Σ Γ M : term -> Type :=
| refl_red : red Σ Γ M M
| trans_red : forall (P : term) N, red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.

Notation "Σ ;;; Γ |- t --> u" := (red Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.

Lemma red1_red (Σ : global_env) Γ t u : red1 Σ Γ t u -> red Σ Γ t u.
Proof. econstructor; eauto. constructor. Qed.
Hint Resolve red1_red refl_red : core pcuic.

Lemma red_step Σ Γ t u v : red1 Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  induction 2.
  - econstructor; auto.
  - econstructor 2; eauto.
Qed.

Lemma red_alt@{i j +} Σ Γ t u : red Σ Γ t u <~> clos_refl_trans@{i j} (red1 Σ Γ) t u.
Proof.
  split.
  - intros H. apply clos_rt_rtn1_iff.
    induction H; econstructor; eauto.
  - intros H. apply clos_rt_rtn1_iff in H.
    induction H; econstructor; eauto.
Qed.

Lemma red_trans Σ Γ t u v : red Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  intros. apply red_alt. apply red_alt in X. apply red_alt in X0. now econstructor 3.
Defined.

Instance red_Transitive Σ Γ : Transitive (red Σ Γ).
Proof. refine (red_trans _ _). Qed.

Instance red_Reflexive Σ Γ : Reflexive (red Σ Γ)
  := refl_red _ _.

Reserved Notation "Σ ;;; Γ |- t <= u" (at level 50, Γ, t, u at next level).
Reserved Notation "Σ ;;; Γ |- t = u" (at level 50, Γ, t, u at next level).
Reserved Notation "Σ ;;; Γ |- t ~~ u" (at level 50, Γ, t, u at next level).
(* Reserved Notation "Σ ;;; Γ |- t -->□ u" (at level 50, Γ, t, u at next level).
Reserved Notation "Σ ;;; Γ |- t -->Π ( na , A , B )" (at level 50, Γ, t, A, B at next level).
Reserved Notation "Σ ;;; Γ |- t -->{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level). *)

Inductive conv `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_refl t u : eq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t = u
| conv_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_red_r t u v : Σ ;;; Γ |- t = v -> red1 Σ Γ u v -> Σ ;;; Γ |- t = u
where "Σ ;;; Γ |- t = u" := (@conv _ Σ Γ t u) : type_scope.

Inductive consi `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| consi_refl t u : syn_cons_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t ~~ u
| consi_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v ~~ u -> Σ ;;; Γ |- t ~~ u
| consi_red_r t u v : Σ ;;; Γ |- t ~~ v -> red1 Σ Γ u v -> Σ ;;; Γ |- t ~~ u
where "Σ ;;; Γ |- t ~~ u" := (@consi _ Σ Γ t u) : type_scope.

(* Inductive red_sort `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> Universe.t -> Type :=
| red_sort_sort u u' : eq_universe Σ u u' -> Σ ;;; Γ |- eSort u -->□ u'
| red_sort_ukn l l' : Σ ;;; Γ |- eErr l ukn (eSort (Universe.super l')) -->□ Universe.make l'
| red_sort_red t t' u : red1 Σ Γ t t' -> Σ ;;; Γ |- t' -->□ u -> Σ ;;; Γ |- t -->□ u
where "Σ ;;; Γ |- t -->□ u" := (@red_sort _ Σ Γ t u) : type_scope.

Inductive red_prod `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> name -> term -> term -> Type :=
| red_prod_prod na A B : Σ ;;; Γ |- eProd na A B -->Π (na,A,B)
| red_prod_ukn l u : Σ ;;; Γ |- eErr l ukn (eSort u) -->Π (nAnon,eErr l ukn (eSort u), eErr l ukn (eSort u))
| red_prod_red t t' na A B : red1 Σ Γ t t' -> Σ ;;; Γ |- t' -->Π (na,A,B) -> Σ ;;; Γ |- t -->Π (na,A,B)
where "Σ ;;; Γ |- t -->Π ( na , A , B )" := (@red_prod _ Σ Γ t na A B ) : type_scope.

Inductive red_indu `{checker_flags} (Σ : global_env_ext) (Γ : context) (ind : inductive)
    : term -> Instance.t -> list term -> Type :=
| red_ind_ind mdecl idecl u args :
    declared_inductive Σ.1 mdecl ind idecl -> #|args| = mdecl.(ind_nparams) ->
    Σ ;;; Γ |- mkApps (eInd ind u) args -->{ind} (u,args)
| red_ind_ukn l u :
    declared_inductive Σ.1 mdecl ind idecl ->
    Σ ;;; Γ |- eErr l ukn (eSort u) -->{ind} ??? 
| red_indu_red t t' na A B : red1 Σ Γ t t' -> Σ ;;; Γ |- t' -->{ind} (u,args) -> Σ ;;; Γ |- t -->{ind} (u,args)
where "Σ ;;; Γ |- t -->{ind} ( u , args )" := (@red_indu _ Σ Γ ind t u args) : type_scope. *)

Instance consi_Reflexive `{checker_flags} Σ Γ : Reflexive (consi Σ Γ).
Proof.
  intro.
  apply consi_refl.
  apply syn_cons_term_refl.
Qed.

Lemma consi_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t ~~ u <~> { v & { v' & (red Σ Γ t v × red Σ Γ u v' × syn_cons_term (global_ext_constraints Σ) v v')}}.
Proof.
  split.
  - induction 1.
    + exists t, u. intuition auto.
    + destruct IHX as (v' & v'' & redv & redv' & sconsv').
      exists v', v''. intuition auto. now eapply red_step.
    + destruct IHX as (v' & v'' & redv & redv' & sconsv).
      exists v', v''. intuition auto. now eapply red_step.
  - intros (v & v' & redv & redv' & Hscons). apply red_alt in redv. apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** econstructor 3; eauto.
    * econstructor 2; eauto.
Qed.

Lemma red_consi `{cf: checker_flags} (Σ : global_env_ext) Γ t u :
  Σ ;;; Γ |- t --> u -> Σ ;;; Γ |- t ~~ u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X.
  - by apply consi_Reflexive.
  - econstructor 2 ; eassumption.
Qed.

Lemma consi_Ukn_r `{checker_flags} Σ Γ t T : Σ ;;; Γ |- t ~~ eErr ukn T.
Proof.
  constructor.
  constructor.
Qed.

Lemma consi_Ukn_l `{checker_flags} Σ Γ t T : Σ ;;; Γ |- eErr ukn T ~~ t.
Proof.
  constructor.
  constructor.
Qed.

Lemma consi_red_sort `{checker_flags} Σ Γ T u :
  Σ ;;; Γ |- T ~~ eSort u ->  {u' & Σ ;;; Γ |- T --> (eSort u') × eq_universe Σ u u'} +
                              {l : Level.t & u = Universe.super l × Σ ;;; Γ |- T --> eErr ukn (eSort (Universe.make l))}.
Proof.
  intros X. dependent induction X.
  - inversion_clear s.
    + left. eexists ; split. constructor. apply eq_universe_sym. assumption.
    + right. admit. (* -->□ is too restrictive in the error case compared to ~~ *)
  - unshelve econstructor ; eauto.
  - inversion r.
    exfalso.
    clear -H0.
    have ne : eFix mfix idx <> eSort u by intro ; discriminate.
    remember (eFix mfix idx) as h ; clear Heqh.
    induction args in ne, H0, h |- *.
    1: auto.
    eapply IHargs.
    1:eassumption.
    intro. discriminate. 
Admitted.

Lemma red_prod_refl `{checker_flags} Σ Γ na A B : Σ ;;; Γ |- eProd na A B -->Π (na,A,B).
Proof.
  constructor.
Qed.

Lemma red_prod_consi `{checker_flags} Σ Γ T na A B : Σ ;;; Γ |- T -->Π (na,A,B) -> Σ ;;; Γ |- T ~~ eProd na A B.
Proof.
  intros X.
  induction X.
  - constructor. constructor.
    all: apply syn_cons_term_refl.
  - apply consi_Ukn_l.
  - econstructor 2 ; eauto.
Qed.

Axiom red_indu_refl : forall {cf : checker_flags} Σ Γ ind ui args, Σ ;;; Γ |- mkApps (eInd ind ui) args -->{ind} (ui,args).
Axiom red_indu_consi : forall {cf : checker_flags} Σ Γ T ind ui args,
  Σ ;;; Γ |- T -->{ind} (ui,args) -> Σ ;;; Γ |- T ~~ mkApps (eInd ind ui) args. *)

(*
 (** ** Cumulativity *)

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u
| cumul_eta_l t u v : eta_expands t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_eta_r t u v : Σ ;;; Γ |- t <= v -> eta_expands u v -> Σ ;;; Γ |- t <= u

where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.

(** *** Conversion

   Defined as cumulativity in both directions.
 *)


Inductive conv `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_refl t u : eq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t = u
| conv_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_red_r t u v : Σ ;;; Γ |- t = v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t = u
| conv_eta_l t u v : eta_expands t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_eta_r t u v : Σ ;;; Γ |- t = v -> eta_expands u v -> Σ ;;; Γ |- t = u
where " Σ ;;; Γ |- t = u " := (@conv _ Σ Γ t u) : type_scope.

Hint Resolve cumul_refl conv_refl : EGCIC. *)