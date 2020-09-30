(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping.

From MetaCoq Require Export LibHypsNaming.
Require Import ssreflect.
Set Asymmetric Patterns.
Require Import Equations.Type.Relation.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import MonadNotation.

Module BDLookup := Lookup PCUICTerm PCUICEnvironment.
Include BDLookup.

Module BDEnvTyping := EnvTyping PCUICTerm PCUICEnvironment.
Include BDEnvTyping.

Section WfArity.
  Context (checking : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).
  Context (sorting : forall (Σ : global_env_ext) (Γ : context), term -> Universe.t -> Type).

  Definition isWfArity_rel Σ (Γ : context) T :=
    { ctx & { s & (destArity [] T = Some (ctx, s)) ×
      All_local_env_rel (lift_sorting checking sorting Σ) Γ ctx } }.

  Context (cproperty : forall (Σ : global_env_ext) (Γ Γ' : context),
              All_local_env_rel (lift_sorting checking sorting Σ) Γ Γ' ->
              forall (t T : term), checking Σ (Γ,,,Γ') t T -> Type).
  Context (sproperty : forall (Σ : global_env_ext) (Γ Γ' : context),
              All_local_env_rel (lift_sorting checking sorting Σ) Γ Γ' ->
              forall (t : term) (u : Universe.t), sorting Σ (Γ,,,Γ') t u -> Type).

  Definition isWfArity_prop_rel Σ (Γ : context) T :=
    { wfa : isWfArity_rel Σ Γ T &
      All_local_env_over_rel checking sorting cproperty sproperty Σ Γ wfa.π1 wfa.π2.π2.2 }.
End WfArity.

Notation "Σ ;;; Γ |- t --> t'" := (red Σ Γ t t') (at level 50, Γ, t, t' at next level) : type_scope.
Reserved Notation " Σ ;;; Γ |- t ▹ T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t ▸□ u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t ▸Π ( na , A , B ) " (at level 50, Γ, t, na, A, B at next level).
Reserved Notation " Σ ;;; Γ |- t ▸{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
Reserved Notation " Σ ;;; Γ |- t ◃ T " (at level 50, Γ, t, T at next level).


Inductive infering `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| infer_Rel n decl :
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n ▹ lift0 (S n) decl.(decl_type)

| infer_Sort l :
    LevelSet.In l (global_ext_levels Σ) ->
    Σ ;;; Γ |- tSort (Universe.make l) ▹ tSort (Universe.super l)

| infer_Prod na A B s1 s2 :
    Σ ;;; Γ |- A ▸□ s1 ->
    Σ ;;; Γ ,, vass na A |- B ▸□ s2 ->
    Σ ;;; Γ |- tProd na A B ▹ tSort (Universe.sort_of_product s1 s2)

| infer_Lambda na A t s B :
    Σ ;;; Γ |- A ▸□ s ->
    Σ ;;; Γ ,, vass na A |- t ▹ B ->
    Σ ;;; Γ |- tLambda na A t ▹ tProd na A B

| infer_LetIn na b B t s A :
    Σ ;;; Γ |- B ▸□ s ->
    Σ ;;; Γ |- b ◃ B ->
    Σ ;;; Γ ,, vdef na b B |- t ▹ A ->
    Σ ;;; Γ |- tLetIn na b B t ▹ tLetIn na b B A

| infer_App t na A B u :
    Σ ;;; Γ |- t ▸Π (na,A,B) ->
    Σ ;;; Γ |- u ◃ A ->
    Σ ;;; Γ |- tApp t u ▹ B{0 := u}

| infer_Const cst u :
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- tConst cst u ▹ subst_instance_constr u decl.(cst_type)

| infer_Ind ind u :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tInd ind u ▹ subst_instance_constr u idecl.(ind_type)

| infer_Construct ind i u :
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tConstruct ind i u ▹ type_of_constructor mdecl cdecl (ind, i) u

| infer_Case (indnpar : inductive × nat) (u : Instance.t) (p c : term) (brs : list (nat × term)) (args : list term) :
  let ind := indnpar.1 in
  let npar := indnpar.2 in
   Σ ;;; Γ |- c ▸{ind} (u,args) ->
  forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
  mdecl.(ind_npars) = npar ->
  isCoFinite mdecl.(ind_finite) = false ->
  let params := List.firstn npar args in
  forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
  Σ ;;; Γ |- p ◃ pty ->
  leb_sort_family (universe_family ps) idecl.(ind_kelim) ->
  forall (btys : list (nat × term)),
  map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
  All2 (fun br bty =>
    (br.1 = bty.1) ×
    (Σ ;;; Γ |- bty.2 ▸□ ps) ×
    (Σ ;;; Γ |- br.2 ◃ bty.2))
    brs btys ->
  Σ ;;; Γ |- tCase indnpar p c brs ▹ mkApps p (skipn npar args ++ [c])

| infer_Proj p c u :
    forall mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) (args : list term),
    Σ ;;; Γ |- c ▸{fst (fst p)} (u,args) ->
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- tProj p c ▹ subst0 (c :: List.rev args) (subst_instance_constr u ty)

| infer_Fix (mfix : mfixpoint term) n decl :
    fix_guard mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) ▸□ s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype))
      × (isLambda d.(dbody) = true)) mfix ->
    wf_fixpoint Σ.1 mfix -> 
    Σ ;;; Γ |- tFix mfix n ▹ decl.(dtype)

| infer_CoFix mfix n decl :
    cofix_guard mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) ▸□ s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ.1 mfix ->
    Σ ;;; Γ |- tCoFix mfix n ▹ decl.(dtype)

with infering_sort `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> Universe.t -> Type :=
| infer_sort_Sort t T u :
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T --> tSort u ->
  Σ ;;; Γ |- t ▸□ u

with infering_prod `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> name -> term -> term -> Type :=
| infer_prod_Prod t T na A B:
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T --> tProd na A B ->
  Σ ;;; Γ |- t ▸Π (na,A,B)

with infering_indu `{checker_flags} (Σ : global_env_ext) (Γ : context) : inductive -> term -> Instance.t -> list term -> Type :=
| infer_ind_Red ind t T u args:
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T --> mkApps (tInd ind u) args ->
  Σ ;;; Γ |- t ▸{ind} (u,args)

with checking `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| check_Cons t T T' :
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T <= T' ->
  Σ ;;; Γ |- t ◃ T'

where " Σ ;;; Γ |- t ▹ T " := (@infering _ Σ Γ t T) : type_scope
and " Σ ;;; Γ |- t ▸□ u " := (@infering_sort _ Σ Γ t u) : type_scope
and " Σ ;;; Γ |- t ▸Π ( na , A , B ) " := (@infering_prod _ Σ Γ t na A B) : type_scope
and " Σ ;;; Γ |- t ▸{ ind } ( u , args ) " := (@infering_indu _ Σ Γ ind t u args) : type_scope
and " Σ ;;; Γ |- t ◃ T " := (@checking _ Σ Γ t T) : type_scope.

Notation wf_local Σ Γ := (All_local_env (lift_sorting checking infering_sort Σ) Γ).
Notation wf_local_rel Σ Γ Γ' := (All_local_env_rel (lift_sorting checking infering_sort Σ) Γ Γ').


(* Lemma meta_conv {cf : checker_flags} Σ Γ t A B :
    Σ ;;; Γ |- t : A ->
    A = B ->
    Σ ;;; Γ |- t : B.
Proof.
  intros h []; assumption.
Qed. *)


(** ** Typechecking of global environments *)

Module BDTypingDef <: Typing PCUICTerm PCUICEnvironment BDEnvTyping.

  Definition ind_guard := ind_guard.
  Definition checking `{checker_flags} := checking.
  Definition sorting `{checker_flags} := infering_sort.
  Definition conv := @conv.
  Definition cumul := @cumul.
  Definition smash_context := smash_context.
  Definition lift_context := lift_context.
  Definition subst_telescope := subst_telescope.
  Definition subst_instance_context := subst_instance_context.
  Definition subst_instance_constr := subst_instance_constr.
  Definition subst := subst.
  Definition lift := lift.
  Definition inds := inds. 
  Definition noccur_between := noccur_between. 
  Definition closedn := closedn.

End BDTypingDef.

Module BDDeclarationTyping :=
  DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    BDEnvTyping
    BDTypingDef
    BDLookup.
Include BDDeclarationTyping.

Fixpoint infering_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T) {struct d} : size
with infering_sort_size `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▸□ u) {struct d} : size
with infering_prod_size `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▸Π (na, A,B)) {struct d} : size
with infering_indu_size `{checker_flags} {Σ Γ ind t ui args} (d : Σ ;;; Γ |- t ▸{ind} (ui,args)) {struct d} : size
with checking_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ◃ T) {struct d} : size.
Proof.
  all: destruct d ;
    repeat match goal with
           | H : infering _ _ _ _ |- _ => apply infering_size in H
           | H : infering_sort _ _ _ _ |- _ => apply infering_sort_size in H
           | H : infering_prod _ _ _ _ _ _ |- _ => apply infering_prod_size in H
           | H : infering_indu _ _ _ _ _ _ |- _ => apply infering_indu_size in H 
           | H : checking _ _ _ _ |- _ => apply checking_size in H
           end ;
    match goal with
    | H : All2 _ _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (H1 + H2 + H3))
    | H1 : size, H2 : size |- _ => exact (S (H1 + H2))
    | H1 : size |- _  => exact (S H1)
    | _ => exact 1
    end. 
    - exact (S (i + c0 + (all2_size _ 
                                        (fun x y p => (infering_sort_size _ _ _ _ _ (fst (snd p)))
                                                      + (checking_size _ _ _ _ _ (snd (snd p)))) a))).
    - exact (S (all_size _ (fun d p => infering_sort_size _ _ _ _ _ p.π2) a) +
               (all_size _ (fun x p => checking_size _ _ _ _ _ p.1) a0)).
    - exact (S (all_size _ (fun d p => infering_sort_size _ _ _ _ _ p.π2) a) +
               (all_size _ (fun x => checking_size _ _ _ _ _) a0)).
  Defined.

Definition wfarity_size `{checker_flags} {Σ Γ T} (d : isWfArity_rel checking infering_sort Σ Γ T) : size.
Proof.
  destruct d as (ctx & u & e & wf).
  exact (wf_local_rel_size Σ (@checking_size _) (@infering_sort_size _) _ _ wf).
Defined.

Fixpoint infering_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T)
  : infering_size d > 0
with infering_sort_size_pos `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▸□ u) {struct d}
  : infering_sort_size d > 0
with infering_prod_size_pos `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▸Π (na,A,B)) {struct d}
  : infering_prod_size d > 0
with infering_indu_size_pos `{checker_flags} {Σ Γ t ind ui args} (d : Σ ;;; Γ |- t ▸{ind} (ui,args)) {struct d}
  : infering_indu_size d > 0
with checking_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ◃ T) {struct d}
  : checking_size d > 0.
Proof.
  all: destruct d ; simpl ; lia.
Qed.

Fixpoint globenv_size (Σ : global_env) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globenv_size Σ)
  end.

(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_env_ext, including size of the global declarations in it
    - size of the derivation. *)

Arguments lexprod [A B].

Definition wf `{checker_flags} := Forall_decls_typing checking infering_sort.
Definition wf_ext `{checker_flags} := on_global_env_ext checking infering_sort.

Lemma wf_ext_wf {cf:checker_flags} Σ : wf_ext Σ -> wf Σ.
Proof. intro H; apply H. Qed.

Hint Resolve wf_ext_wf : core.

Lemma wf_ext_consistent {cf:checker_flags} Σ :
  wf_ext Σ -> consistent Σ.
Proof.
  intros [? [? [? [? ?]]]]; assumption.
Qed.

Hint Resolve wf_ext_consistent : core.


Section TypingInduction.

#[local] Notation wfl_size := (wf_local_size _ (@checking_size _) (@infering_sort_size _) _).

  Context (Pcheck : global_env_ext -> context -> term -> term -> Type).
  Context (Pinfer : global_env_ext -> context -> term -> term -> Type).
  Context (Psort : global_env_ext -> context -> term -> Universe.t -> Type).
  Context (Pprod : global_env_ext -> context -> term -> name -> term -> term -> Type).
  Context (Pind : global_env_ext -> context -> inductive -> term -> Instance.t -> list term -> Type).
  Context (PΓ : forall `{checker_flags} Σ Γ, wf_local Σ Γ -> Type).
  Arguments PΓ {_}.

  Definition env_prop `{checker_flags} :=
    forall Σ (wfΣ : wf Σ.1),
    (Forall_decls_typing Pcheck Psort Σ.1) ×
    (forall Γ (wfΓ : wf_local Σ Γ), PΓ Σ Γ wfΓ) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t ◃ T -> Pcheck Σ Γ t T) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t ▹ T -> Pinfer Σ Γ t T) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t u, Σ ;;; Γ |- t ▸□ u -> Psort Σ Γ t u) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t na A B, Σ ;;; Γ |- t ▸Π (na,A,B) -> Pprod Σ Γ t na A B) ×
    (forall Γ (wfΓ : wf_local Σ Γ) ind t u args, Σ ;;; Γ |- t ▸{ind} (u,args) -> Pind Σ Γ ind t u args).

  Lemma wf_local_app `{checker_flags} Σ (Γ Γ' : context) : wf_local Σ (Γ,,,Γ') -> wf_local Σ Γ.
  Proof.
    induction Γ'. auto.
    simpl. intros H'; inv H'; eauto.
  Defined.
  Hint Resolve wf_local_app : wf.

  Derive Signature for All_local_env.

  Set Equations With UIP.
  Derive NoConfusion for context_decl.
  Derive NoConfusion for list.
  Derive NoConfusion for All_local_env.

  Lemma size_wf_local_app `{checker_flags} {Σ} (Γ Γ' : context) (Hwf : wf_local Σ (Γ ,,, Γ')) :
    wfl_size (wf_local_app _ _ _ Hwf) <=
    wfl_size Hwf.
  Proof.
    induction Γ' in Γ, Hwf |- *; try lia. simpl. lia.
    depelim Hwf.
    - inversion H0. subst. noconf H4. simpl. unfold eq_rect_r. simpl. specialize (IHΓ' _ Hwf). lia.
    - inversion H0. subst. noconf H4. specialize (IHΓ' _ Hwf). simpl. unfold eq_rect_r. simpl. lia.
  Qed.

  Lemma wf_local_inv `{checker_flags} {Σ Γ'} (w : wf_local Σ Γ') :
    forall d Γ,
      Γ' = d :: Γ ->
      ∑ w' : wf_local Σ Γ,
        match d.(decl_body) with
        | Some b =>
          ∑ u (ty : Σ ;;; Γ |- b ◃ d.(decl_type)),
            { ty' : Σ ;;; Γ |- d.(decl_type) ▸□ u |
              wfl_size w' <
              wfl_size w /\
              checking_size ty <= wfl_size w /\
              infering_sort_size ty' <= wfl_size w }

        | None =>
          ∑ u,
            { ty : Σ ;;; Γ |- d.(decl_type) ▸□ u |
              wfl_size w' < wfl_size w /\
              infering_sort_size ty <= wfl_size w }
        end.
  Proof.
    intros d Γ.
    destruct w.
    - simpl. congruence.
    - intros [=]. subst d Γ0.
      exists w. simpl. destruct t0 ; simpl in *. exists x.
      exists i.
      pose (infering_sort_size_pos i).
      simpl. split.
      + lia.
      + auto with arith.
    - intros [=]. subst d Γ0.
      exists w. simpl in *.
      dependent inversion t0 as [[u h] h'].
      exists u, h', h. simpl in *.
      pose (infering_sort_size_pos h).
      pose (checking_size_pos h').
      intuition lia.
  Qed.

  Lemma isWfArity_sort `{checker_flags} {Σ Γ} u : isWfArity_rel checking infering_sort Σ Γ (tSort u).
  Proof.
    red. exists []. exists u.
    split.
    1: by rewrite /destArity /=.
    by constructor.
  Defined.

  Derive Signature for Alli.

  (** *** Inductive principle, giving extra-strong premisses,
          including environment and context well-formedness
  *)

  Inductive typing_sum `{checker_flags} Σ (wfΣ : wf Σ.1) : Type :=
    | env_cons : typing_sum Σ wfΣ
    | context_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ), typing_sum Σ wfΣ
    | check_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) T t, Σ ;;; Γ |- t ◃ T -> typing_sum Σ wfΣ
    | inf_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) T t, Σ ;;; Γ |- t ▹ T -> typing_sum Σ wfΣ
    | sort_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) t u, Σ ;;; Γ |- t ▸□ u -> typing_sum Σ wfΣ
    | prod_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) t na A B, Σ ;;; Γ |- t ▸Π (na,A,B) -> typing_sum Σ wfΣ
    | ind_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) ind t u args,
        Σ ;;; Γ |- t ▸{ind} (u,args) -> typing_sum Σ wfΣ.

  Definition typing_sum_size `{checker_flags} {Σ} {wfΣ : wf Σ.1} (d : typing_sum Σ wfΣ) :=
  match d with
    | env_cons => 0
    | context_cons Γ wfΓ => wfl_size wfΓ
    | check_cons Γ wfΓ _ _ d => (wfl_size wfΓ) + (checking_size d)
    | inf_cons Γ wfΓ _ _ d => (wfl_size wfΓ) + (infering_size d)
    | sort_cons Γ wfΓ _ _ d => (wfl_size wfΓ) + (infering_sort_size d)
    | prod_cons Γ wfΓ _ _ _ _ d => (wfl_size wfΓ) + (infering_prod_size d)
    | ind_cons Γ wfΓ _ _ _ _ d => (wfl_size wfΓ) + (infering_indu_size d)
  end.

  Definition context_size `{checker_flags} {Σ} {wfΣ : wf Σ.1} (d : typing_sum Σ wfΣ) := 
  match d with
    | env_cons => 0
    | context_cons Γ wfΓ => wfl_size wfΓ
    | check_cons Γ wfΓ _ _ d => wfl_size wfΓ
    | inf_cons Γ wfΓ _ _ d => wfl_size wfΓ
    | sort_cons Γ wfΓ _ _ d => wfl_size wfΓ
    | prod_cons Γ wfΓ _ _ _ _ d => wfl_size wfΓ
    | ind_cons Γ wfΓ _ _ _ _ d => wfl_size wfΓ
  end.

  Definition Ptyping_sum `{checker_flags} {Σ wfΣ} (d : typing_sum Σ wfΣ) :=
  match d with
    | env_cons => Forall_decls_typing Pcheck Psort Σ.1
    | context_cons Γ wfΓ => PΓ Σ Γ wfΓ
    | check_cons Γ _ T t _ => Pcheck Σ Γ t T
    | inf_cons Γ _ T t _ => Pinfer Σ Γ t T
    | sort_cons Γ _ T u _ => Psort Σ Γ T u
    | prod_cons Γ _ T na A B _ => Pprod Σ Γ T na A B
    | ind_cons Γ _ ind T u args _ => Pind Σ Γ ind T u args
  end.

  Ltac applyIH := match goal with
    | IH : forall _ _ d', _ -> Ptyping_sum d' |- Forall_decls_typing Pcheck Psort _ =>
          unshelve eapply (IH _ _ (env_cons _ _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- PΓ _ ?Γ ?wfΓ =>
          unshelve eapply (IH _ _ (context_cons _ _ Γ wfΓ))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pcheck _ ?Γ ?t ?T =>
          unshelve eapply (IH _ _ (check_cons _ _ Γ _ T t _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pinfer _ ?Γ ?t ?T =>
          unshelve eapply (IH _ _ (inf_cons _ _ Γ _ T t _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d'|- Psort _ ?Γ ?t ?u =>
          unshelve eapply (IH _ _ (sort_cons _ _ Γ _ t u _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pprod _ ?Γ ?t ?na ?A ?B =>
          unshelve eapply (IH _ _ (prod_cons _ _ Γ _ t na A B _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pind _ ?Γ ?ind ?t ?u ?args =>
          unshelve eapply (IH _ _ (ind_cons _ _ Γ _ ind t u args _))
    end ;
    match goal with
    | |- isWfArity _ _ _ (tSort _) => apply isWfArity_sort ; try assumption ; try (by constructor)
    | |- dlexprod _ _ _ _ => constructor ; simpl ; lia
    | |- dlexprod _ _ _ _ =>
            constructor 2 ; simpl ;
            (match goal with | |- dlexprod _ _ (?x1;_) (?y1;_) => replace x1 with y1 by lia end ; constructor 2) ||
            constructor ; try lia
    | _ => assumption
    | _ => simpl ; lia
    | _ => idtac
    end.

  Lemma typing_ind_env `{cf : checker_flags} :
    let Pdecl_check := fun Σ Γ wfΓ t T tyT => Pcheck Σ Γ t T in
    let Pdecl_sort := fun Σ Γ wfΓ t u tyT => Psort Σ Γ t u in

    (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ), 
          All_local_env_over checking infering_sort Pdecl_check Pdecl_sort Σ Γ wfΓ -> PΓ Σ Γ wfΓ) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ wfΓ ->
        Pinfer Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (l : Level.t),
        PΓ Σ Γ wfΓ ->
        LevelSet.In l (global_ext_levels Σ) ->
        Pinfer Σ Γ (tSort (Universe.make l)) (tSort (Universe.super l))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term) (s1 s2 : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸□ s1 ->
        Psort Σ Γ t s1 ->
        Σ ;;; Γ,, vass n t |- b ▸□ s2 ->
        Psort Σ (Γ,, vass n t) b s2 -> Pinfer Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term)
            (s : Universe.t) (bty : term),
            PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸□ s ->
        Psort Σ Γ t s ->
        Σ ;;; Γ,, vass n t |- b ▹ bty -> Pinfer Σ (Γ,, vass n t) b bty ->
        Pinfer Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (b B t : term)
            (s : Universe.t) (A : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- B ▸□ s ->
        Psort Σ Γ B s ->
        Σ ;;; Γ |- b ◃ B ->
        Pcheck Σ Γ b B ->
        Σ ;;; Γ,, vdef n b B |- t ▹ A ->
        Pinfer Σ (Γ,, vdef n b B) t A -> Pinfer Σ Γ (tLetIn n b B t) (tLetIn n b B A)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) na A B u,
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸Π (na, A, B) -> Pprod Σ Γ t na A B ->
        Σ ;;; Γ |- u ◃ A -> Pcheck Σ Γ u A ->
        Pinfer Σ Γ (tApp t u) (subst10 u B)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (cst : kername) u (decl : constant_body),
        Forall_decls_typing Pcheck Psort Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        Pinfer Σ Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl,
        Forall_decls_typing Pcheck Psort Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_inductive Σ.1 mdecl ind idecl ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        Pinfer Σ Γ (tInd ind u) (subst_instance_constr u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl,
        Forall_decls_typing Pcheck Psort Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constructor Σ.1 mdecl idecl (ind, i) cdecl ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        Pinfer Σ Γ (tConstruct ind i u)
          (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u (npar : nat)
            (p c : term) (brs : list (nat * term))
            (args : list term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
            (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing Pcheck Psort Σ.1 -> PΓ Σ Γ wfΓ ->
        isCoFinite mdecl.(ind_finite) = false ->
        Σ ;;; Γ |- c ▸{ind} (u,args) ->
        Pind Σ Γ ind c u args ->
        ind_npars mdecl = npar ->
        let params := firstn npar args in
        forall ps pty,
        build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
        Σ ;;; Γ |- p ◃ pty ->
        Pcheck Σ Γ p pty ->
        leb_sort_family (universe_family ps) idecl.(ind_kelim) ->
        forall btys,
        map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
        All2 (fun br bty => (br.1 = bty.1) ×
                          (Σ ;;; Γ |- bty.2 ▸□ ps) × Psort Σ Γ bty.2 ps ×
                          (Σ ;;; Γ |- br.2 ◃ bty.2) × Pcheck Σ Γ br.2 bty.2)
              brs btys ->
        Pinfer Σ Γ (tCase (ind,npar) p c brs) (mkApps p (skipn npar args ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl pdecl args,
        Forall_decls_typing Pcheck Psort Σ.1 -> PΓ Σ Γ wfΓ ->
        declared_projection Σ.1 mdecl idecl p pdecl ->
        Σ ;;; Γ |- c ▸{fst (fst p)} (u,args) ->
        Pind Σ Γ (fst (fst p)) c u args ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in
        Pinfer Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : mfixpoint term) (n : nat) decl,
        fix_guard mfix ->
        nth_error mfix n = Some decl ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▸□ s) × Psort Σ Γ d.(dtype) s}) mfix ->
        All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                  (isLambda d.(dbody) = true) ×
                  Pcheck Σ (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
        wf_fixpoint Σ.1 mfix ->
        Pinfer Σ Γ (tFix mfix n) decl.(dtype)) ->
    
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : mfixpoint term) (n : nat) decl,
        cofix_guard mfix ->
        nth_error mfix n = Some decl ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▸□ s) × Psort Σ Γ d.(dtype) s}) mfix ->
        All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                  Pcheck Σ (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
        wf_cofixpoint Σ.1 mfix ->
        Pinfer Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term) (u : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T --> tSort u ->
        Psort Σ Γ t u) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term) (na : name) (A B : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T --> tProd na A B ->
        Pprod Σ Γ t na A B) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (t T : term) (ui : Instance.t)
          (args : list term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T --> mkApps (tInd ind ui) args ->
        Pind Σ Γ ind t ui args) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T T' : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T <= T' ->
        Pcheck Σ Γ t T') ->
      
    env_prop.
  Proof.
    intros Pdecl_check Pdecl_sort HΓ HRel HSort HProd HLambda HLetIn HApp HConst HInd HConstruct HCase
      HProj HFix HCoFix HiSort HiProd HiInd HCheck ; unfold env_prop.
    pose (@Fix_F (∑ (Σ : _) (wfΣ : _), typing_sum Σ wfΣ)
            (dlexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
              (fun Σ => precompose (dlexprod lt (fun _ => lt)) (fun d => (typing_sum_size d.π2 ; context_size d.π2))))
            (fun d => Ptyping_sum d.π2.π2)).
    forward p.
    2:{ intros Σ wfΣ.
        enough (HP : forall x : typing_sum Σ wfΣ, Ptyping_sum x).
        - repeat split ; intros.
          + exact (HP (env_cons Σ wfΣ)).
          + exact (HP (context_cons Σ wfΣ Γ wfΓ)).
          + exact (HP (check_cons Σ wfΣ Γ wfΓ T t X)).
          + exact (HP (inf_cons Σ wfΣ Γ wfΓ T t X)).
          + exact (HP (sort_cons Σ wfΣ Γ wfΓ t u X)).
          + exact (HP (prod_cons Σ wfΣ Γ wfΓ t na A B X)).
          + exact (HP (ind_cons Σ wfΣ Γ wfΓ ind t u args X)).
        - intros x ; apply (p (Σ ; (wfΣ ; x))).
          apply wf_dlexprod ; intros ; apply wf_precompose ; [ | apply wf_dlexprod ; intros] ; apply lt_wf.
    }
    clear p.     
    intros (Σ & wfΣ & d) IH'. simpl.
    match goal with | IH' : forall y : _ , ?P _ _ -> _ |- _ =>
      have IH : forall (Σ' : global_env_ext) (wfΣ' : wf Σ'.1) (d' :typing_sum Σ' wfΣ'),
        P (Σ'; wfΣ'; d') (Σ; wfΣ; d) -> Ptyping_sum d' end.
    1: intros Σ' wfΣ' d' H; exact (IH' (Σ' ; wfΣ' ; d') H).
    clear IH'.
    destruct d ; simpl.
    4: destruct i.
    - destruct Σ as [Σ φ]. destruct Σ.
      1: constructor.
      destruct p.
      cbn in  *.
      have IH' : forall Σ' wfΣ' (d' : typing_sum Σ' wfΣ'), globenv_size (Σ'.1) < S (globenv_size Σ) ->
                    Ptyping_sum d'
        by intros ; apply IH ; constructor ; simpl ; assumption.
      clear IH.
      dependent destruction wfΣ.
      constructor.
      + change (Forall_decls_typing Pcheck Psort (Σ,φ).1).
        applyIH.
      + assumption.
      + assumption.
      + destruct g as [[? [] ?]| ]; cbn.
        * applyIH.
          constructor.
        * dependent elimination o0.
          eexists. applyIH.
          1: by constructor.
          eassumption.
        * dependent elimination o0.
          constructor.
          3-5: assumption.
          2:{
            clear - wfΣ IH' onParams0.
            induction onParams0.
            1: by constructor.
            -- constructor.
               1: by assumption.
               destruct t0.
               eexists.
               applyIH.
               by eassumption. 
            -- constructor.
               1: by assumption.
               destruct t0.
               constructor.
               2: by cbn ; applyIH.
               destruct l.
               eexists.
               applyIH.
               by eassumption. 
          }
           have wftypes : wf_local (Σ, udecl) (arities_context (ind_bodies m)).
          { admit. }
          remember (ind_bodies m) as Γ in onInductives0 |- *.
          clear - wfΣ IH' onParams0 wftypes onInductives0.
          induction onInductives0 as [| ? ? ? [] ?].
          1: by constructor.
          constructor.
          2: eassumption.
          econstructor ; try eassumption.
          ++ destruct onArity0.
            eexists. applyIH.
            1: by constructor.
            eassumption.
          ++ clear - wfΣ IH' onConstructors0 onParams0 wftypes.
            induction onConstructors0.
            1: by constructor.
            constructor.
            2: assumption.
            destruct r.
            constructor.
            all: try assumption.
            ** cbn.
                destruct on_ctype0.
                eexists.
                applyIH.
                eassumption.
            ** eapply type_local_ctx_impl.
                1: eassumption.
                all: intros ; applyIH ; eapply type_local_ctx_wf_local ; try eassumption.
                admit. (*well-formedness of context concatenation, when both contexts are well-formed *)
                  


            ** admit.
          ++ clear - wfΣ IH' ind_sorts0.
              red in ind_sorts0 |- *.
              destruct (universe_family ind_sort0).
              all: intuition.
              all: destruct indices_matter ; auto.
              ** eapply type_local_ctx_impl.
                1: eassumption.
                all: intros ; applyIH ; eapply type_local_ctx_wf_local ; eassumption.
              ** eapply type_local_ctx_impl.
                1: eassumption.
                all: intros ; applyIH ; eapply type_local_ctx_wf_local ; eassumption.


    - apply HΓ.
      1: assumption.
      dependent induction wfΓ.
      + constructor.
      + destruct t0 as (u & d).
        constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          dependent destruction H ; [constructor | constructor 2] ; auto.
          etransitivity ; eauto.
          constructor.
          simpl ; cbn in d ; pose proof (infering_sort_size_pos d) ; lia.
        * constructor.
          red ; applyIH.
          cbn in d ; pose proof (infering_sort_size_pos d) ; lia.
      + destruct t0 as [[u h] h'].
        constructor.
        2: constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          dependent destruction H ; [constructor | constructor 2] ; auto.
          etransitivity ; eauto.
          constructor.
          simpl. cbn in h ; pose proof (infering_sort_size_pos h) ; lia.
        * red ; applyIH.
          cbn in h' ; pose proof (checking_size_pos h') ; lia.
        * red ; applyIH.
          cbn in h ; pose proof (infering_sort_size_pos h) ; lia.

    - destruct c.
      unshelve (eapply HCheck ; eauto) ; auto.
      all: applyIH.

    - unshelve eapply HRel ; auto.
      applyIH.

    - unshelve eapply HSort ; auto.
      applyIH.

    - unshelve eapply HProd ; auto.
      all: applyIH.
        * constructor ; auto.
          econstructor.
          eassumption.
        * simpl ; lia.
    
    - unshelve eapply HLambda ; auto.
      all: applyIH.
      * constructor ; auto.
        econstructor.
        eassumption.
      * simpl ; lia.

    - unshelve eapply HLetIn ; auto.
      all: applyIH.
      * constructor ; auto.
        econstructor.
        2: by eauto.
        econstructor.
        eauto.
      * simpl ; lia.

    - unshelve eapply (HApp _ _ _ _ _ _ A) ; auto.
      all: applyIH.
        
    - unshelve eapply HConst ; auto.
      all: applyIH.

    - unshelve eapply HInd ; auto.
      all: applyIH.

    - unshelve eapply HConstruct ; auto.
      all: applyIH.

    - destruct indnpar as [ind' npar'] ; cbn in ind ; cbn in npar ; subst ind ; subst npar.
      unshelve eapply HCase ; auto.
      1-4: applyIH.
      match goal with | IH : forall Σ' wfΣ' d', _ _ (_ ; _ ; ?d) -> _ |- _ =>
        have IH' : forall d' : typing_sum Σ wfΣ, (typing_sum_size d') < (typing_sum_size d) -> Ptyping_sum d' end.
      1: by intros ; apply IH ; constructor 2 ; constructor 1 ; assumption.
      clear IH.
      revert a wfΓ IH'. simpl. clear. intros.
      induction a ; simpl in *.
      1: by constructor.
      destruct r as [? [? ?]].
      constructor.
      + intuition eauto.
        1: unshelve eapply (IH' (sort_cons _ wfΣ _ wfΓ _ _ _)) ; try eassumption.
        2: unshelve eapply (IH' (check_cons _ wfΣ _ wfΓ _ _ _)) ; try eassumption.
        all: simpl ; lia.
      + apply IHa.
        intros. apply IH'. simpl in *. lia.
    
    - unshelve eapply HProj ; auto.
      all: applyIH.

    - unshelve eapply HFix ; eauto.

      all: have IH' : (forall d' : typing_sum Σ wfΣ,
      (typing_sum_size d') <
        (typing_sum_size (inf_cons _ wfΣ _ wfΓ _ (tFix mfix n)
        (infer_Fix Σ Γ mfix n decl i e a a0 i0)))
      -> Ptyping_sum d')
       by intros ; apply IH ; constructor 2 ; constructor 1 ; assumption.
      all: simpl in IH'.
      all: remember (fix_context mfix) as mfixcontext.

      {
        remember (all_size _ _ a0) as s.
        clear -IH'.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        + destruct p ; eexists ; split.
          1: eassumption.
          unshelve eapply (IH' (sort_cons _ wfΣ _ _ _ _ _)).
          all: try assumption.
          simpl. lia.
        + apply (IHa s).
          intros.
          apply IH'.
          cbn. lia.
      }

      have wfΓmfix : wf_local Σ (Γ ,,, mfixcontext).
      { admit. }
      remember (all_size _ (fun d p => infering_sort_size p.π2) a) as s.
      have wf_size : wfl_size wfΓmfix <= wfl_size wfΓ + s.
      { admit. }

      clear -IH' wf_size.
      induction a0 as [| ? ? [? ?]].
      1: by constructor.
      constructor.
      + intuition.
        unshelve eapply (IH' (check_cons _ wfΣ _ _ _ _ _)) ; try assumption.
        simpl. lia.
      + apply IHa0.
        intros ; apply IH'.
        cbn. lia.

    - unshelve eapply HCoFix ; eauto.

      all: have IH' : (forall d' : typing_sum Σ wfΣ,
      (typing_sum_size d') <
        (typing_sum_size (inf_cons _ wfΣ _ wfΓ _ (tCoFix mfix n)
        (infer_CoFix Σ Γ mfix n decl i e a a0 i0)))
      -> Ptyping_sum d')
      by intros ; apply IH ; constructor 2 ; constructor 1 ; assumption.
      all: simpl in IH'.
      all: remember (fix_context mfix) as mfixcontext.

      {
        remember (all_size _ _ a0) as s.
        clear -IH'.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        + destruct p ; eexists ; split.
          1: eassumption.
          unshelve eapply (IH' (sort_cons _ wfΣ _ _ _ _ _)).
          all: try assumption.
          simpl. lia.
        + apply (IHa s).
          intros.
          apply IH'.
          cbn. lia.
      }

      have wfΓmfix : wf_local Σ (Γ,,,mfixcontext).
      { admit. }
      remember (all_size _ (fun d p => infering_sort_size p.π2) a) as s.
      have wf_size : wfl_size wfΓmfix <= wfl_size wfΓ + s.
      { admit. }

      clear -IH' wf_size.
      induction a0.
      1: by constructor.
      constructor.
      + intuition.
        unshelve eapply (IH' (check_cons _ wfΣ _ _ _ _ _)) ; try assumption.
        simpl. lia.
      + apply IHa0.
        intros ; apply IH'.
        cbn. lia.

    - destruct i.
      unshelve (eapply HiSort ; try eassumption) ; try eassumption.
      all: applyIH.

    - destruct i.
      unshelve (eapply HiProd ; try eassumption) ; try eassumption.
      all: applyIH.

    - destruct i.
      unshelve (eapply HiInd ; try eassumption) ; try eassumption.
      all: applyIH.
      
  Admitted.

End TypingInduction.


Ltac my_rename_hyp h th :=
  match th with
  | (wf ?E) => fresh "wf" E
  | (wf (fst_ctx ?E)) => fresh "wf" E
  | (wf _) => fresh "wf"
  | (checking _ _ ?t _) => fresh "check" t
  | (conv _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_typing (@checking _) _) ?G) => fresh "wf" G
  | (All_local_env (lift_typing (@checking _) _) _) => fresh "wf"
  | (All_local_env _ _ ?G) => fresh "H" G
  | context [checking _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.