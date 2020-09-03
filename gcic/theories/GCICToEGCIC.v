(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst.
From MetaCoq.PCUIC Require Import PCUICUtils.
From MetaCoq.EGCIC Require Import EGCICAst EGCICConversion EGCICTyping.
From MetaCoq.GCIC Require Import  PairTerms GCICTyping.

From MetaCoq Require Export LibHypsNaming.

Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Require Import Equations.Type.Relation.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import MonadNotation.

Module E := EGCIC.EGCICAst.
Module G := GCIC.GCICAst.
Module ET := EGCIC.EGCICTyping.

Lemma e_levels_of_udecl Σ : PairLookup.global_levels Σ = EGCICLookup.global_levels Σ.
Proof.
  induction Σ as [|[? []] Σ IHΣ].
  - reflexivity.
  - simpl ; by rewrite IHΣ.
  - simpl ; by rewrite IHΣ.
Qed.

Lemma e_global_ext_levels Σ : PairLookup.global_ext_levels Σ = EGCICLookup.global_ext_levels Σ.
Proof.
  destruct Σ.
  by rewrite /global_ext_levels e_levels_of_udecl.
Qed.

Lemma e_global_constraints Σ : PairLookup.global_constraints Σ = EGCICLookup.global_constraints Σ.
Proof.
  rewrite /global_constraints /global_constraints.
  induction Σ as [|[? []] Σ IHΣ] ; simpl.
  - reflexivity.
  - f_equal ; apply IHΣ.
  - f_equal ; apply IHΣ.
Qed. 

Lemma e_declared_constant Σ cst decl:
  PairLookup.declared_constant Σ cst decl -> EGCICLookup.declared_constant (e_global_env Σ) cst (e_constant_body decl).
Proof.
  induction Σ as [|[k []] Σ IHΣ].
  - intros H ; inversion H.
  - intros H ; inversion H as [H'].
    red. cbn.
    destruct (eq_kername cst k) ; simpl in *.
    1: by inversion_clear H'.
    by apply IHΣ.
  - intros H ; inversion H as [H'].
    red. cbn.
    destruct (eq_kername cst k) ; simpl in *.
    1: by inversion_clear H'.
    by apply IHΣ.
Qed.

Lemma e_declared_minductive Σ mind mdecl:
  PairLookup.declared_minductive Σ mind mdecl ->
  EGCICLookup.declared_minductive (e_global_env Σ) mind (e_mutual_inductive_body mdecl).
Proof.
  induction Σ as [|[k []] Σ IHΣ].
  - intros H ; inversion H.
  - intros H ; inversion H as [H'].
    red. cbn.
    destruct (eq_kername mind k) ; simpl in *.
    1: by inversion_clear H'.
    by apply IHΣ.
  - intros H ; inversion H as [H'].
    red. cbn.
    destruct (eq_kername mind k) ; simpl in *.
    1: by inversion_clear H'.
    by apply IHΣ. 
Qed.

Lemma e_declared_inductive Σ mdecl ind idecl:
  PairLookup.declared_inductive Σ mdecl ind idecl ->
  EGCICLookup.declared_inductive (e_global_env Σ) (e_mutual_inductive_body mdecl) ind (e_one_inductive_body idecl).
Proof.
  intros [? H].
  split.
  1: by apply e_declared_minductive.
  by apply map_nth_error.
Qed.

Lemma e_declared_constructor Σ mdecl idecl ind cdecl :
  PairLookup.declared_constructor Σ mdecl idecl ind cdecl ->
  EGCICLookup.declared_constructor (e_global_env Σ) (e_mutual_inductive_body mdecl) (e_one_inductive_body idecl) ind (on_pi2 eterm cdecl).
Proof.
  intros [? H].
  split.
  1: by apply e_declared_inductive.
  by apply map_nth_error.
Qed.

Lemma e_declared_projection Σ mdecl idecl p pdecl :
  PairLookup.declared_projection Σ mdecl idecl p pdecl ->
  EGCICLookup.declared_projection (e_global_env Σ) (e_mutual_inductive_body mdecl) (e_one_inductive_body idecl)
    p (on_snd eterm pdecl).
Proof.
  intros [? []].
  split ; [|split].
  - by apply e_declared_inductive.
  - by apply map_nth_error.
  - by destruct mdecl.
Qed.

Lemma e_consistent_instance_ext `{checker_flags} Σ udecl u :
  PairLookup.consistent_instance_ext Σ udecl u ->
  EGCICLookup.consistent_instance_ext (e_global_env_ext Σ) (udecl) u.
Proof.
  destruct Σ as [Σ φ].
  intros.
  unfold EGCICLookup.consistent_instance_ext ; rewrite <- e_global_ext_levels.
  unfold EGCICLookup.global_ext_constraints ; simpl ; rewrite <- e_global_constraints.
  assumption.
Qed.

Lemma e_global_ext_constraints `{checker_flags} (Σ : global_env_ext) :
  PairLookup.global_ext_constraints Σ = EGCICLookup.global_ext_constraints (e_global_env_ext Σ).
Proof.
  destruct Σ as [Σ φ].
  rewrite /global_ext_constraints /EGCICLookup.global_ext_constraints /=.
  f_equal.
  apply e_global_constraints.
Qed.

Section CompiledTyping.

  Definition Pcheck `{checker_flags} Σ Γ t T :=
    Σ ;;; Γ |- t ◃ T ->
    (ET.isWfArity typing Σ Γ T + {s & (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) : eSort s}) ->
    (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm t) : (eterm T).

  Definition Pinfer `{checker_flags} Σ Γ t T :=
    Σ ;;; Γ |- t ▹ T -> (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm t) : (eterm T).

  Definition Psort `{checker_flags} Σ Γ t u :=
    Σ ;;; Γ |- t ▸□ u -> (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm t) : (eSort u).

  Definition Pprod `{checker_flags} Σ Γ t na A B :=
    Σ ;;; Γ |- t ▸Π (na,A,B) -> (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm t) : (eProd na (eterm A) (eterm B)).

  Definition Pind `{checker_flags} Σ Γ ind t u args :=
    Σ ;;; Γ |- t ▸{ind} (u,args) -> (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm t) : (mkApps (eInd ind u) (map eterm args)).

  Definition PΓ `{checker_flags} Σ Γ (wfΓ : wf_local Σ Γ) :=
    EGCICTyping.wf_local Σ Γ.

Lemma e_wf_local `{checker_flags} Σ Γ (all: wf_local Σ Γ) :
  All_local_env_over checking (fun Σ Γ _ t T _ => Pcheck Σ Γ t T) Σ Γ all -> ET.wf_local Σ Γ.
Proof.
  intros X.
  induction X.
  - by constructor.
  - constructor ; auto.
    simpl.
    inversion_clear o ; simpl in *.
    eexists. eapply X0.
    1: destruct H0 ; auto.
    left.
    eexists. eexists.
    split ; cbn.
    1: reflexivity.
    assumption.
  - inversion_clear o.
    constructor ; auto.
    + eexists. eapply X0.
      1: destruct H0 as [? []]; auto.
      left.
      eexists. eexists.
      split ; cbn.
      1: reflexivity.
      assumption.
    + eapply X1.
      1: destruct H0 as [? []] ; auto.
      right.
      eexists.
      apply X0.
      1: destruct H0 as [? []] ; auto.
      left.
      eexists. eexists.
      split ; cbn.
      1: reflexivity.
      assumption.
Qed.

Theorem GT_to_ET `{cf : checker_flags} : env_prop Pcheck Pinfer Psort Pprod Pind (@PΓ).
Proof.
  apply typing_ind_env.
  - intros Σ wfΣ Γ wfΓ wfoΓ.
    induction Γ as [| [r [t|] T] Γ].
    + constructor.
    + inversion_clear wfoΓ. constructor ; fold (map e_decl Γ) ; fold (e_context Γ).
      * eapply IHΓ ; eassumption.
      * inversion_clear X0 ; simpl in *.
        eexists ; apply X1 ; destruct H ; intuition.
        left. simpl.
        apply isWfArity_Sort.
        eapply e_wf_local.
        eassumption.

      * inversion_clear X0 ; simpl in *.
        apply X2 ; destruct H as [? []] ; intuition.
        right.
        eexists.
        eapply X1.
        1: eassumption.
        left.
        apply isWfArity_Sort.
        eapply e_wf_local.
        eassumption.

    + inversion_clear wfoΓ. constructor ; fold (map e_decl Γ) ; fold (e_context Γ).
      * eapply IHΓ ; eassumption.
      * inversion_clear X0 ; simpl in *.
        eexists ; apply X1 ; destruct H ; intuition.
        left.
        apply isWfArity_Sort.
        eapply e_wf_local.
        eassumption.

  - intros Σ wfΣ Γ wfΓ n decl nΓ ; red ; intros.
    simpl ; change (eterm (decl_type decl)) with (EGCICAst.decl_type (e_decl decl)).
    constructor.
    1: assumption.
    by rewrite nth_error_map nΓ.

  - intros Σ wfΣ Γ wfΓ l HΓ Hl ; red ; intros.
    simpl ; constructor.
    1: assumption.
    destruct Σ ; cbn.
    by rewrite <- e_global_ext_levels.

  - intros ; red ; intros.
    constructor.
    all : intuition.

  - intros ; red ; intros.
    econstructor.
    all: intuition eauto.

  - intros ; red ; intros.
    econstructor.
    all: intuition eauto.
    
  - intros ; red ; intros.
    econstructor.
    1: intuition eauto.
    apply X3 ; auto.
    right.
    eexists.
    admit. (*validity (+ SR ?)*)
    
  - intros ; red ; intros.
    simpl ; change (eterm (cst_type decl)) with (EGCICAst.cst_type (e_constant_body decl)).
    econstructor.
    + by intuition eauto.
    + by apply e_declared_constant.
    + by apply e_consistent_instance_ext.

  - intros ; red ; intros.
    simpl ; change (eterm (ind_type idecl)) with (EGCICAst.ind_type (e_one_inductive_body idecl)).
    econstructor.
    + by intuition eauto.
    + by eapply e_declared_inductive ; eassumption.
    + by apply e_consistent_instance_ext.

  - intros ; red ; intros.
    simpl ; econstructor.
    + by intuition eauto.
    + by apply e_declared_constructor ; eassumption.
    + by apply e_consistent_instance_ext.

  - intros ; red ; intros.
    simpl.
    rewrite map_app map_skipn /=.
    econstructor.
    + by apply e_declared_inductive ; eassumption.
    + done.
    + admit. (*projection of build_case_predicate*)
    + apply X4 ; auto.
      right ; eexists.
      admit. (*build_case_predicate is a valid type*)
    + eassumption.
    + by intuition eauto.
    + assumption.  
    + simpl ; rewrite firstn_map ; fold params.
      admit. (*projection of build_branches_types*)
    + admit. (*projection of branches well-typedness*)
  
  - intros ; red ; intros.
    subst ty ; destruct pdecl as [k ty] ; simpl in *.
    rewrite map_rev.
    change (eterm ty) with ((k,eterm ty).2).
    econstructor.
    + change (k, eterm ty) with (on_snd eterm (k, ty)). 
      by eapply e_declared_projection ; eassumption.
    + by intuition eauto.
    + rewrite map_length.
      destruct mdecl ; assumption.
  
  - intros ; red ; intros.
    change (eterm (dtype decl)) with (dtype (map_def eterm eterm decl)).
    econstructor.
    + assumption.
    + by rewrite /e_mfix nth_error_map H0.
    + eapply ET.wf_local_app.
      replace (E.app_context _ _)
        with (e_context (Γ ,,, fix_context mfix)) by eapply map_app.
      assumption.
    + red in X.
      admit. (*strengthening of well-formedness of the fix_context *)
    + unfold Pcheck in X0 ; simpl in X0.
      clear X1.
      remember (fix_context mfix) as Γ'.
      remember (EGCICLiftSubst.fix_context (e_mfix mfix)) as Γ''.
      have HΓ : Γ'' = e_context Γ' by admit.
      clear -X0 HΓ.
      dependent induction X0.
      * constructor.
      * constructor.
        2: rewrite HΓ ; exact IHX0.
        intuition auto.
        rewrite HΓ /= /e_context map_length /E.app_context -map_app.
        apply X2.
        eexists.
        admit. (*this is a consequence of the well-formedness of Γ,,,Γ', via weakening*)
    + admit. (*wf_fixpoint ??*)
  
  - intros ; red ; intros.
    econstructor.
    all: intuition.

  - intros ; red ; intros.
    apply X3 ; auto.
    right. eexists.
    intuition.

  - intros ; red ; intros.
    simpl.
    econstructor ; auto.
    + admit. (*validity*)
    + admit. (*inferred eSort u for T is well-typed -> SR ? *)
    + by apply red_consi.

  - intros ; red ; intros.
    simpl.
    econstructor ; auto.
    + admit. (*validity*)
    + constructor ; auto.
      admit. (*sorts are well-typed*)
    + apply consi_alt.
      eexists. eexists. repeat split.
      * eassumption.
      * apply refl_red.
      * constructor. 

  - intros ; red ; intros.
    simpl.
    econstructor ; auto.
    + admit. (*validity*)
    + admit. (*inferred eProd na A B for T is well-typed -> SR ? *) 
    + by apply red_consi.

  - intros ; red ; intros.
    simpl.
    econstructor ; auto.
    + admit. (*validity*)
    + constructor.
      * econstructor.
        admit. (*Sorts are well-typed*)
      * econstructor.
        admit. (*Sorts are well-typed*)
    + apply consi_alt.
      eexists. eexists. repeat split.
      * eassumption.
      * apply refl_red.
      * constructor. 

  - intros ; red ; intros.
    simpl.
    econstructor ; auto.
    red in X1.
    + right. eexists.
      admit. (*validity + SR*)
    + admit. (*reduction implies conversion*)

  - intros ; red ; intros.
    simpl.
    destruct X4 as [|[]].
    + econstructor ; auto.
      1: admit. (*validity*)
      admit. (*well-formed arity is typable, should not happen?*)
    + econstructor ; auto.
      1: admit. (*validity*)
      eassumption.
Admitted.