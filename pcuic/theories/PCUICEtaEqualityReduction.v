(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICInduction PCUICAstUtils PCUICLiftSubst PCUICTyping
     PCUICReduction PCUICWeakening PCUICEquality PCUICUnivSubstitution
     PCUICContextRelation PCUICSigmaCalculus PCUICContextReduction PCUICContextRelation
     PCUICParallelReduction PCUICParallelReductionConfluence
     PCUICRedTypeIrrelevance.
From MetaCoq.PCUIC Require Import PCUICEtaEquality.
From MetaCoq.PCUIC Require Import PCUICConfluence.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import CRelationClasses CMorphisms.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

(* This comes from PCUICUnivSubstitution *)

Section UniverseSubstitution.

Lemma subst_equal_inst_global_inst Σ Re Rle gr :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  forall u u1 u2, R_universe_instance Re u1 u2 ->
             R_global_instance Σ Re Rle gr (subst_instance u1 u)
                                    (subst_instance u2 u).
Proof.
  intros reflRe hRe subr u u1 u2 Ru1u2.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance as [v|]; auto using subst_equal_inst_inst.
  induction u in v |- *; cbnr; try now constructor.
  - destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
    * pose proof (hRe (Universe.make a) u1 u2 Ru1u2) as HH.
      now rewrite !subst_instance_univ_make in HH.
    * pose proof (hRe (Universe.make a) u1 u2 Ru1u2) as HH.
      now rewrite !subst_instance_univ_make in HH.
Qed.


Lemma eq_term_upto_univ_eta_subst_instance Σ Re Rle :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  forall t u1 u2,
    R_universe_instance Re u1 u2 ->
    eq_term_upto_univ_eta Σ Re Rle (subst_instance u1 t)
                            (subst_instance u2 t).
Proof.
  intros ref hRe subr t.
  induction t in Rle, ref, hRe, subr |- * using term_forall_list_ind; intros u1 u2 hu.
  all: cbn; try constructor; eauto using subst_equal_inst_inst.
  all: try eapply All2_map, All_All2; tea; cbn; intros; rdest; eauto.
  all: try (eapply X0 || eapply IHt || eapply IHt1 || eapply IHt2 || eapply e || eapply e0); try typeclasses eauto; auto.
  all: eauto using subst_equal_inst_global_inst.
  - rewrite /eq_predicate /=. intuition auto.
    * solve_all. eapply All_All2; tea; cbn; intros; rdest; eauto.
      eapply X; eauto. tc.
    * eapply subst_equal_inst_inst => //.
    * reflexivity.
    * eapply X => //.
  - reflexivity.
Qed.

Context {cf : checker_flags}.

Lemma precompose_subst_instance_global Σ Re Rle gr u i i' :
  precompose (R_global_instance Σ Re Rle gr) (subst_instance u) i i'
  <~> R_global_instance Σ (precompose Re (subst_instance_univ u))
    (precompose Rle (subst_instance_univ u)) gr i i'.
Proof.
  unfold R_global_instance, R_opt_variance, subst_instance.
  destruct global_variance as [v|]; eauto using precompose_subst_instance.
  induction i in i', v |- *; destruct i', v; simpl; try split; auto.
  - destruct (IHi i' []). intros; auto.
  - destruct (IHi i' []). intros; auto.
  - destruct (IHi i' v). intros []; split; auto.
    destruct t0; simpl in *; auto.
    * now rewrite !subst_instance_make'_make.
    * now rewrite !subst_instance_make'_make.
  - destruct (IHi i' v). intros []; split; auto.
    destruct t0; simpl in *; auto.
    * now rewrite !subst_instance_make'_make in H.
    * now rewrite !subst_instance_make'_make in H.
Qed.

Definition precompose_subst_instance_global__1 Σ Re Rle gr u i i'
  := fst (precompose_subst_instance_global Σ Re Rle gr u i i').

Definition precompose_subst_instance_global__2 Σ Re Rle gr u i i'
  := snd (precompose_subst_instance_global Σ Re Rle gr u i i').

Global Instance eq_term_upto_univ_eta_subst_preserved Σ
  (Re Rle : ConstraintSet.t -> Universe.t -> Universe.t -> Prop)
  {he: SubstUnivPreserved Re} {hle: SubstUnivPreserved Rle}
  : SubstUnivPreserved (fun φ => eq_term_upto_univ_eta Σ (Re φ) (Rle φ)).
Proof.
  intros φ φ' u HH t t' e.
  specialize (he _ _ _ HH).
  specialize (hle _ _ _ HH).
  clear HH. cbn in he, hle.
  revert hle.
  dependent induction e using eq_term_upto_univ_eta_list_ind ; intros hle ;
    cbn in * ; constructor ; eauto using precompose_subst_instance__2, R_universe_instance_impl'.
  all: try solve [apply All2_map; eapply All2_impl ; tea;
    cbn; intros; rdest; eauto with univ_subst ].
  - rewrite -PCUICUnivSubst.subst_instance_lift ; auto.
  - rewrite -PCUICUnivSubst.subst_instance_lift ; auto. 
  - eapply precompose_subst_instance_global__2.
    eapply R_global_instance_impl; eauto.
  - eapply precompose_subst_instance_global__2.
    eapply R_global_instance_impl; eauto.
  - destruct X as (?&?&?&?&?).
    repeat split; simpl; eauto; solve_all.
    eapply precompose_subst_instance.
    eapply R_universe_instance_impl; eauto.
Qed.

Lemma leq_term_eta_subst_instance Σ : SubstUnivPreserved (leq_term_eta Σ).
Proof. exact _. Qed.

Lemma eq_term_eta_subst_instance Σ : SubstUnivPreserved (eq_term_eta Σ).
Proof. exact _. Qed.

Lemma compare_term_subst_instance le Σ : SubstUnivPreserved (compare_term_eta le Σ).
Proof. destruct le; simpl; unfold compare_term_eta.
  - apply leq_term_eta_subst_instance.
  - apply eq_term_eta_subst_instance.
Qed.

End UniverseSubstitution.

(* This file is for now parallel to PCUICConfluence *)

Lemma on_one_decl_compare_decl Σ Re Rle Γ x y :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  on_one_decl
    (fun (_ : context) (y0 v' : term) => eq_term_upto_univ_eta Σ Re Rle y0 v') Γ x y ->
  compare_decls (eq_term_upto_univ_eta Σ Re Rle) (eq_term_upto_univ_eta Σ Re Rle) x y.
Proof.
  intros heq hle.
  destruct x as [na [b|] ty], y as [na' [b'|] ty']; cbn; intuition (subst; auto);
  constructor; auto; reflexivity.
Qed.

Notation eq_eta_one_decl Σ Re Rle := 
  (OnOne2_local_env
    (on_one_decl
      (fun _ (x0 y0 : term) => 
        eq_term_upto_univ_eta Σ Re Rle x0 y0))).

Lemma red1_eq_context_upto_eta_l {Σ Rle Re Γ Δ u v} :
  RelationClasses.Reflexive Rle ->
  SubstUnivPreserving Rle ->
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  red1 Σ Γ u v ->
  eq_context_upto_eta Σ Re Rle Γ Δ ->
  ∑ v', red1 Σ Δ u v' *
        eq_term_upto_univ_eta Σ Re Re v v'.
Proof.
  intros hle hle' he he' hlee h e.
  induction h in Δ, e |- * using red1_ind_all.
  all: try solve [
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | reflexivity ; eauto
    ]
  ].
  all: try solve [
    destruct (IHh _ e) as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor; eauto ;
      reflexivity ; eauto
    ]
  ].
  all: try solve [
    match goal with
    | r : red1 _ (?Γ ,, ?d) _ _ |- _ =>
      assert (e' : eq_context_upto_eta Σ Re Rle (Γ,, d) (Δ,, d))
      ; [
        constructor ; [ eauto | constructor; eauto ] ;
        reflexivity ; eauto
      |
      ]
    end;
    destruct (IHh _ e') as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor ; eauto ;
      reflexivity ; eauto
    ]
  ].
  - assert (h : ∑ b',
                (option_map decl_body (nth_error Δ i) = Some (Some b')) *
                eq_term_upto_univ_eta Σ Re Re body b').
    { induction i in Γ, Δ, H, e |- *.
      - destruct e.
        + cbn in *. discriminate.
        + simpl in *. depelim c; noconf H.
          simpl. eexists; split; eauto.
      - destruct e.
        + cbn in *. discriminate.
        + simpl in *. eapply IHi in H ; eauto.
    }
    destruct h as [b' [e1 e2]].
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_eta_lift ; eauto.
  - eapply OnOne2_prod_inv in X as [_ X].
    eapply OnOne2_apply, OnOne2_apply in X; tea.
    eapply OnOne2_exist' in X as [pars' [parred pareq]]; intros; tea.
    eexists. split. eapply case_red_param; tea.
    econstructor; eauto.
    red. intuition; eauto. reflexivity.
    apply All2_same; intros. intuition eauto; reflexivity.
  - specialize (IHh (Δ ,,, inst_case_predicate_context p)).
    forward IHh.
    1:{ eapply eq_context_upto_eta_cat => //.
        now reflexivity. }
    destruct IHh as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + econstructor; try red; intuition (simpl; eauto); try reflexivity.
      * now eapply All2_same.
      * eapply All2_same. split; reflexivity.
  - specialize (IHh _ e) as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + econstructor; try red; intuition (simpl; eauto); try reflexivity.
      * now eapply All2_same.
      * eapply All2_same. split; reflexivity.
  - eapply (OnOne2_impl (Q:=fun x y => (∑ v', _) × bcontext x = bcontext y)) in X; tea.
    2:{ intros x y [[red IH] eq]. split; tas. 
        specialize (IH (Δ ,,, inst_case_branch_context p x)).
        forward IH by now apply eq_context_upto_eta_cat. exact IH. }
    eapply (OnOne2_exist' _ (fun x y => on_Trel_eq (red1 Σ (Δ ,,, inst_case_branch_context p x)) bbody bcontext x y)
      (fun x y => on_Trel_eq (eq_term_upto_univ_eta Σ Re Re) bbody bcontext x y)) in X as [brr [Hred Heq]]; tea.
    2:{ intros x y [[v' [redv' eq]] eqctx].
        exists {| bcontext := bcontext x; bbody := v' |}.
        intuition auto. }
    eexists; split.
    eapply case_red_brs; tea.
    econstructor; eauto; try reflexivity.
    eapply OnOne2_All2; tea => /=; intuition eauto; try reflexivity.
    now rewrite b.

(*   - destruct (IHh _ e) as [x [redl redr]].
    exists (tApp x M2).
    split. constructor; auto.
    constructor. eapply eq_term_upto_univ_impl. 5:eauto.
    all:auto. 1-3:typeclasses eauto.
    reflexivity. *)
  - assert (h : ∑ ll,
      OnOne2 (red1 Σ Δ) l ll *
      All2 (eq_term_upto_univ_eta Σ Re Re) l' ll
    ).
    { induction X.
      - destruct p as [p1 p2].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor. eassumption.
        + constructor.
          * assumption.
          * eapply All2_same.
            intros.
            reflexivity ; eauto.
      - destruct IHX as [ll [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          reflexivity ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply evar_red. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ Δ d.(dtype) d'.(dtype) ×
          (d.(dname), d.(dbody), d.(rarg)) =
          (d'.(dname), d'.(dbody), d'.(rarg))
        ) mfix0 mfix'
      *
      All2 (fun x y =>
        eq_term_upto_univ_eta Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ_eta Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y) *
        (eq_binder_annot (dname x) (dname y)))%type mfix1 mfix').
    { induction X.
      - destruct p as [[p1 p2] p3].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            reflexivity ; eauto.
          * eapply All2_same.
            intros. repeat split ; eauto.
            all: reflexivity ; eauto.
      - destruct IHX as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: reflexivity ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_ty. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) ×
          (d.(dname), d.(dtype), d.(rarg)) =
          (d'.(dname), d'.(dtype), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ_eta Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ_eta Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y) * 
        eq_binder_annot (dname x) (dname y))%type mfix1 mfix').
    { (* Maybe we should use a lemma using firstn or skipn to keep
          fix_context intact. Anything general?
        *)
      Fail induction X using OnOne2_ind_l.
      (* This FAILs because it reduces the type of X before unifying
          unfortunately...
        *)
      change (
        OnOne2
      ((fun L (x y : def term) =>
        (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Δ : context,
            eq_context_upto_eta Σ Re Rle (Γ ,,, fix_context L) Δ ->
            ∑ v' : term,
              red1 Σ Δ (dbody x) v' × eq_term_upto_univ_eta Σ Re Re (dbody y) v'))
        × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix0) mfix0 mfix1
      ) in X.
      Fail induction X using OnOne2_ind_l.
      revert mfix0 mfix1 X.
      refine (OnOne2_ind_l _ (fun (L : mfixpoint term) (x y : def term) =>
    ((red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
      × (forall Δ0 : context,
        eq_context_upto_eta Σ Re Rle (Γ ,,, fix_context L) Δ0 ->
        ∑ v' : term,
          red1 Σ Δ0 (dbody x) v' × eq_term_upto_univ_eta Σ Re Re (dbody y) v'))
    × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)))
  (fun L mfix0 mfix1 o => ∑ mfix' : list (def term),
  OnOne2
      (fun d d' : def term =>
        red1 Σ (Δ ,,, fix_context L) (dbody d) (dbody d')
        × (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')) mfix0 mfix'
    × All2
        (fun x y : def term =>
          ((eq_term_upto_univ_eta Σ Re Re (dtype x) (dtype y)
          × eq_term_upto_univ_eta Σ Re Re (dbody x) (dbody y)) ×
          (rarg x = rarg y)) *
          eq_binder_annot (dname x) (dname y)) mfix1 mfix') _ _).
      - intros L x y l [[p1 p2] p3].
        assert (
            e' : eq_context_upto_eta Σ Re Rle (Γ ,,, fix_context L) (Δ ,,, fix_context L)
        ).
        { eapply eq_context_upto_eta_cat ; eauto. reflexivity. }
        eapply p2 in e' as hh. destruct hh as [? [? ?]].
        eexists. constructor.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            reflexivity ; eauto.
          * eapply All2_same. intros.
            repeat split ; eauto.
            all: reflexivity ; eauto.
      - intros L x l l' h [? [? ?]].
        eexists. constructor.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: reflexivity ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_body. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ Δ d.(dtype) d'.(dtype) ×
          (d.(dname), d.(dbody), d.(rarg)) =
          (d'.(dname), d'.(dbody), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ_eta Σ Re Re (dtype x) (dtype y) ×
        eq_term_upto_univ_eta Σ Re Re (dbody x) (dbody y) ×
        (rarg x = rarg y) ×
        eq_binder_annot (dname x) (dname y))%type mfix1 mfix'
    ).
    { induction X.
      - destruct p as [[p1 p2] p3].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            reflexivity ; eauto.
          * eapply All2_same.
            intros. repeat split ; eauto.
            all: reflexivity ; eauto.
      - destruct IHX as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: reflexivity ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_ty. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) ×
          (d.(dname), d.(dtype), d.(rarg)) =
          (d'.(dname), d'.(dtype), d'.(rarg))
        ) mfix0 mfix' ×
      All2 (fun x y =>
        eq_term_upto_univ_eta Σ Re Re (dtype x) (dtype y) ×
        eq_term_upto_univ_eta Σ Re Re (dbody x) (dbody y) ×
        (rarg x = rarg y) ×
        eq_binder_annot (dname x) (dname y))%type mfix1 mfix').
    { (* Maybe we should use a lemma using firstn or skipn to keep
          fix_context intact. Anything general?
        *)
      Fail induction X using OnOne2_ind_l.
      (* This FAILs because it reduces the type of X before unifying
          unfortunately...
        *)
      change (
        OnOne2
      ((fun L (x y : def term) =>
        (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Δ : context,
            eq_context_upto_eta Σ Re Rle (Γ ,,, fix_context L) Δ ->
            ∑ v' : term,
              red1 Σ Δ (dbody x) v' × eq_term_upto_univ_eta Σ Re Re (dbody y) v' ))
        × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix0) mfix0 mfix1
      ) in X.
      Fail induction X using OnOne2_ind_l.
      revert mfix0 mfix1 X.
      refine (OnOne2_ind_l _ (fun (L : mfixpoint term) (x y : def term) =>
    (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
      × (forall Δ0 : context,
        eq_context_upto_eta Σ Re Rle (Γ ,,, fix_context L) Δ0 ->
        ∑ v' : term,
            red1 Σ Δ0 (dbody x) v' × eq_term_upto_univ_eta Σ Re Re (dbody y) v' ))
    × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) (fun L mfix0 mfix1 o => ∑ mfix' : list (def term),
  (OnOne2
      (fun d d' : def term =>
        red1 Σ (Δ ,,, fix_context L) (dbody d) (dbody d')
        × (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')) mfix0 mfix'
    × All2
        (fun x y : def term =>
          eq_term_upto_univ_eta Σ Re Re (dtype x) (dtype y)
          × eq_term_upto_univ_eta Σ Re Re (dbody x) (dbody y) ×
          rarg x = rarg y ×
          eq_binder_annot (dname x) (dname y)) mfix1 mfix')) _ _).
      - intros L x y l [[p1 p2] p3].
        assert (
            e' : eq_context_upto_eta Σ Re Rle (Γ ,,, fix_context L) (Δ ,,, fix_context L)
        ).
        { eapply eq_context_upto_eta_cat ; eauto. reflexivity. }
        eapply p2 in e' as hh. destruct hh as [? [? ?]].
        eexists. constructor.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            reflexivity ; eauto.
          * eapply All2_same. intros.
            repeat split ; eauto.
            all: reflexivity ; eauto.
      - intros L x l l' h [? [? ?]].
        eexists. constructor.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: reflexivity ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_body. eassumption.
    + constructor; assumption.
Qed.

Lemma eq_context_eta_extended_subst {Σ Re Rle Γ Δ k} :
  eq_context_gen (eq_term_upto_univ_eta Σ Re Re) (eq_term_upto_univ_eta Σ Re Rle) Γ Δ ->
  All2 (eq_term_upto_univ_eta Σ Re Re) (extended_subst Γ k) (extended_subst Δ k).
Proof.
  intros Heq.
  induction Heq in k |- *; simpl.
  - constructor; auto.
  - depelim p => /=.
    * constructor. eauto. constructor; eauto. eauto.
    * constructor.
      + rewrite (eq_context_gen_context_assumptions Heq).
        len. rewrite (All2_fold_length Heq).
        eapply eq_term_upto_univ_eta_substs; eauto. tc.
        eapply eq_term_upto_univ_eta_lift, e0.
      + eapply IHHeq.
Qed.

Lemma eq_context_gen_eq_context_upto_eta Σ Re Rle Γ Γ' :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  eq_context_gen eq eq Γ Γ' ->
  eq_context_upto_eta Σ Re Rle Γ Γ'.
Proof.
  intros.
  eapply PCUICEnvironment.All2_fold_impl; tea.
  cbn; intros ????. move => []; constructor; subst; auto; reflexivity.
Qed.


Lemma red1_eq_context_upto_univ_eta_l Σ Re Rle Γ ctx ctx' ctx'' :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  SubstUnivPreserving Re ->
  SubstUnivPreserving Rle ->
  RelationClasses.subrelation Re Rle ->
  eq_context_gen (eq_term_upto_univ_eta Σ Re Re)
   (eq_term_upto_univ_eta Σ Re Re) ctx ctx' ->
  OnOne2_local_env (on_one_decl
    (fun (Γ' : context) (u v : term) =>
    forall (Rle : Relation_Definitions.relation Universe.t)
      (u' : term),
    RelationClasses.Reflexive Re ->
    RelationClasses.Reflexive Rle ->
    RelationClasses.Transitive Re ->
    RelationClasses.Transitive Rle ->
    SubstUnivPreserving Re ->
    SubstUnivPreserving Rle ->
    (forall x y : Universe.t, Re x y -> Rle x y) ->
    eq_term_upto_univ_eta Σ Re Rle u u' ->
    ∑ v' : term,
      red1 Σ (Γ,,, Γ') u' v'
      × eq_term_upto_univ_eta Σ Re Rle v v')) ctx ctx'' ->
  ∑ pctx,
    red1_ctx_rel Σ Γ ctx' pctx *
    eq_context_gen (eq_term_upto_univ_eta Σ Re Re) (eq_term_upto_univ_eta Σ Re Re) ctx'' pctx.
Proof.
  intros.
  rename X into e, X0 into X.
  induction X in e, ctx' |- *.
  - red in p. simpl in p.
    depelim e. depelim c.
    destruct p as [-> p].
    eapply p in e1 as hh ; eauto.
    destruct hh as [? [? ?]].
    eapply red1_eq_context_upto_eta_l in r; cycle -1.
    { eapply eq_context_upto_eta_cat; tea.
      reflexivity. }
    all:try tc.
    destruct r as [v' [redv' eqv']].
    eexists; split.
    + constructor; tea. red. cbn. split; tea. reflexivity.
    + constructor. all: eauto. constructor; auto.
      now transitivity x.
  - depelim e.
    depelim c.
    destruct p as [-> [[p ->]|[p ->]]].
    { eapply p in e2 as hh ; eauto.
      destruct hh as [? [? ?]].
      eapply red1_eq_context_upto_eta_l in r; cycle -1.
      { eapply eq_context_upto_eta_cat; tea.
        reflexivity. }
      all:try tc.
      destruct r as [v' [redv' eqv']].
      eexists; split.
      + constructor; tea. red. cbn. split; tea. reflexivity.
        left. split; tea. reflexivity.
      + constructor. all: eauto. constructor; auto.
        now transitivity x. }
    { eapply p in e1 as hh ; eauto.
      destruct hh as [? [? ?]].
      eapply red1_eq_context_upto_eta_l in r; cycle -1.
      { eapply eq_context_upto_eta_cat; tea.
        reflexivity. }
      all:try tc.
      destruct r as [v' [redv' eqv']].
      eexists; split.
      + constructor; tea. red. cbn. split; tea. reflexivity.
        right. split; tea. reflexivity.
      + constructor. all: eauto. constructor; auto.
        now transitivity x. }
  - depelim e.
    destruct (IHX _ e) as [? [? ?]].
    eexists. split.
    + now eapply onone2_localenv_cons_tl.
    + constructor. all: eauto.
Qed.


Global Instance eq_context_upto_univ_eta_subst_preserved {cf:checker_flags} Σ
  (Re Rle : ConstraintSet.t -> Universe.t -> Universe.t -> Prop)
  {he: SubstUnivPreserved Re} {hle: SubstUnivPreserved Rle}
  : SubstUnivPreserved (fun φ => eq_context_upto_eta Σ (Re φ) (Rle φ)).
Proof.
  intros φ φ' u vc Γ Δ eqc.
  eapply All2_fold_map.
  eapply PCUICEnvironment.All2_fold_impl; tea.
  cbn; intros.
  destruct X ; constructor ; cbn; auto ; eapply eq_term_upto_univ_eta_subst_preserved ; tc; eauto.
Qed.

(* Lemma eq_context_gen_eq_univ_subst_preserved u Γ Δ :
  eq_context_gen eq eq Γ Δ ->
  eq_context_gen eq eq (subst_instance u Γ) (subst_instance u Δ).
Proof.
  intros onctx.
  eapply All2_fold_map.
  eapply PCUICEnvironment.All2_fold_impl; tea.
  cbn; intros.
  destruct X; constructor; cbn; auto; now subst.
Qed. *)

Lemma eq_term_upto_univ_eta_subst_instance' {cf:checker_flags} Σ Re Rle :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->  
  RelationClasses.subrelation Re Rle ->
  SubstUnivPreserved (fun _ => Re) ->
  SubstUnivPreserved (fun _ => Rle) ->
  forall x y u1 u2,
    R_universe_instance Re u1 u2 ->
    eq_term_upto_univ_eta Σ Re Rle x y ->
    eq_term_upto_univ_eta Σ Re Rle (subst_instance u1 x) (subst_instance u2 y).
Proof.
  intros.
  transitivity (subst_instance u2 x).
  1: now eapply eq_term_upto_univ_eta_subst_instance.
  eapply (eq_term_upto_univ_eta_subst_preserved Σ (fun _ => Re) (fun _ => Rle) ConstraintSet.empty ConstraintSet.empty u2).
  2: assumption.
  red. destruct check_univs => //.
Qed.

Lemma eq_context_upto_univ_eta_subst_instance Σ Re Rle :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  forall x u1 u2,
    R_universe_instance Re u1 u2 ->
    eq_context_upto_eta Σ Re Rle (subst_instance u1 x) (subst_instance u2 x).
Proof.
  intros ref hRe subr t.
  induction t. intros.
  - rewrite /subst_instance /=. constructor.
  - rewrite /subst_instance /=. constructor; auto.
    destruct a as [na [b|] ty]; cbn; constructor; cbn; eauto using eq_term_upto_univ_eta_subst_instance.
    apply eq_term_upto_univ_eta_subst_instance; eauto. tc.
Qed.

Lemma eq_context_upto_univ_eta_subst_instance' Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  forall x y u1 u2,
    R_universe_instance Re u1 u2 ->
    eq_context_gen eq eq x y ->
    eq_context_upto_eta Σ Re Rle (subst_instance u1 x) (subst_instance u2 y).
Proof.
  intros ref refl' tr trle hRe subr x y u1 u2 ru eqxy.
  etransitivity.
  - eapply eq_context_upto_univ_eta_subst_instance; tc. tea.
  - apply eq_context_gen_eq_context_upto_eta ; tc.
    eapply eq_context_gen_eq_univ_subst_preserved; tea.
Qed.

Lemma structural_red1_eq_term Σ Re Rle Γ u u' v:
  ~ isLambda u ->
  (forall u'' Δ (e : eq_term_upto_univ_eta Σ Re Rle (lift0 #|Δ| u) u''),
    ~ isEta e ->
    ∑ v'', red Σ (Γ ,,, Δ) u'' v'' × eq_term_upto_univ_eta Σ Re Rle (lift0 #|Δ| v) v'') ->
  eq_term_upto_univ_eta Σ Re Rle u u' ->
  ∑ v', red Σ Γ u' v' × eq_term_upto_univ_eta Σ Re Rle v v'.
Proof.
  intros iLu base.
  replace u with (lift_applies #|@nil context_decl| [] u) by apply lift0_id.
  replace v with (lift_applies #|@nil context_decl| [] v) by apply lift0_id.
  change Γ with (Γ ,,, []).
  generalize (@nil context_decl), (@nil nat).
  intros Δ l e.
  induction u' in Δ, l, u, v, iLu, Rle, base, e |- *.
  all: try solve [destruct l ; cbn in * ;
        [ eapply (base _ _ e) ; auto ; destruct u ; by dependent inversion e |
        by inversion e ]].

  - inversion e ; subst.
    1,3: destruct l, u ; cbn in * ; congruence.
    replace (tApp _ _) with (lift_applies #|Δ,, vass na u'1| (0::(map S l)) u) in X
      by (cbn ; by rewrite lift_lift_applies).
    edestruct IHu'2 as (v'2&?&?) ; eauto.
    exists (tLambda na u'1 v'2) ; split.
    1: by apply red_abs ; [reflexivity | assumption].
    constructor.
    by rewrite lift_lift_applies.
  - destruct l.
    + cbn in *.
      apply (base _ _ e).
      destruct u ; cbn in * ; auto.
      all: dependent inversion e ; cbn ; auto.
    + cbn in *.
      inversion e ; subst.
      edestruct IHu'1 as (v'1&?&?) ; eauto.
      exists (tApp v'1 u'2) ; split.
      1: by apply red_app ; [assumption | reflexivity].
      by constructor.
Qed.

Fixpoint red1_depth {Σ Γ u v} (r : red1 Σ Γ u v) {struct r}: size.
Proof.
  destruct r ;
  match goal with
    | H : red1 _ _ _ _ |- _ => exact (S (red1_depth _ _ _ _ H))
    | O : OnOne2 (red1 _ _) _ _ |- _ =>
      induction O as [? ? ? p'|? ? ? ? IHO] ; [exact (S (red1_depth _ _ _ _ p'))|exact IHO]
    | O : OnOne2 (fun _ _ _ => red1 _ _ _ _ × _) _ _ |- _ =>
      induction O as [? ? ? p'|? ? ? ? IHO] ; [exact (S (red1_depth _ _ _ _ p'.1))|exact IHO]
    | _ => exact 1
  end.
Defined.

Lemma weakening_red1_0 `{cf : checker_flags} Σ Γ Γ' M N :
  wf Σ ->
  PCUICOnFreeVars.on_free_vars (fun _ : nat => true) M ->
  red1 Σ Γ M N ->
  red1 Σ (Γ,,,Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
Proof.
  intros.
  change 0 with (#|@nil context_decl|).
  change (Γ,,, Γ') with (Γ,,, Γ',,, lift_context #|Γ'| 0 []).
  apply weakening_red1 ; auto.
Qed.

Lemma red1_eq_term_upto_univ_l `{cf : checker_flags} {Σ} {wfΣ : wf Σ} Re Rle Γ u v u' :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  SubstUnivPreserving Re ->
  SubstUnivPreserving Rle ->
  RelationClasses.subrelation Re Rle ->
  red1 Σ Γ u v ->
  eq_term_upto_univ_eta Σ Re Rle u u' ->
  ∑ v', red Σ Γ u' v' *
         eq_term_upto_univ_eta Σ Re Rle v v'.
Proof.
  intros he he' tRe tRle hle hle' hR r.
  revert Rle he' tRle hle' hR.
  set p := (u ; (v ; (u' ; (Γ ; r)))) : ∑ u v u' Γ, red1 Σ Γ u v.
  change v with p.π2.π1.
  change Γ with p.π2.π2.π2.π1.
  change u' with p.π2.π2.π1.
  change u with p.π1.
  clearbody p.
  clear u v u' Γ r.
  pattern p.
  apply (@Fix_F 
    (∑ (u v _ : term) (Γ : context), red1 Σ Γ u v)
    (precompose lt ((fun p => (red1_depth p.π2.π2.π2.π2 + size_lambda p.π1 + size_lambda p.π2.π2.π1))))).
  2: by apply wf_precompose, lt_wf.
  intros (u&v&u'&Γ&r) IH Rle he' tRle hle' hR e ; cbn in *.
  revert IH ; dependent inversion r ; subst ; intros IH.
  12:{
    eapply structural_red1_eq_term ; tea.
    1: cbn ; congruence.
    intros u'' Δ e'.
    dependent inversion e' ; cbn ; try solve [congruence] ; subst.
    intros _.
    unshelve edestruct IH.
    1:{
      exists (lift0 #|Δ| b), (lift0 #|Δ| r0), t', (Γ ,,, Δ).
      apply weakening_red1_0 ; auto.
      admit. (*well-scopedness?*) }
    all: tea.
    + exists (lift0 #|b)
    edestruct IHr as (r'&?&?).
    2:{
      exists (tLetIn na' x ty' u'0).
      split.
      - apply red_letin ; auto. 