(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith CMorphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.EGCIC Require Import EGCICAst EGCICAstUtils EGCICInduction EGCICReflect EGCICLiftSubst EGCICEquality.

Require Import ssreflect.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.


Local Open Scope type_scope.

(** ** Syntactic equality up-to universes
  We don't look at printing annotations *)

Inductive syn_cons_term_upto_univ (Re Rle : Universe.t -> Universe.t -> Prop) : term -> term -> Type :=
| syn_cons_Rel n  :
    syn_cons_term_upto_univ Re Rle (eRel n) (eRel n)

| syn_cons_Evar e args args' :
    All2 (syn_cons_term_upto_univ Re Re) args args' ->
    syn_cons_term_upto_univ Re Rle (eEvar e args) (eEvar e args')

| syn_cons_Var id :
    syn_cons_term_upto_univ Re Rle (eVar id) (eVar id)

| syn_cons_Sort s s' :
    Rle s s' ->
    syn_cons_term_upto_univ Re Rle (eSort s) (eSort s')

| syn_cons_App t t' u u' :
    syn_cons_term_upto_univ Re Rle t t' ->
    syn_cons_term_upto_univ Re Re u u' ->
    syn_cons_term_upto_univ Re Rle (eApp t u) (eApp t' u')

| syn_cons_Const c u u' :
    R_universe_instance Re u u' ->
    syn_cons_term_upto_univ Re Rle (eConst c u) (eConst c u')

| syn_cons_Ind i u u' :
    R_universe_instance Re u u' ->
    syn_cons_term_upto_univ Re Rle (eInd i u) (eInd i u')

| syn_cons_Construct i k u u' :
    R_universe_instance Re u u' ->
    syn_cons_term_upto_univ Re Rle (eConstruct i k u) (eConstruct i k u')

| syn_cons_Lambda na na' ty ty' t t' :
    syn_cons_term_upto_univ Re Re ty ty' ->
    syn_cons_term_upto_univ Re Rle t t' ->
    syn_cons_term_upto_univ Re Rle (eLambda na ty t) (eLambda na' ty' t')

| syn_cons_Prod na na' a a' b b' :
    syn_cons_term_upto_univ Re Re a a' ->
    syn_cons_term_upto_univ Re Rle b b' ->
    syn_cons_term_upto_univ Re Rle (eProd na a b) (eProd na' a' b')

| syn_cons_LetIn na na' t t' ty ty' u u' :
    syn_cons_term_upto_univ Re Re t t' ->
    syn_cons_term_upto_univ Re Re ty ty' ->
    syn_cons_term_upto_univ Re Rle u u' ->
    syn_cons_term_upto_univ Re Rle (eLetIn na t ty u) (eLetIn na' t' ty' u')

| syn_cons_Case indn p p' c c' brs brs' :
    syn_cons_term_upto_univ Re Re p p' ->
    syn_cons_term_upto_univ Re Re c c' ->
    All2 (fun x y =>
      (fst x = fst y) *
      syn_cons_term_upto_univ Re Re (snd x) (snd y)
    ) brs brs' ->
    syn_cons_term_upto_univ Re Rle (eCase indn p c brs) (eCase indn p' c' brs')

| syn_cons_Proj p c c' :
    syn_cons_term_upto_univ Re Re c c' ->
    syn_cons_term_upto_univ Re Rle (eProj p c) (eProj p c')

| syn_cons_Fix mfix mfix' idx :
    All2 (fun x y =>
      syn_cons_term_upto_univ Re Re x.(dtype) y.(dtype) *
      syn_cons_term_upto_univ Re Re x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg))
    ) mfix mfix' ->
    syn_cons_term_upto_univ Re Rle (eFix mfix idx) (eFix mfix' idx)

| syn_cons_CoFix mfix mfix' idx :
    All2 (fun x y =>
      syn_cons_term_upto_univ Re Re x.(dtype) y.(dtype) *
      syn_cons_term_upto_univ Re Re x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg))
    ) mfix mfix' ->
    syn_cons_term_upto_univ Re Rle (eCoFix mfix idx) (eCoFix mfix' idx)

| syn_cons_rai A A' :
    syn_cons_term_upto_univ Re Rle (eErr rai A) (eErr rai A')

| syn_cons_ukn_l t A :
    syn_cons_term_upto_univ Re Rle t (eErr ukn A)

| syn_cons_ukn_r t A :
    syn_cons_term_upto_univ Re Rle (eErr ukn A) t

| syn_cons_Cast A A' B B' t t' :
    syn_cons_term_upto_univ Re Rle A A' ->
    syn_cons_term_upto_univ Re Re B B' ->
    syn_cons_term_upto_univ Re Re t t' ->
    syn_cons_term_upto_univ Re Rle (eCast A B t) (eCast A' B' t').
(* ** Syntactic conversion up-to universes *)

Definition syn_cons_term `{checker_flags} φ :=
  syn_cons_term_upto_univ (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Instance syn_cons_term_upto_univ_refl Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (syn_cons_term_upto_univ Re Rle).
Proof.
  intros hRe hRle t.
  induction t in Rle, hRle |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor. all: eauto.
  all: try solve [eapply All_All2 ; eauto].
  all: try solve [eapply Forall2_same ; eauto].
  - eapply All_All2; eauto. simpl. intuition eauto.
  - eapply All_All2; eauto. simpl. intuition eauto.
  - destruct e ; econstructor ; eauto.
Qed.

Instance syn_cons_term_refl `{checker_flags} φ : Reflexive (syn_cons_term φ).
Proof.
  apply syn_cons_term_upto_univ_refl. all: exact _.
Qed.

Derive Signature for syn_cons_term_upto_univ.

Instance syn_cons_term_upto_univ_sym Re Rle :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (syn_cons_term_upto_univ Re Rle).
Proof.
  intros he hle u v e.
  induction u in Rle, hle, v, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto ;
    try eapply Forall2_symP ; eauto
  ].
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 h2]. eapply h1 in h2 ; auto.
  - econstructor; eauto.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 [h2 h3]]. eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]].
      eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]]. eapply h1 in h3 ; auto.
Qed.

Instance syn_cons_term_sym `{checker_flags} φ : Symmetric (syn_cons_term φ).
Proof.
  eapply syn_cons_term_upto_univ_sym. all: exact _.
Qed.

Instance eq_term_upto_univ_impl Re Re' Rle Rle' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (eq_term_upto_univ Re Rle) (eq_term_upto_univ Re' Rle').
Proof.
  intros he hle t t'.
  induction t in t', Rle, Rle', hle |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor; eauto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x ? y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
Qed.

Local Ltac lih :=
  lazymatch goal with
  | ih : forall Rle v n k, syn_cons_term_upto_univ _ _ ?u _ -> _
    |- syn_cons_term_upto_univ _ _ (lift _ _ ?u) _ =>
    eapply ih
  end.

Lemma syn_cons_term_upto_univ_lift Re Rle n k :
  Proper (syn_cons_term_upto_univ Re Rle ==> syn_cons_term_upto_univ Re Rle) (lift n k).
Proof.
  intros u v e.
  induction u in v, n, k, e, Rle |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try (cbn ; constructor ; try lih ; assumption).
  all: try (simpl ; econstructor ; eauto).
  - solve_all.
  - solve_all.
  - pose proof (All2_length _ _ a).
    solve_all. rewrite H. eauto.
  - pose proof (All2_length _ _ a).
    solve_all. rewrite H. eauto.
Qed.

Lemma lift_syn_cons_term {cf:checker_flags} φ n k T U :
  syn_cons_term φ T U -> syn_cons_term φ (lift n k T) (lift n k U).
Proof.
  apply syn_cons_term_upto_univ_lift.
Qed.

Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> syn_cons_term_upto_univ _ _ ?u _ -> _ -> _
    |- syn_cons_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
  end.

Lemma syn_cons_term_upto_univ_substs Re :
  forall u v n l l',
    syn_cons_term_upto_univ Re Re u v ->
    All2 (syn_cons_term_upto_univ Re Re) l l' ->
    syn_cons_term_upto_univ Re Re (subst l n u) (subst l' n v).
Proof.
  intros u v n l l' hu hl.
  induction u in v, n, l, l', hu, hl, Re |- * using term_forall_list_ind.
  all: dependent destruction hu.
  all: try solve [ cbn ; constructor ; try sih ; eauto ].
  all: try solve [ econstructor ; eauto].
  - cbn. destruct (Nat.leb_spec0 n n0).
    + case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply syn_cons_term_upto_univ_lift.
        eauto.
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn. constructor ; try sih ; eauto. solve_all.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length _ _ a).
    solve_all. now rewrite H.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length _ _ a).
    solve_all. now rewrite H.
Qed.

Lemma syn_cons_term_upto_univ_subst Re :
  forall u v n x y,
    syn_cons_term_upto_univ Re Re u v ->
    syn_cons_term_upto_univ Re Re x y ->
    syn_cons_term_upto_univ Re Re (u{n := x}) (v{n := y}).
Proof.
  intros u v n x y e1 e2.
  eapply syn_cons_term_upto_univ_substs; eauto.
Qed.

Lemma subst_syn_cons_term {cf:checker_flags} φ l k T U :
  syn_cons_term φ T U ->
  syn_cons_term φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply syn_cons_term_upto_univ_substs; try easy.
  now eapply All2_same.
Qed.

(** ** Boolean version **  *)

Fixpoint syn_consb_term_upto_univ (equ lequ : Universe.t -> Universe.t -> bool) (u v : term) : bool :=
  match u, v with
  | eRel n, eRel m =>
    eqb n m

  | eEvar e args, eEvar e' args' =>
    eqb e e' &&
    forallb2 (syn_consb_term_upto_univ equ equ) args args'

  | eVar id, eVar id' =>
    eqb id id'

  | eSort u, eSort u' =>
    lequ u u'

  | eApp u v, eApp u' v' =>
    syn_consb_term_upto_univ equ lequ u u' &&
    syn_consb_term_upto_univ equ equ v v'

  | eConst c u, eConst c' u' =>
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | eInd i u, eInd i' u' =>
    eqb i i' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | eConstruct i k u, eConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | eLambda na A t, eLambda na' A' t' =>
    syn_consb_term_upto_univ equ equ A A' &&
    syn_consb_term_upto_univ equ lequ t t'

  | eProd na A B, eProd na' A' B' =>
    syn_consb_term_upto_univ equ equ A A' &&
    syn_consb_term_upto_univ equ lequ B B'

  | eLetIn na B b u, eLetIn na' B' b' u' =>
    syn_consb_term_upto_univ equ equ B B' &&
    syn_consb_term_upto_univ equ equ b b' &&
    syn_consb_term_upto_univ equ lequ u u'

  | eCase indp p c brs, eCase indp' p' c' brs' =>
    eqb indp indp' &&
    syn_consb_term_upto_univ equ equ p p' &&
    syn_consb_term_upto_univ equ equ c c' &&
    forallb2 (fun x y =>
      eqb (fst x) (fst y) &&
      syn_consb_term_upto_univ equ equ (snd x) (snd y)
    ) brs brs'

  | eProj p c, eProj p' c' =>
    eqb p p' &&
    syn_consb_term_upto_univ equ equ c c'

  | eFix mfix idx, eFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      syn_consb_term_upto_univ equ equ x.(dtype) y.(dtype) &&
      syn_consb_term_upto_univ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | eCoFix mfix idx, eCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      syn_consb_term_upto_univ equ equ x.(dtype) y.(dtype) &&
      syn_consb_term_upto_univ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | eErr rai A, eErr rai A' =>
    true
  
  | eErr ukn _, _ => true

  | _, eErr ukn _ => true

  | eCast A B t, eCast A' B' t' =>
    syn_consb_term_upto_univ equ lequ A A' &&
    syn_consb_term_upto_univ equ equ B B'  &&
    syn_consb_term_upto_univ equ equ t t'

  | _, _ => false

  end.

Ltac eqspec :=
  lazymatch goal with
  | |- context [ eqb ?u ?v ] =>
    destruct (eqb_spec u v) ; nodec ; subst
  end.

Ltac eqspecs :=
  repeat eqspec.

Local Ltac equspec equ h :=
  repeat lazymatch goal with
  | |- context [ equ ?x ?y ] =>
    destruct (h x y) ; nodec ; subst
  end.

Local Ltac ih :=
  repeat lazymatch goal with
  | ih : forall lequ Rle hle t', reflectT (syn_cons_term_upto_univ _ _ ?t _) _,
    hle : forall u u', reflectT (?Rle u u') (?lequ u u')
    |- context [ syn_consb_term_upto_univ _ ?lequ ?t ?t' ] =>
    destruct (ih lequ Rle hle t') ; nodec ; subst
  end.

Lemma syn_consb_term_upto_univ_impl (equ lequ : _ -> _ -> bool) Re Rle :
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  subrelation (syn_consb_term_upto_univ equ lequ) (syn_cons_term_upto_univ Re Rle).
Proof.
  intros he hle t t'.
  induction t in t', lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t'; try discriminate 1. all: cbn -[eqb].
  all: try solve [destruct e ; intros H ; [constructor|discriminate]].
  - eqspec; [intros _|discriminate]. constructor.
  - eqspec; [intros _|discriminate]. constructor.
  - eqspec; [|discriminate]. constructor.
    cbn in H. apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    eapply All_impl; tea. eauto.
  - constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    apply forallb2_Forall2 in H0.
    eapply Forall2_impl; tea; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    apply forallb2_Forall2 in H0.
    eapply Forall2_impl; tea; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    apply forallb2_Forall2 in H0.
    eapply Forall2_impl; tea; eauto.
  - eqspec; [|discriminate]. intro. rtoProp.
    destruct indn. econstructor; eauto.
    apply forallb2_All2 in H0.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|discriminate].
    intro. split; eauto.
  - eqspec; [|discriminate]. intro. constructor; eauto.
  - eqspec; [|discriminate].
    econstructor; eauto.
    cbn -[eqb] in H; apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|rewrite andb_false_r; discriminate].
    intro. rtoProp. split; tas. split; eapply X0; tea.
  - eqspec; [|discriminate].
    econstructor; eauto.
    cbn -[eqb] in H; apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|rewrite andb_false_r; discriminate].
    intro. rtoProp. split; tas. split; eapply X0; tea.
  - destruct e ; destruct e0 ; intros ; try constructor.
  - intro. rtoProp. constructor; eauto.
Qed.


Lemma reflect_syn_cons_term_upto_univ equ lequ (Re Rle : Universe.t -> Universe.t -> Prop) :
  (forall u u', reflectT (Re u u') (equ u u')) ->
  (forall u u', reflectT (Rle u u') (lequ u u')) ->
  forall t t', reflectT (syn_cons_term_upto_univ Re Rle t t')
                   (syn_consb_term_upto_univ equ lequ t t').
Proof.
  intros he hle t t'.
  induction t in t', lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t' ; nodec.
  all: try solve [destruct e ; cbn ; constructor ; [constructor|] ; intro H ; inversion H].
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn.
    induction X in l0 |- *.
    + destruct l0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. inversion X.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn. destruct (p _ _ he t).
        -- destruct (IHX l0).
           ++ constructor. constructor. constructor ; try assumption.
              inversion s0. subst. assumption.
           ++ constructor. intro bot. inversion bot. subst.
              inversion X0. subst.
              apply f. constructor. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb].
    pose proof (eqb_spec s k) as H.
    match goal with
    | |- context G[ eqb ?x ?y ] =>
      set (toto := eqb x y) in * ;
      let G' := context G[toto] in
      change G'
    end.
    destruct H ; nodec. subst.
    equspec equ he. equspec lequ hle. ih.
    cbn. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion s. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion s. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion s. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb].
    destruct indn as [i n].
    induction l in brs, X |- *.
    + destruct brs.
      * constructor. constructor ; try assumption.
        constructor.
      * constructor. intro bot. inversion bot. subst. inversion X2.
    + destruct brs.
      * constructor. intro bot. inversion bot. subst. inversion X2.
      * cbn - [eqb]. inversion X. subst.
        destruct a, p. cbn - [eqb]. eqspecs.
        -- cbn - [eqb]. pose proof (X0 equ Re he t0) as hh. cbn in hh.
           destruct hh.
           ++ cbn - [eqb].
              destruct (IHl X1 brs).
              ** constructor. constructor ; try assumption.
                 constructor ; try easy.
                 inversion s2. subst. assumption.
              ** constructor. intro bot. apply f. inversion bot. subst.
                 constructor ; try assumption.
                 inversion X4. subst. assumption.
           ++ constructor. intro bot. apply f. inversion bot. subst.
              inversion X4. subst. destruct X5. assumption.
        -- constructor. intro bot. inversion bot. subst.
           inversion X4. subst. destruct X5. cbn in s1. subst.
           apply n2. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb]. inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re he (dtype d)).
        -- destruct (h2 equ Re he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- constructor. constructor. constructor ; try easy.
                     inversion s1. assumption.
                 --- constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb]. inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re he (dtype d)).
        -- destruct (h2 equ Re he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- constructor. constructor. constructor ; try easy.
                     inversion s1. assumption.
                 --- constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
  - cbn - [eqb].
    destruct e ; destruct e0.
    all: equspec equ he ; constructor ; constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. ih.
  constructor. constructor ; assumption.
Qed.

Lemma syn_consb_term_upto_univ_refl :
  forall (eqb leqb : Universe.t -> Universe.t -> bool) t,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    syn_consb_term_upto_univ eqb leqb t t.
Proof.
  intros eqb leqb t eqb_refl leqb_refl.
  induction t using term_forall_list_ind in leqb, leqb_refl |- *.
  all: simpl.
  all: rewrite -> ?Nat.eqb_refl, ?eq_string_refl, ?eq_kername_refl, ?eq_inductive_refl, ?eq_errtype_refl, ?eqb_refl.
  all: repeat rewrite -> eq_prod_refl
        by (eauto using eq_prod_refl, Nat.eqb_refl, eq_string_refl, eq_inductive_refl).
  all: repeat lazymatch goal with
      | ih : forall leqb, _ -> @?P leqb |- _ =>
        rewrite -> ih by assumption ; clear ih
      end.
  all: simpl.
  all: try solve [ eauto ].
  - induction X.
    + reflexivity.
    + simpl. rewrite -> p by assumption. auto.
  - eapply forallb2_map. eapply forallb2_refl.
    intro l. eapply eqb_refl.
  - eapply forallb2_map. eapply forallb2_refl.
    intro l. eapply eqb_refl.
  - eapply forallb2_map. eapply forallb2_refl.
    intro l. eapply eqb_refl.
  - induction X.
    + reflexivity.
    + simpl. rewrite Nat.eqb_refl. rewrite -> p0 by assumption.
      assumption.
  - induction X.
    + reflexivity.
    + simpl. rewrite Nat.eqb_refl.
      destruct p as [e1 e2].
      rewrite -> e1 by assumption. rewrite -> e2 by assumption.
      assumption.
  - induction X.
    + reflexivity.
    + simpl. rewrite -> Nat.eqb_refl.
      destruct p as [e1 e2].
      rewrite -> e1 by assumption. rewrite -> e2 by assumption.
      assumption.
  - by destruct e. 
Qed.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma syn_cons_term_upto_univ_mkApps Re Rle u1 l1 u2 l2 :
    syn_cons_term_upto_univ Re Rle u1 u2 ->
    All2 (syn_cons_term_upto_univ Re Re) l1 l2 ->
    syn_cons_term_upto_univ Re Rle (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

Lemma syn_cons_term_upto_univ_it_mkLambda_or_LetIn Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (syn_cons_term_upto_univ Re Rle) (syn_cons_term_upto_univ Re Rle)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply syn_cons_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply syn_cons_term_upto_univ_refl.
    all: auto.
Qed.

Lemma syn_cons_term_it_mkLambda_or_LetIn {cf:checker_flags} φ Γ :
  respectful (syn_cons_term φ) (syn_cons_term φ)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  apply syn_cons_term_upto_univ_it_mkLambda_or_LetIn; exact _.
Qed.

Lemma syn_cons_term_upto_univ_it_mkProd_or_LetIn Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (syn_cons_term_upto_univ Re Rle) (syn_cons_term_upto_univ Re Rle)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply syn_cons_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply syn_cons_term_upto_univ_refl.
    all: auto.
Qed.

Lemma syn_cons_term_it_mkProd_or_LetIn {cf:checker_flags} φ Γ:
  respectful (syn_cons_term φ) (syn_cons_term φ)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  eapply syn_cons_term_upto_univ_it_mkProd_or_LetIn ; exact _.
Qed.

Lemma syn_cons_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} φ Γ u v :
    syn_cons_term φ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
    syn_cons_term φ u v.
Proof.
  revert u v. induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.

(** Syntactical equality of terms implies syntactical consistency*)

Lemma upto_names_impl Re Rle :
  subrelation (eq_term_upto_univ Re Rle) (syn_cons_term_upto_univ Re Rle).
Proof.
  intros t t'.
  induction t in Re, Rle, t' |- * using term_forall_list_ind.
  all: intro H ; inversion H.
  all: try solve [subst ; econstructor ; eauto].
  - constructor.
    clear -X0 X.
    induction X0.
    + constructor.
    + inversion_clear X.
      constructor ; auto. 
  - constructor ; auto.
    subst.
    induction X2.
    + constructor.
    + constructor ; inversion_clear X ; intuition.
      apply X.
      constructor ; assumption.
  - constructor ; auto.
    subst.
    induction X0.
    + constructor.
    + constructor ; inversion_clear X ; intuition.
      apply X.
      constructor ; assumption.
  - constructor ; auto.
    subst.
    induction X0.
    + constructor.
    + constructor ; inversion_clear X ; intuition.
      apply X.
      constructor ; assumption.
  - destruct e ; constructor.
Qed.


(** ** Equality on contexts ** *)
(* 
Inductive eq_context_upto (Re : Universe.t -> Universe.t -> Prop) : context -> context -> Type :=
| eq_context_nil : eq_context_upto Re [] []
| eq_context_vass na A Γ nb B Δ :
    eq_term_upto_univ Re Re A B ->
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (Γ ,, vass na A) (Δ ,, vass nb B)
| eq_context_vdef na u A Γ nb v B Δ :
    eq_term_upto_univ Re Re u v ->
    eq_term_upto_univ Re Re A B ->
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (Γ ,, vdef na u A) (Δ ,, vdef nb v B).

Definition eq_def_upto Re d d' : Type :=
  (eq_term_upto_univ Re Re d.(dtype) d'.(dtype)) *
  (eq_term_upto_univ Re Re d.(dbody) d'.(dbody)) *
  (d.(rarg) = d'.(rarg)).

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Definition eq_decl_upto Re d d' : Type :=
  rel_option (eq_term_upto_univ Re Re) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Re Re d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto Re :
  subrelation (All2 (eq_decl_upto Re)) (eq_context_upto Re).
Proof.
  intros Γ Δ h.
  induction h.
  - constructor.
  - destruct r as [h1 h2].
    destruct x as [na bo ty], y as [na' bo' ty'].
    simpl in h1, h2.
    destruct h1.
    + constructor ; eauto.
    + constructor ; eauto.
Qed.

Lemma eq_context_upto_refl Re :
  RelationClasses.Reflexive Re ->
  Reflexive (eq_context_upto Re).
Proof.
  intros hRe Γ.
  induction Γ as [| [na [bo |] ty] Γ ih].
  - constructor.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
Qed.

Lemma eq_context_upto_sym Re :
  RelationClasses.Symmetric Re ->
  Symmetric (eq_context_upto Re).
Proof.
  intros hRe Γ Δ.
  induction 1; constructor; eauto using eq_term_upto_univ_sym.
  all:eapply eq_term_upto_univ_sym; auto.
Qed.

Lemma eq_context_upto_cat Re Γ Δ Γ' Δ' :
  eq_context_upto Re Γ Γ' ->
  eq_context_upto Re Δ Δ' ->
  eq_context_upto Re (Γ ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros h1 h2. induction h2 in Γ, Γ', h1 |- *.
  - assumption.
  - simpl. constructor ; eauto.
  - simpl. constructor ; eauto.
Qed.

Lemma eq_context_upto_rev Re Γ Δ :
  eq_context_upto Re Γ Δ ->
  eq_context_upto Re (rev Γ) (rev Δ).
Proof.
  induction 1.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
Qed.

Lemma eq_context_upto_rev' :
  forall Γ Δ Re,
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (List.rev Γ) (List.rev Δ).
Proof.
  intros Γ Δ Re h.
  induction h.
  - constructor.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor. assumption.
    + assumption.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_context_impl :
  forall Re Re',
    RelationClasses.subrelation Re Re' ->
    subrelation (eq_context_upto Re) (eq_context_upto Re').
Proof.
  intros Re Re' hR Γ Δ h.
  induction h.
  - constructor.
  - constructor. 2: assumption.
    eapply eq_term_upto_univ_impl. all: eassumption.
  - constructor. 3: assumption.
    all: eapply eq_term_upto_univ_impl. all: eassumption.
Qed.

Lemma eq_context_upto_length :
  forall Re Γ Δ,
    eq_context_upto Re Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Re Γ Δ h.
  induction h. all: simpl ; auto.
Qed.

Section ContextUpTo.

  Context (Re : Universe.t -> Universe.t -> Prop).
  Context (ReR : RelationClasses.Reflexive Re).
  Context (ReS : RelationClasses.Symmetric Re).
  Context (ReT : RelationClasses.Transitive Re).

  Notation eq_ctx := (eq_context_upto Re).

  Global Instance eq_ctx_refl : Reflexive eq_ctx.
  Proof. now intros ?; apply eq_context_upto_refl. Qed.

  Global Instance eq_ctx_sym : Symmetric eq_ctx.
  Proof.
    intros x y. now apply eq_context_upto_sym.
  Qed.

  Global Instance eq_ctx_trans : Transitive eq_ctx.
  Proof.
    intros Γ0 Γ1 Γ2 H. induction H in Γ2 |- *.
    - intros H2; inversion H2; subst; constructor; auto.
    - intros H2; inversion H2; subst; constructor; auto.
      etransitivity; eauto.
    - intros H2; inversion H2; subst; constructor; auto.
      all: etransitivity; eauto.
  Qed.

End ContextUpTo.


(* todo: unify *)
Definition eq_opt_term `{checker_flags} φ (t u : option term) :=
  match t, u with
  | Some t, Some u => eq_term φ t u
  | None, None => True
  | _, _ => False
  end.

Definition eq_decl `{checker_flags} φ (d d' : context_decl) :=
  eq_opt_term φ d.(decl_body) d'.(decl_body) * eq_term φ d.(decl_type) d'.(decl_type).

Definition eq_context `{checker_flags} φ (Γ Δ : context) :=
  All2 (eq_decl φ) Γ Δ.


Lemma lift_eq_decl `{checker_flags} ϕ n k d d' :
  eq_decl ϕ d d' -> eq_decl ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  destruct d, d', decl_body, decl_body0;
    unfold eq_decl, map_decl; cbn; intuition auto using lift_eq_term.
Qed.

Lemma lift_eq_context `{checker_flags} φ l l' n k :
  eq_context φ l l' ->
  eq_context φ (lift_context n k l) (lift_context n k l').
Proof.
  induction l in l', n, k |- *; intros; destruct l'; rewrite -> ?lift_context_snoc0.
  constructor.
  all: inversion X; subst. constructor.
  - apply All2_length in X1. rewrite X1.
    now apply lift_eq_decl.
  - now apply IHl.
Qed.

Lemma eq_term_upto_univ_mkApps_inv Re u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  eq_term_upto_univ Re Re (mkApps u l) (mkApps u' l') ->
  eq_term_upto_univ Re Re u u' * All2 (eq_term_upto_univ Re Re) l l'.
Proof.
  intros hu hu' h.
  apply eq_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.

Lemma isLambda_eq_term_l Re u v :
    isLambda u ->
    eq_term_upto_univ Re Re u v ->
    isLambda v.
Proof.
  intros h e.
  destruct u; try discriminate.
  depelim e. auto.
Qed.

Lemma isLambda_eq_term_r Re u v :
    isLambda v ->
    eq_term_upto_univ Re Re u v ->
    isLambda u.
Proof.
  intros h e.
  destruct v ; try discriminate.
  depelim e. auto.
Qed.

Lemma isConstruct_app_eq_term_l Re u v :
    isConstruct_app u ->
    eq_term_upto_univ Re Re u v ->
    isConstruct_app v.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e1 in h. cbn in h.
  rewrite e2. cbn.
  destruct t1 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_eq_term_r :
  forall Re u v,
    isConstruct_app v ->
    eq_term_upto_univ Re Re u v ->
    isConstruct_app u.
Proof.
  intros Re u v h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.

(* TODO MOVE *)
Instance subrelation_same :
  forall A (R : A -> A -> Prop),
    RelationClasses.subrelation R R.
Proof.
  intros A R x y h. assumption.
Qed.

Lemma eq_term_upto_univ_flip (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  eq_term_upto_univ Re Rle u v ->
  eq_term_upto_univ Re Rle' v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl' H.
  assert (Resub : RelationClasses.subrelation Re Re).
  { typeclasses eauto. }
  revert Rerefl Rlerefl Resym Retrans Rletrans incl incl' Resub.
  revert Re Rle u v H Rle'.
  induction 1; intros; constructor; intuition auto.
  - eapply All2_symP; auto. eapply eq_term_upto_univ_sym; auto.
  - eapply Forall2_sym. eapply Forall2_map_inv in r.
    eapply Forall2_map. solve_all.
  - eapply Forall2_sym. eapply Forall2_map_inv in r.
    eapply Forall2_map. solve_all.
  - eapply Forall2_sym. eapply Forall2_map_inv in r.
    eapply Forall2_map. solve_all.
  - eapply All2_sym. solve_all.
    simpl in *. subst. now eapply eq_term_upto_univ_sym.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
Qed.

Lemma eq_univ_make :
  forall u u',
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros u u' H. eapply Forall2_map' in H.
  eapply Forall2_eq. eapply Forall2_impl; tea.
  clear. intros [] [] H; now inversion H.
Qed. *)