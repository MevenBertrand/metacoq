Require Import String.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICEquality PCUICTyping PCUICBasicStrengthening
     PCUICReduction PCUICPosition PCUICInduction PCUICWeakening.

Local Open Scope string_scope.

Require Import ssrbool List CRelationClasses Arith Lia.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.

Import ListNotations. Open Scope list_scope.

Set Default Goal Selector "!".

Existing Instance All2_trans.

Instance All2_refl {A} R :
  @Reflexive A R -> Reflexive (All2 R).
Proof.
  intros H l. induction l; constructor; auto.
Qed.

(** ** η-confluence ** **)


Lemma eta1_local_confluence t u1 u2 :
  eta1 t u1 -> eta1 t u2 ->
  ∑ v, eta u1 v × eta u2 v.
Proof.
  induction 1 in u2 |- * using eta1_ind_all.
  - intro XX; invs XX. 3: invs X.
    + apply lift_inj in H2; subst. exists t; now split.
    + exists t; eta.
    + apply eta1_strengthening in X0 as [t' [? ?]]; subst. 
      exists t'; eta.
    + invs X0.
  - intro XX; invs XX.
    + exists u2; eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLambda na v N); eta.
    + exists (tLambda na M' M'0); eta.
  - intros XX; invs XX.
    + invs X; [|invs X0].
      apply eta1_strengthening in X0 as [v [? ?]]; subst.
      exists v; eta.
    + exists (tLambda na M'0 M'); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLambda na N v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tLetIn na v t b'); eta.
    + exists (tLetIn na r r0 b'); eta.
    + exists (tLetIn na r t r0); eta.
  - intro XX; invs XX.
    + exists (tLetIn na r0 r b'); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLetIn na b v b'); eta.
    + exists (tLetIn na b r r0); eta.
  - intro XX; invs XX.
    + exists (tLetIn na r0 t r); eta.
    + exists (tLetIn na b r0 r); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLetIn na b t v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tCase ind v c brs); eta.
    + exists (tCase ind p' c' brs); eta.
    + exists (tCase ind p' c brs'); eta.
  - intro XX; invs XX.
    + exists (tCase ind p' c' brs); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tCase ind p v brs); eta.
    + exists (tCase ind p c' brs'); eta.
  - intro XX; invs XX.
    + exists (tCase ind p' c brs'); eta.
    + exists (tCase ind p c' brs'); eta.
    + enough (∑ v', All2 (on_Trel_eq eta snd fst) brs' v'
                    × All2 (on_Trel_eq eta snd fst) brs'0 v') as XX. {
        destruct XX as [v' [H1 H2]]. exists (tCase ind p c v'); eta. }
      induction X in brs'0, X0 |- *; invs X0.
      * destruct hd, hd', hd'0, p0 as [[] ?], X; cbn in *; subst.
        apply s in e1 as [v' [H1 H2]].
        exists ((n1, v') :: tl); split; constructor; cbn; eta; apply All2_refl; eta.
      * destruct hd, hd', p0 as [[] ?]; cbn in *; subst.
        exists ((n0, t0) :: tl'); split; constructor; cbn; eta.
      * destruct hd, hd', X1 as []; cbn in *; subst.
        exists ((n0, t0) :: tl'); split; constructor; cbn; eta.
      * eapply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; cbn; eta.
  - intro XX; invs XX.
    apply IHX in X0 as [v [? ?]].
    exists (tProj p v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tApp v M2); eta.
    + exists (tApp N1 N2); eta.
  - intro XX; invs XX.
    + exists (tApp N1 N2); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tApp M1 v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tProd na v M2); eta.
    + exists (tProd na N1 N2); eta.
  - intro XX; invs XX.
    + exists (tProd na N1 N2); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tProd na M1 v); eta.
  - intro XX; invs XX.
    enough (∑ l'', All2 eta l' l'' × All2 eta l'0 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tEvar ev v); eta. }
    induction X in l'0, X0 |- *; invs X0.
    + destruct p as [? p]. apply p in X as [v' [H1 H2]].
      exists (v' :: tl); split; constructor; tas; now apply All2_refl.
    + destruct p. exists (hd' :: tl'); split; constructor; trea.
      -- eapply OnOne2_All2; trea. eta.
      -- eta.
    + assert (OnOne2 eta1 tl tl') as XX. {
        eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
      specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
      exists (hd' :: v'); split; constructor; trea.
      -- eta.
      -- etransitivity; tea. eapply OnOne2_All2; trea; eta.
    + apply IHX in X1 as [v' [H1 H2]].
      exists (hd :: v'); split; constructor; trea.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 v' dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dtype x) (dtype y)
         × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype0 dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype1 dbody0 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 dtype1 v' rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dbody x) (dbody y)
         × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 v' dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dtype x) (dtype y)
         × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype0 dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype1 dbody0 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 dtype1 v' rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dbody x) (dbody y)
         × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
Qed.




(** ** βη-reduction ** **)

(* Lemma app_mkApps u v t l : *)
(*   isApp t = false -> tApp u v = mkApps t l -> *){
(*   ∑ l', (l = l' ++ [v])%list × u = mkApps t l'. *)
(* Proof. *)
(*   intros h e. induction l in u, v, t, e, h |- * using list_rect_rev. *)
(*   - cbn in e. subst. cbn in h. discriminate. *)
(*   - rewrite <- mkApps_nested in e. cbn in e. *)
(*     exists l. inversion e. subst. auto. *)
(* Qed. *)

Lemma not_isLambda_mkApps u l :
  ~~ isLambda u -> ~~ isLambda (mkApps u l).
Proof.
  induction l in u |- *; cbn; auto.
Qed.

Lemma Lambda_mkApps_not_isLambda na A t u l :
  ~~ isLambda u -> tLambda na A t <> mkApps u l.
Proof.
  intros H e. eapply not_isLambda_mkApps in H.
  rewrite <- e in H; auto.
Qed.

Lemma Lambda_mkApps_Fix na A t mfix idx args :
  tLambda na A t <> mkApps (tFix mfix idx) args.
Proof.
  now apply Lambda_mkApps_not_isLambda.
Qed.

Lemma Lambda_mkApps_CoFix na A t mfix idx args :
  tLambda na A t <> mkApps (tCoFix mfix idx) args.
Proof.
  now apply Lambda_mkApps_not_isLambda.
Qed.

Lemma Rel_mkApps_Fix n mfix idx args :
  tRel n <> mkApps (tFix mfix idx) args.
Proof.
  induction args using rev_ind; cbn.
  - inversion 1.
  - rewrite <- mkApps_nested; cbn. inversion 1.
Qed.

(* Lemma tVar_mkApps_tFix n mfix idx args : *)
(*   tVar n <> mkApps (tFix mfix idx) args. *)
(* Proof. *)
(*   induction args using rev_ind; cbn. *)
(*   - inversion 1. *)
(*   - rewrite <- mkApps_nested; cbn. inversion 1. *)
(* Qed. *)

(* (* TODO MOVE *) *)
(* Fixpoint isFixApp t : bool := *)
(*   match t with *)
(*   | tApp f u => isFixApp f *)
(*   | tFix mfix idx => true *)
(*   | _ => false *)
(*   end. *)

(* (* TODO MOVE *) *)
(* Lemma isFixApp_mkApps : *)
(*   forall t l, *)
(*     isFixApp (mkApps t l) = isFixApp t. *)
(* Proof. *)
(*   intros t l. induction l in t |- *. *)
(*   - cbn. reflexivity. *)
(*   - cbn. rewrite IHl. reflexivity. *)
(* Qed. *)

Hint Constructors red1 : beta.
Hint Resolve red1_red refl_red red_trans : beta.
Hint Resolve red_evar red_prod red_abs red_letin red_app
     red_case_p red_case_c red_proj_c : beta.


Lemma red1_App_Lambda_Rel0 Σ Γ na M N :
  red1 Σ Γ (tApp (tLambda na (lift0 1 M) (lift 1 1 N)) (tRel 0)) N.
Proof.
  refine (_ # red_beta _ _ _ _ _ _).
  apply lift_subst0_Rel.
Defined.
Hint Resolve red1_App_Lambda_Rel0 : beta_eta.

Hint Resolve weakening_eta1 : beta_eta.
Hint Resolve weakening_eta : beta_eta.

Hint Extern 0 (All2 _ _ _) => try reflexivity; OnOne2_All2;
                               intuition auto with beta_eta : beta_eta.
Hint Resolve All2_refl : beta_eta.

Ltac ap_beta_eta := repeat (reflexivity || eapply beta_eta_Evar
                            || eapply beta_eta_Prod || eapply beta_eta_Lambda
                            || eapply beta_eta_LetIn || eapply beta_eta_App
                            || eapply beta_eta_Case || eapply beta_eta_Proj
                            || eapply beta_eta_Fix || eapply beta_eta_CoFix).


(** ** βη-reduction and substitution ** **)
Require Import PCUICSubstitution.

Lemma beta_eta_subst {cf:checker_flags} Σ Γ Δ Γ' s M N :
  wf Σ -> untyped_subslet Γ s Δ ->
  beta_eta Σ (Γ ,,, Δ ,,, Γ') M N ->
  beta_eta Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
Proof.
  intros HΣ Hs Hred.
  induction Hred; [|reflexivity|etransitivity; tea].
  destruct r.
  - eapply red_beta_eta, substitution_untyped_let_red; tea.
  - eapply eta_beta_eta, eta_subst; beta_eta.
Qed.

(* useless for the moment *)
Lemma beta_eta_subst_vass {cf:checker_flags} Σ Γ na A t M N :
  wf Σ -> beta_eta Σ (Γ ,, vass na A) M N ->
  beta_eta Σ Γ (M {0 := t}) (N {0 := t}).
Proof.
  intros. eapply beta_eta_subst with (Γ' := []) (Δ := [_]); tea.
  repeat constructor.
Qed.

Lemma beta_eta_subst0 {cf:checker_flags} Σ Γ Δ s M N :
  wf Σ -> untyped_subslet Γ s Δ ->
  beta_eta Σ (Γ ,,, Δ) M N ->
  beta_eta Σ Γ (subst s 0 M) (subst s 0 N).
Proof.
  apply beta_eta_subst with (Γ' := []).
Qed.

Lemma subst_beta_eta {cf:checker_flags} Σ Γ Γ' s s' b :
  wf Σ -> All2 (beta_eta Σ Γ) s s' ->
  beta_eta Σ (Γ ,,, Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
Proof.
  intros HΣ XX.
  assert (clos_refl_trans (union (All2 (red Σ Γ)) (All2 eta)) s s') as YY. {
    induction XX; [reflexivity|].
    transitivity (y :: l).
    - clear -r. induction r; [|reflexivity|etransitivity; tea].
      constructor.
      destruct r; [left|right]; constructor; trea; beta_eta.
    - clear XX. induction IHXX; [|reflexivity|etransitivity; tea].
      constructor.
      destruct r0; [left|right]; constructor; trea. }
  clear XX. induction YY; [|reflexivity|etransitivity; tea].
  destruct r.
  - apply red_beta_eta. eapply red_red; tea.
  - apply eta_beta_eta. eapply subst_eta, All2_impl; tea; beta_eta.
Qed.


(** ** η-reduction in context ** **)

Require Import PCUICParallelReduction.

Definition eta_ctx : relation context := All2 (on_decls eta).

Instance on_decls_refl R : Reflexive R -> Reflexive (on_decls R).
Proof.
  intros H [? [] ?]; now cbn.
Qed.

Instance on_Trel_eq_refl {A B C} R (f : A -> B) (g : A -> C) :
  Reflexive R -> Reflexive (on_Trel_eq R f g).
Proof.
  now intros H x.
Qed.
  

Lemma red1_eta_ctx Σ Γ Δ t u :
  red1 Σ Γ t u -> eta_ctx Γ Δ ->
  ∑ u', beta_eta Σ Δ t u' × beta_eta Σ Δ u u'.
Proof.
  induction 1 in Δ |- * using red1_ind_all; intro XX.
  all: try (eexists; split; [|reflexivity];
            apply red1_beta_eta; beta_eta; fail).
  - destruct (nth_error Γ i) eqn:e; [|discriminate].
    destruct c as [na [bo|] ty]; [|discriminate].
    cbn in *. invs H.
    eapply All2_nth_error_Some in e; tea.
    destruct e as [d [? ?]].
    destruct d as [na' [bo'|] ty']; [|contradiction]; cbn in *.
    destruct o.
    exists (lift0 (S i) bo'); split; [|beta_eta].
    apply red1_beta_eta. constructor. now rewrite e.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tLambda na xx N); beta_eta.
  - edestruct IHX as [xx [? ?]].
    2: exists (tLambda na N xx); beta_eta.
    now constructor.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tLetIn na xx t b'); beta_eta.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tLetIn na b xx b'); beta_eta.
  - edestruct IHX as [xx [? ?]].
    2: exists (tLetIn na b t xx); beta_eta.
    now constructor.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tCase ind xx c brs); beta_eta.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tCase ind p xx brs); beta_eta.
  - enough (∑ xx, All2 (on_Trel_eq (beta_eta Σ Δ) snd fst) brs xx
                × All2 (on_Trel_eq (beta_eta Σ Δ) snd fst) brs' xx) as Z. {
      destruct  Z as [xx [? ?]].
      eexists (tCase ind p c xx); beta_eta. }
    induction X.
    + rdestruct p0. destruct hd, hd'; cbn in *; subst.
      edestruct p2 as [xx [? ?]]; tea.
      exists ((n0, xx) :: tl); split; constructor; cbn; beta_eta; reflexivity.
    + destruct IHX as [xx [? ?]].
      exists (hd :: xx); split; constructor; beta_eta.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tProj p xx); beta_eta.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tApp xx M2); beta_eta.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tApp M1 xx); beta_eta.
  - edestruct IHX as [xx [? ?]]; tea.
    exists (tProd na xx M2); beta_eta.
  - edestruct IHX as [xx [? ?]]; tea.
    2: exists (tProd na M1 xx); beta_eta.
    now constructor.
  - enough (∑ xx, All2 (beta_eta Σ Δ) l xx
                × All2 (beta_eta Σ Δ) l' xx) as Z. {
      destruct  Z as [xx [? ?]].
      eexists (tEvar ev xx); beta_eta. }
    induction X.
    + rdestruct p.
      edestruct p0 as [xx [? ?]]; tea.
      exists (xx :: tl); split; constructor; cbn; beta_eta; reflexivity.
    + destruct IHX as [xx [? ?]].
      exists (hd :: xx); split; constructor; beta_eta.
  - enough (∑ xx, All2 (fun d0 d1 => beta_eta Σ Δ (dtype d0) (dtype d1)
                                  × dbody d0 = dbody d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix0 xx
                × All2 (fun d0 d1 => beta_eta Σ Δ (dtype d0) (dtype d1)
                                  × dbody d0 = dbody d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix1 xx) as Z. {
      destruct  Z as [xx [? ?]].
      eexists (tFix xx idx); beta_eta. }
    induction X.
    + rdestruct p. destruct hd, hd'; cbn in *; invs p0.
      edestruct p1 as [xx [? ?]]; tea.
      exists ((mkdef _ dname0 xx dbody0 rarg0) :: tl); split; constructor; cbn; beta_eta.
      all: now apply All2_refl.
    + destruct IHX as [xx [? ?]].
      exists (hd :: xx); split; constructor; beta_eta.
  - enough (∑ xx, All2 (fun d0 d1 => beta_eta Σ (Δ ,,, fix_context mfix0)
                                           (dbody d0) (dbody d1)
                                  × dtype d0 = dtype d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix0 xx
                × All2 (fun d0 d1 => beta_eta Σ (Δ ,,, fix_context mfix1)
                                           (dbody d0) (dbody d1)
                                  × dtype d0 = dtype d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix1 xx) as Z. {
      destruct  Z as [xx [? ?]].
      eexists (tFix xx idx); beta_eta. }
    assert (e : fix_context mfix0 = fix_context mfix1). {
       apply (f_equal (@rev _)). unfold mapi.
       generalize 0 at 2 4 as k.
       induction X; intro k; simpl.
       + rdest. congruence.
       + now rewrite IHX. }
    rewrite <- e; clear e.
    set (Γ' := fix_context mfix0) in *; clearbody Γ'.
    induction X.
    + rdestruct p. destruct hd, hd'; cbn in *; invs p0.
      edestruct (p1 (Δ ,,, Γ')) as [xx [? ?]]; tea.
      * now apply All2_app.
      * exists ((mkdef _ dname0 dtype0 xx rarg0) :: tl); split; constructor; cbn; beta_eta.
        all: now apply All2_refl.
    + destruct IHX as [xx [? ?]].
      exists (hd :: xx); split; constructor; beta_eta.
  - enough (∑ xx, All2 (fun d0 d1 => beta_eta Σ Δ (dtype d0) (dtype d1)
                                  × dbody d0 = dbody d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix0 xx
                × All2 (fun d0 d1 => beta_eta Σ Δ (dtype d0) (dtype d1)
                                  × dbody d0 = dbody d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix1 xx) as Z. {
      destruct  Z as [xx [? ?]].
      eexists (tCoFix xx idx); beta_eta. }
    induction X.
    + rdestruct p. destruct hd, hd'; cbn in *; invs p0.
      edestruct p1 as [xx [? ?]]; tea.
      exists ((mkdef _ dname0 xx dbody0 rarg0) :: tl); split; constructor; cbn; beta_eta.
      all: now apply All2_refl.
    + destruct IHX as [xx [? ?]].
      exists (hd :: xx); split; constructor; beta_eta.
  - enough (∑ xx, All2 (fun d0 d1 => beta_eta Σ (Δ ,,, fix_context mfix0)
                                           (dbody d0) (dbody d1)
                                  × dtype d0 = dtype d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix0 xx
                × All2 (fun d0 d1 => beta_eta Σ (Δ ,,, fix_context mfix1)
                                           (dbody d0) (dbody d1)
                                  × dtype d0 = dtype d1 × dname d0 = dname d1
                                  × rarg d0 = rarg d1) mfix1 xx) as Z. {
      destruct  Z as [xx [? ?]].
      eexists (tCoFix xx idx); beta_eta. }
    assert (e : fix_context mfix0 = fix_context mfix1). {
       apply (f_equal (@rev _)). unfold mapi.
       generalize 0 at 2 4 as k.
       induction X; intro k; simpl.
       + rdest. congruence.
       + now rewrite IHX. }
    rewrite <- e; clear e.
    set (Γ' := fix_context mfix0) in *; clearbody Γ'.
    induction X.
    + rdestruct p. destruct hd, hd'; cbn in *; invs p0.
      edestruct (p1 (Δ ,,, Γ')) as [xx [? ?]]; tea.
      * now apply All2_app.
      * exists ((mkdef _ dname0 dtype0 xx rarg0) :: tl); split; constructor; cbn; beta_eta.
        all: now apply All2_refl.
    + destruct IHX as [xx [? ?]].
      exists (hd :: xx); split; constructor; beta_eta.
Qed.



(** ** βη-local confluence up to domains ** **)

Local Ltac pretac t := exists t, t; repeat split; [.. | try reflexivity].
Local Ltac tac t := pretac t; beta_eta.
Local Ltac itac H1 H2 := apply H1 in H2 as [?u' [?v' [? [? ?]]]].

Lemma eta1_mkApps_inv M l N :
  eta1 (mkApps M l) N ->
  (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l').
Proof.
  induction l in M |- *; cbn.
  - left; now exists N.
  - intro H; apply IHl in H as [[M' [? ?]]|[l' [? ?]]]; subst.
    + invs e.
      * left; now exists N1.
      * right; exists (N2 :: l). split; now constructor.
    + right; exists (a :: l'). split; now constructor.
Defined.


Lemma fix_context_app_sing mfix def :
  fix_context (mfix ++ [def])
  = fix_context mfix ,, vass (dname def) (lift0 #|mfix| (dtype def)).
Proof.
  unfold fix_context, mapi.
  change (#|mfix|) with (0 + #|mfix|).  generalize 0 at 2 4 5.
  induction mfix; intro n; cbnr.
  - now rewrite Nat.add_0_r.
  - rewrite IHmfix. cbn. unfold snoc. repeat f_equal. lia.
Qed.

Definition fix_subst_aux (l : mfixpoint term) :=
  fix aux n :=
    match n with
    | 0 => []
    | S n => tFix l n :: aux n
    end.

Lemma fix_subst_fix_subst_aux mfix :
  fix_subst mfix = fix_subst_aux mfix #|mfix|.
Proof.
  reflexivity.
Qed.

Lemma fix_subst_app_sing mfix def :
  fix_subst (mfix ++ [def])
  = fix_subst_aux (mfix ++ [def]) #|mfix| ,, tFix (mfix ++ [def]) #|mfix|.
Proof.
  unfold fix_subst. rewrite app_length; cbn.
  now rewrite Nat.add_comm.
Qed.

Lemma fix_subst_aux_app_sing (mfix0 mfix : mfixpoint term) def :
  fix_subst_aux mfix0 #|mfix ++ [def]|
  = fix_subst_aux mfix0  #|mfix| ,, tFix mfix0 #|mfix|.
Proof.
  unfold fix_subst. rewrite app_length; cbn.
  now rewrite Nat.add_comm.
Qed.

Lemma untyped_subslet_fix_subst Γ mfix :
  untyped_subslet Γ (fix_subst mfix) (fix_context mfix).
Proof.
  rewrite fix_subst_fix_subst_aux.
  generalize mfix at 1 as mfix0.
  induction mfix using MCList.rev_ind; intro mfix0; try now constructor.
  rewrite fix_context_app_sing.
  rewrite fix_subst_aux_app_sing. constructor; eauto.
Qed.


Definition cofix_subst_aux (l : mfixpoint term) :=
  fix aux n :=
    match n with
    | 0 => []
    | S n => tCoFix l n :: aux n
    end.

Lemma cofix_subst_cofix_subst_aux mcofix :
  cofix_subst mcofix = cofix_subst_aux mcofix #|mcofix|.
Proof.
  reflexivity.
Qed.

Lemma cofix_subst_app_sing mcofix def :
  cofix_subst (mcofix ++ [def])
  = cofix_subst_aux (mcofix ++ [def]) #|mcofix| ,, tCoFix (mcofix ++ [def]) #|mcofix|.
Proof.
  unfold cofix_subst. rewrite app_length; cbn.
  now rewrite Nat.add_comm.
Qed.

Lemma cofix_subst_aux_app_sing (mcofix0 mcofix : mfixpoint term) def :
  cofix_subst_aux mcofix0 #|mcofix ++ [def]|
  = cofix_subst_aux mcofix0  #|mcofix| ,, tCoFix mcofix0 #|mcofix|.
Proof.
  unfold cofix_subst. rewrite app_length; cbn.
  now rewrite Nat.add_comm.
Qed.

Lemma untyped_subslet_cofix_subst Γ mcofix :
  untyped_subslet Γ (cofix_subst mcofix) (fix_context mcofix).
Proof.
  rewrite cofix_subst_cofix_subst_aux.
  generalize mcofix at 1 as mcofix0.
  induction mcofix using MCList.rev_ind; intro mcofix0; try now constructor.
  rewrite fix_context_app_sing.
  rewrite cofix_subst_aux_app_sing. constructor; eauto.
Qed.


Lemma fst_decompose_app_App M N :
  (decompose_app (tApp M N)).1 = (decompose_app M).1.
Proof.
  unfold decompose_app; cbn. generalize [N]. generalize (@nil term).
  induction M; cbnr. eauto.
Qed.

Lemma isConstruct_app_App M N :
  isConstruct_app (tApp M N) = isConstruct_app M.
Proof.
  unfold isConstruct_app. now rewrite fst_decompose_app_App.
Qed.

Lemma is_constructor_not_nil narg args :
  is_constructor narg args = true -> args <> [].
Proof.
  intros H e; rewrite e in H. unfold is_constructor in H.
  destruct narg; discriminate.
Qed.

Lemma mkApps_eq_app f l f' a :
  ~~ isApp f ->
  mkApps f l = tApp f' a ->
  l <> nil /\ a = last l a /\ f' = mkApps f (removelast l).
Proof.
  intros.
  apply (f_equal decompose_app) in H0.
  rewrite decompose_app_mkApps in H0; cbn in H0; tas.
  symmetry in H0. apply decompose_app_rec_inv' in H0.
  destruct H0 as [x [_ [H0 H1]]]; subst.
  pose proof (firstn_skipn x l). rewrite <- H0 in H1.
  set (firstn x l) in *. rewrite <- H1. rdest.
  - intro e; apply app_eq_nil in e. destruct e; discriminate.
  - now rewrite last_app.
  - rewrite removelast_app; [| intro; discriminate]. cbn.
    now rewrite app_nil_r.
Qed.




Lemma red1_eta1_diamond {cf:checker_flags} {Σ Γ t u v} :
  wf Σ -> red1 Σ Γ t u -> eta1 t v ->
  ∑ u' v', beta_eta Σ Γ u u' × beta_eta Σ Γ v v' × upto_domain u' v'.
Proof.
  intros HΣ X; induction X in v |- * using red1_ind_all.
  - intro XX; invs XX. 1: invs X.
    + cbn. rewrite simpl_subst, !lift0_id; [|lia].
      tac (tApp N1 a).
    + tac (b {0 := a}).
    + tac (M' {0 := a}).
      apply eta_beta_eta, eta_subst; eta.
    + tac (b {0 := N2}).
      apply eta_beta_eta, subst_eta; eta.
  - intro XX; invs XX.
    + tac (b' {0 := r}).
      apply eta_beta_eta, subst_eta; eta.
    + tac (b' {0 := b}).
    + tac (r {0 := b}).
      apply eta_beta_eta, eta_subst; eta.
  - intros XX; invs XX.
  - intros XX; invs XX.
    + tac (iota_red pars c args brs).
    + apply eta1_mkApps_inv in X as [[v' [? ?]]|[l' [? ?]]]; subst.
      { invs e. }
      tac (iota_red pars c l' brs).
      apply beta_eta_mkApps; beta_eta.
      apply All2_skipn; beta_eta.
    + tac (iota_red pars c args brs').
      apply beta_eta_mkApps; [|reflexivity].
      apply OnOne2_length in X as e.
      rewrite !nth_nth_error. destruct (nth_error brs c) eqn:f.
      * eapply OnOne2_nth_error in X; tea.
        destruct X as [? [f' ?]]. rewrite f'.
        destruct s as [[]|[]]; beta_eta.
      * apply nth_error_None in f. rewrite e in f.
        apply nth_error_None in f. now rewrite f.

  - intro XX. apply eta1_mkApps_inv in XX as [[M' [? ?]]|[l' [? ?]]]; subst.
    + invs e.
      * enough (∑ fn', beta_eta Σ Γ fn fn'
                       × unfold_fix mfix1 idx = Some (narg, fn')) as XX. {
          destruct XX as [fn' [? ?]].
          tac (mkApps fn' args). }
        unfold unfold_fix in *.
        destruct (nth_error mfix idx) eqn:e; [|discriminate].
        apply OnOne2_length in X as el.
        eapply OnOne2_nth_error in X as X'; tea.
        invs H. destruct X' as [v' [e' [|]]]; tea.
        -- subst. exists (subst0 (fix_subst mfix1) (dbody v')); split.
           ++ apply subst_beta_eta with (Γ':=[]); tas.
              unfold fix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ now rewrite e'.
        -- exists (subst0 (fix_subst mfix1) (dbody d)); eta.
           ++ apply subst_beta_eta with (Γ':=[]); tas.
              unfold fix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ rewrite e'. destruct p as [? HH]; now invs HH.
      * enough (∑ fn', beta_eta Σ Γ fn fn'
                       × unfold_fix mfix1 idx = Some (narg, fn')) as XX. {
          destruct XX as [fn' [? ?]].
          tac (mkApps fn' args). }
        unfold unfold_fix in *.
        destruct (nth_error mfix idx) eqn:e; [|discriminate].
        apply OnOne2_length in X as el.
        eapply OnOne2_nth_error in X as X'; tea.
        invs H. destruct X' as [v' [e' [|]]]; tea.
        -- subst. exists (subst0 (fix_subst mfix1) (dbody v')); split.
           ++ apply subst_beta_eta with (Γ':=[]); tas.
              unfold fix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ now rewrite e'.
        -- exists (subst0 (fix_subst mfix1) (dbody v')); eta.
           ++ transitivity (subst0 (fix_subst mfix) (dbody v')). {
                destruct p.
                eapply beta_eta_subst0; beta_eta.
                eapply untyped_subslet_fix_subst. }
              apply subst_beta_eta with (Γ':=[]); tas.
              unfold fix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ rewrite e'. destruct p as [? HH]; now invs HH.
    + pretac (mkApps fn l'). 1: beta_eta.
      constructor. left. econstructor; tea.
      unfold is_constructor in *.
      destruct (nth_error args narg) eqn:e; [|discriminate].
      eapply OnOne2_nth_error in o as [v' [e' [|]]]; tea;
        rewrite e'.
      * easy.
      * clear -H0 e0.
        induction e0; cbn in *; try discriminate;
          rewrite isConstruct_app_App in *; auto.

  - intro XX; invs XX.
    + tac (tCase ip p' (mkApps fn args) brs).
    + apply eta1_mkApps_inv in X as [[M' [? ?]]|[l' [? ?]]]; subst.
      2: tac (tCase ip p (mkApps fn l') brs).
      invs e.
      * enough (∑ fn', beta_eta Σ Γ fn fn'
                       × unfold_cofix mfix1 idx = Some (narg, fn')) as XX. {
          destruct XX as [fn' [? ?]].
          tac (tCase ip p (mkApps fn' args) brs). }
        unfold unfold_cofix in *.
        destruct (nth_error mfix idx) eqn:e; [|discriminate].
        apply OnOne2_length in X as el.
        eapply OnOne2_nth_error in X as X'; tea.
        invs H. destruct X' as [v' [e' [|]]]; tea.
        -- subst. exists (subst0 (cofix_subst mfix1) (dbody v')); split.
           ++ apply subst_beta_eta with (Γ':=[]); tas.
              unfold cofix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ now rewrite e'.
        -- exists (subst0 (cofix_subst mfix1) (dbody d)); eta.
           ++ apply subst_beta_eta with (Γ':=[]); tas.
              unfold cofix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ rewrite e'. destruct p0 as [? HH]; now invs HH.
      * enough (∑ fn', beta_eta Σ Γ fn fn'
                       × unfold_cofix mfix1 idx = Some (narg, fn')) as XX. {
          destruct XX as [fn' [? ?]].
          tac (tCase ip p (mkApps fn' args) brs). }
        unfold unfold_cofix in *.
        destruct (nth_error mfix idx) eqn:e; [|discriminate].
        apply OnOne2_length in X as el.
        eapply OnOne2_nth_error in X as X'; tea.
        invs H. destruct X' as [v' [e' [|]]]; tea.
        -- subst. exists (subst0 (cofix_subst mfix1) (dbody v')); split.
           ++ apply subst_beta_eta with (Γ':=[]); tas.
              unfold cofix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ now rewrite e'.
        -- exists (subst0 (cofix_subst mfix1) (dbody v')); eta.
           ++ transitivity (subst0 (cofix_subst mfix) (dbody v')). {
                destruct p0.
                eapply beta_eta_subst0; beta_eta.
                eapply untyped_subslet_cofix_subst. }
              apply subst_beta_eta with (Γ':=[]); tas.
              unfold cofix_subst. rewrite el.
              clear -X. induction #|mfix1|; trea.
              constructor; beta_eta.
           ++ rewrite e'. destruct p0 as [? HH]; now invs HH.
    + tac (tCase ip p (mkApps fn args) brs').


  - intro XX; invs XX.
    apply eta1_mkApps_inv in X as [[M' [? ?]]|[l' [? ?]]]; subst.
    2: tac (tProj p (mkApps fn l')).
    invs e.
    * enough (∑ fn', beta_eta Σ Γ fn fn'
                     × unfold_cofix mfix1 idx = Some (narg, fn')) as XX. {
        destruct XX as [fn' [? ?]].
        tac (tProj p (mkApps fn' args)). }
      unfold unfold_cofix in *.
      destruct (nth_error mfix idx) eqn:e; [|discriminate].
      apply OnOne2_length in X as el.
      eapply OnOne2_nth_error in X as X'; tea.
      invs H. destruct X' as [v' [e' [|]]]; tea.
      -- subst. exists (subst0 (cofix_subst mfix1) (dbody v')); split.
         ++ apply subst_beta_eta with (Γ':=[]); tas.
            unfold cofix_subst. rewrite el.
            clear -X. induction #|mfix1|; trea.
            constructor; beta_eta.
         ++ now rewrite e'.
      -- exists (subst0 (cofix_subst mfix1) (dbody d)); eta.
         ++ apply subst_beta_eta with (Γ':=[]); tas.
            unfold cofix_subst. rewrite el.
            clear -X. induction #|mfix1|; trea.
            constructor; beta_eta.
         ++ rewrite e'. destruct p0 as [? HH]; now invs HH.
    * enough (∑ fn', beta_eta Σ Γ fn fn'
                     × unfold_cofix mfix1 idx = Some (narg, fn')) as XX. {
        destruct XX as [fn' [? ?]].
        tac (tProj p (mkApps fn' args)). }
      unfold unfold_cofix in *.
      destruct (nth_error mfix idx) eqn:e; [|discriminate].
      apply OnOne2_length in X as el.
      eapply OnOne2_nth_error in X as X'; tea.
      invs H. destruct X' as [v' [e' [|]]]; tea.
      -- subst. exists (subst0 (cofix_subst mfix1) (dbody v')); split.
         ++ apply subst_beta_eta with (Γ':=[]); tas.
            unfold cofix_subst. rewrite el.
            clear -X. induction #|mfix1|; trea.
            constructor; beta_eta.
         ++ now rewrite e'.
      -- exists (subst0 (cofix_subst mfix1) (dbody v')); eta.
         ++ transitivity (subst0 (cofix_subst mfix) (dbody v')). {
              destruct p0.
              eapply beta_eta_subst0; beta_eta.
              eapply untyped_subslet_cofix_subst. }
            apply subst_beta_eta with (Γ':=[]); tas.
            unfold cofix_subst. rewrite el.
            clear -X. induction #|mfix1|; trea.
            constructor; beta_eta.
         ++ rewrite e'. destruct p0 as [? HH]; now invs HH.

  - intro XX; invs XX.
  - intro XX; invs XX.
    apply eta1_mkApps_inv in X as [[M' [? ?]]|[l' [? ?]]]; subst.
    1: invs e.
    eapply OnOne2_nth_error in o as [v' [e' [|]]]; tea.
    + subst. tac v'.
    + tac v'.
  - intro XX; invs XX.
    + tac v.
    + itac IHX X0.
      exists (tLambda na u' N), (tLambda na v' N); beta_eta.
    + tac (tLambda na M' M'0).

  - intro XX; invs XX.
    + clear IHX. invs X.
      * destruct v; invs H0.
        rewrite lift_subst0_Rel.
        exists (tLambda na N v2), (tLambda na1 v1 v2); beta_eta.
      * apply mkApps_eq_app in H as [H2 [H3 H4]];
          [|auto].
        eapply app_removelast_last with (d:=tRel 0) in H2.
        rewrite H2 in H1; rewrite H2; clear H2.
        rewrite <- H3 in H1; rewrite <- H3; clear H3.
        set (args' := removelast args) in *; clearbody args'; clear args.
        eapply lift_Apps_Fix_inv in H4 as [? [? [? [? ?]]]]; subst.
        rewrite PCUICBasicStrengthening.lift_unfold_fix in H0.
        destruct (unfold_fix x idx) as [[]|] eqn:e; [|discriminate]. invs H0.
        assert (is_constructor narg x0); [|clear H1]. {
          unfold is_constructor in *.
          destruct (le_gt_dec #|x0| narg).
          - rewrite nth_error_app_ge in H1; rewrite map_length in *; tas.
            destruct (narg - #|x0|) as [|[|n]]; discriminate.
          - rewrite nth_error_app_lt in H1; [|now rewrite map_length].
            rewrite nth_error_map in H1.
            destruct (nth_error x0 narg); [cbn in *|discriminate].
            unfold isConstruct_app, decompose_app in *.
            pose proof (decompose_app_rec_lift 1 0 t0 []) as HH.
            destruct (decompose_app_rec t0 []); cbn in *.
            rewrite HH in H1. cbn in H1.
            destruct t1; try discriminate; reflexivity.
        }
        tac (mkApps t x0).
        rewrite <- mkApps_nested; cbn.
        eapply eta1_beta_eta.
        pose proof (eta_red na (mkApps t x0) N) as X.
        now rewrite lift_mkApps in X.
      * eapply (red1_strengthening _ Γ [] [vass na N]) in X0 as [v' [? ?]]; tas.
        subst. tac v'.
      * invs X0.
        -- invs H0.
        -- now sap Rel_mkApps_Fix in H.
    + tac (tLambda na M'0 M').
    + itac IHX X0.
      exists (tLambda na N u'), (tLambda na N v'); beta_eta.

  - intro XX; invs XX.
    + itac IHX X0.
      exists (tLetIn na u' t b'), (tLetIn na v' t b'); beta_eta.
    + tac (tLetIn na r r0 b').
    + tac (tLetIn na r t r0).
  - intro XX; invs XX.
    + tac (tLetIn na r0 r b').
    + itac IHX X0.
      exists (tLetIn na b u' b'), (tLetIn na b v' b'); beta_eta.
    + tac (tLetIn na b r r0).
  - intro XX; invs XX.
    + destruct (red1_eta_ctx _ _ (Γ,, vdef na r0 t) _ _ X) as [v' [? ?]]. {
        constructor; [|reflexivity]. now cbn; eta. }
      tac (tLetIn na r0 t v').
    + destruct (red1_eta_ctx _ _ (Γ,, vdef na b r0) _ _ X) as [v' [? ?]]. {
        constructor; [|reflexivity]. now cbn; eta. }
      tac (tLetIn na b r0 v').
    + itac IHX X0.
      exists (tLetIn na b t u'), (tLetIn na b t v'); beta_eta.
  - intro XX; invs XX.
    + apply IHX in X0 as (u' & v' & H1 & H2 & H3).
      exists (tCase ind u' c brs), (tCase ind v' c brs); beta_eta.
      constructor; beta_eta. apply All2_refl. intro; split; reflexivity.
    + tac (tCase ind p' c' brs).
    + tac (tCase ind p' c brs').
  - intro XX; invs XX.
    + tac (tCase ind p' c' brs).
    + apply IHX in X0 as (u' & v' & H1 & H2 & H3).
      exists (tCase ind p u' brs), (tCase ind p v' brs); beta_eta.
      constructor; beta_eta. apply All2_refl. intro; split; reflexivity.
    + tac (tCase ind p c' brs').

  - intro XX; invs XX.
    + tac (tCase ind p' c brs').
    + tac (tCase ind p c' brs').
    + enough (∑ u' v', OnOne2 (on_Trel_eq (beta_eta Σ Γ) snd fst) brs' u'
                × All2 (fun x y => x.1 = y.1 × upto_domain x.2 y.2) u' v'
                × OnOne2 (on_Trel_eq (beta_eta Σ Γ) snd fst) brs'0 v') as XX. {
        destruct XX as [u' [v' [H1 [H2 H3]]]].
        exists (tCase ind p c u'), (tCase ind p c v'); beta_eta. }
      induction X in brs'0, X0 |- *; invs X0.
      * rdestruct p0. destruct X as [X1 X2].
        apply p2 in X1 as [u' [v' [? [? ?]]]].
        exists ((hd.1, u') :: tl), ((hd.1, v') :: tl).
        do 3 constructor; cbn; eta.
        apply All2_refl; now intros [].
      * rdestruct p0. destruct hd' as [n hd']; cbn in *; subst n.
        pretac ((hd.1, hd') :: tl'); constructor; cbn; beta_eta.
        -- eapply OnOne2_impl; tea.
           intros [] [] []; cbn; beta_eta.
        -- apply All2_refl; now intros [].
      * destruct X1. destruct hd' as [n hd']; cbn in *; subst n.
        pretac ((hd.1, hd') :: tl'); constructor; cbn; beta_eta.
        -- apply All2_refl; now intros [].
        -- eapply OnOne2_impl; tea.
           intros [] [] ?; cbn in *; rdest; beta_eta.
      * apply IHX in X1 as (u' & v' & ? & ? & ?); clear IHX.
        exists (hd :: u'), (hd :: v').
        repeat split; constructor; cbn; beta_eta.

  - intro XX; invs XX.
    itac IHX X0.
      exists (tProj p u'), (tProj p v'); beta_eta.
  - intro XX; invs XX.
    + itac IHX X0.
      exists (tApp u' M2), (tApp v' M2); beta_eta.
    + tac (tApp N1 N2).
  - intro XX; invs XX.
    + tac (tApp N1 N2).
    + itac IHX X0.
      exists (tApp M1 u'), (tApp M1 v'); beta_eta.
  - intro XX; invs XX.
    + itac IHX X0.
      exists (tProd na u' M2), (tProd na v' M2); beta_eta.
    + tac (tProd na N1 N2).
  - intro XX; invs XX.
    + tac (tProd na N1 N2).
    + itac IHX X0.
      exists (tProd na M1 u'), (tProd na M1 v'); beta_eta.

  - intro XX; invs XX.
    enough (∑ u' v', OnOne2 (beta_eta Σ Γ) l' u'
                × All2 (fun x y => upto_domain x y) u' v'
                × OnOne2 (beta_eta Σ Γ) l'0 v') as XX. {
        destruct XX as [u' [v' [H1 [H2 H3]]]].
        exists (tEvar ev u'), (tEvar ev v'); beta_eta. }
      induction X in l'0, X0 |- *; invs X0.
      * rdestruct p.
        apply p0 in X as [u' [v' [? [? ?]]]].
        exists (u' :: tl), (v' :: tl).
        repeat split; constructor; beta_eta.
        apply All2_refl; now intros [].
      * rdestruct p.
        pretac (hd' :: tl'); constructor; cbn; beta_eta.
        -- eapply OnOne2_impl; beta_eta.
        -- now apply All2_refl.
      * pretac (hd' :: tl'); constructor; cbn; beta_eta.
        -- now apply All2_refl.
        -- eapply OnOne2_impl; tea.
           intros [] [] ?; cbn in *; rdest; beta_eta.
      * apply IHX in X1 as (u' & v' & ? & ? & ?); clear IHX.
        exists (hd :: u'), (hd :: v').
        repeat split; constructor; cbn; beta_eta.

  - intro XX; invs XX.
    + enough (∑ mfix2 mfix4,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × dbody d0 = dbody d1 × dname d0 = dname d1
                      × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun x y => upto_domain (dtype x) (dtype y)
                      × upto_domain (dbody x) (dbody y)
                      × rarg x = rarg y) mfix2 mfix4
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × dbody d0 = dbody d1 × dname d0 = dname d1
                      × rarg d0 = rarg d1) mfix3 mfix4) as XX. {
        destruct XX as (mfix2 & mfix4 & ? & ? & ?).
        exists (tFix mfix2 idx), (tFix mfix4 idx); beta_eta. }
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        itac p1 X1.
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        exists ({| dname := na'; dtype := u'; dbody := bd'; rarg := ar' |} :: tl),
          ({| dname := na'; dtype := v'; dbody := bd'; rarg := ar' |} :: tl);
          repeat split; constructor; cbn; repeat split; trea.
        all: now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        2-3: now apply All2_refl.
        OnOne2_All2; rdest; try invs e0; beta_eta.
      * destruct X1 as [X1 p0].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        1-2: now apply All2_refl.
        OnOne2_All2; rdest; try invs e; beta_eta.
      * itac IHX X1; clear IHX.
        exists (hd :: u'), (hd :: v'); beta_eta.
        constructor; beta_eta.
    + enough (∑ mfix2 mfix4,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix1) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun x y => upto_domain (dtype x) (dtype y)
                      × upto_domain (dbody x) (dbody y)
                      × rarg x = rarg y) mfix2 mfix4
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix3 mfix4)
        as XX. {
        destruct XX as (mfix2 & mfix4 & ? & ? & ?).
        exists (tFix mfix2 idx), (tFix mfix4 idx); beta_eta. }
      set (Γ1 := fix_context mfix1) in *; clearbody Γ1.
      set (Γ3 := fix_context mfix3) in *; clearbody Γ3.
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        tac ({| dname := na'; dtype := ty'; dbody := bd0; rarg := ar' |} :: tl);
          repeat split; constructor; cbn; repeat split; beta_eta.
        all: now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        2-3: now apply All2_refl.
        OnOne2_All2; rdest; try invs e0; beta_eta.
      * destruct X1 as [X1 p0].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        1-2: now apply All2_refl.
        OnOne2_All2; rdest; try invs e; beta_eta.
      * itac IHX X1; clear IHX.
        exists (hd :: u'), (hd :: v'); beta_eta.
        all: constructor; beta_eta.

  - intro XX; invs XX.
    + enough (∑ mfix2,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix3 mfix2)
        as XX. {
        assert (#|mfix1| = #|mfix3|). {
          erewrite <- OnOne2_length; tea.
          now erewrite OnOne2_length; tea. }
        destruct XX as (mfix2 & ? & ?).
        pretac (tFix mfix2 idx); [|beta_eta].
        ap_beta_eta. eapply All2_impl; tea; cbn.
        intros ? ? [? [? []]]; beta_eta. }
      assert (upto_types (Γ ,,, fix_context mfix0) (Γ ,,, fix_context mfix3))
        as HΓ. {
        apply upto_types_app; [reflexivity|].
        apply upto_types_fix_context. now eapply OnOne2_length. }
      set (Γ0 := fix_context mfix0) in *; clearbody Γ0.
      set (Γ3 := fix_context mfix3) in *; clearbody Γ3.
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        exists ({| dname := na'; dtype := ty0; dbody := bd'; rarg := ar' |} :: tl);
          split; constructor; cbn; repeat split; beta_eta.
        all: try now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        cbn in *; invs p0.
        exists (hd' :: tl'); split; constructor; beta_eta.
        -- OnOne2_All2; rdest; try invs e0; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
      * destruct X1 as [X1 X2].
        destruct hd as [na ty bd ar].
        cbn in *; invs X2. 
        exists (hd' :: tl'); split; constructor; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- OnOne2_All2; rdest; try invs e; beta_eta.
      * eapply IHX  in X1 as [mfix2 [? ?]]; clear IHX.
        exists (hd :: mfix2); split; constructor; beta_eta.
    + enough (∑ mfix2 mfix4,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix1) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun x y => upto_domain (dtype x) (dtype y)
                      × upto_domain (dbody x) (dbody y)
                      × rarg x = rarg y) mfix2 mfix4
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix3 mfix4)
        as XX. {
        destruct XX as (mfix2 & mfix4 & ? & ? & ?).
        exists (tFix mfix2 idx), (tFix mfix4 idx); beta_eta. }
      assert (upto_types (Γ ,,, fix_context mfix0) (Γ ,,, fix_context mfix1))
        as HΓ. {
        apply upto_types_app; [reflexivity|].
        apply upto_types_fix_context. now eapply OnOne2_length. }
      assert (upto_types (Γ ,,, fix_context mfix0) (Γ ,,, fix_context mfix3))
        as HΓ'. {
        apply upto_types_app; [reflexivity|].
        apply upto_types_fix_context. now eapply OnOne2_length. }
      set (Γ0 := fix_context mfix0) in *; clearbody Γ0.
      set (Γ1 := fix_context mfix1) in *; clearbody Γ1.
      set (Γ3 := fix_context mfix3) in *; clearbody Γ3.
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        eapply p1 in X1 as [u' [v' [? [? ?]]]].
        exists ({| dname := na'; dtype := ty'; dbody := u'; rarg := ar' |} :: tl),
          ({| dname := na'; dtype := ty'; dbody := v'; rarg := ar' |} :: tl);
          repeat split; constructor; cbn; repeat split; beta_eta.
        all: now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        cbn in *; invs p0.
        pretac (hd' :: tl'); constructor; beta_eta.
        -- OnOne2_All2; rdest; try invs e0; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
      * destruct X1 as [X1 X2].
        destruct hd as [na ty bd ar].
        cbn in *; invs X2. 
        pretac (hd' :: tl'); constructor; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- OnOne2_All2; rdest; try invs e; beta_eta.
      * eapply IHX  in X1 as [mfix2 [mfix4 [? [? ?]]]]; clear IHX.
        exists (hd :: mfix2), (hd :: mfix4); repeat split; constructor; beta_eta.

  - intro XX; invs XX.
    + enough (∑ mfix2 mfix4,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × dbody d0 = dbody d1 × dname d0 = dname d1
                      × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun x y => upto_domain (dtype x) (dtype y)
                      × upto_domain (dbody x) (dbody y)
                      × rarg x = rarg y) mfix2 mfix4
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × dbody d0 = dbody d1 × dname d0 = dname d1
                      × rarg d0 = rarg d1) mfix3 mfix4) as XX. {
        destruct XX as (mfix2 & mfix4 & ? & ? & ?).
        exists (tCoFix mfix2 idx), (tCoFix mfix4 idx); beta_eta. }
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        itac p1 X1.
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        exists ({| dname := na'; dtype := u'; dbody := bd'; rarg := ar' |} :: tl),
          ({| dname := na'; dtype := v'; dbody := bd'; rarg := ar' |} :: tl);
          repeat split; constructor; cbn; repeat split; trea.
        all: now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        2-3: now apply All2_refl.
        OnOne2_All2; rdest; try invs e0; beta_eta.
      * destruct X1 as [X1 p0].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        1-2: now apply All2_refl.
        OnOne2_All2; rdest; try invs e; beta_eta.
      * itac IHX X1; clear IHX.
        exists (hd :: u'), (hd :: v'); beta_eta.
        constructor; beta_eta.
    + enough (∑ mfix2 mfix4,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix1) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun x y => upto_domain (dtype x) (dtype y)
                      × upto_domain (dbody x) (dbody y)
                      × rarg x = rarg y) mfix2 mfix4
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix3 mfix4)
        as XX. {
        destruct XX as (mfix2 & mfix4 & ? & ? & ?).
        exists (tCoFix mfix2 idx), (tCoFix mfix4 idx); beta_eta. }
      set (Γ1 := fix_context mfix1) in *; clearbody Γ1.
      set (Γ3 := fix_context mfix3) in *; clearbody Γ3.
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        tac ({| dname := na'; dtype := ty'; dbody := bd0; rarg := ar' |} :: tl);
          repeat split; constructor; cbn; repeat split; beta_eta.
        all: now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        2-3: now apply All2_refl.
        OnOne2_All2; rdest; try invs e0; beta_eta.
      * destruct X1 as [X1 p0].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        cbn in *; invs p0.
        pretac ({| dname := na'; dtype := ty'; dbody := bd'; rarg := ar' |} :: tl');
          constructor; cbn; repeat split; trea; beta_eta.
        1-2: now apply All2_refl.
        OnOne2_All2; rdest; try invs e; beta_eta.
      * itac IHX X1; clear IHX.
        exists (hd :: u'), (hd :: v'); beta_eta.
        all: constructor; beta_eta.

  - intro XX; invs XX.
    + enough (∑ mfix2,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix3 mfix2)
        as XX. {
        assert (#|mfix1| = #|mfix3|). {
          erewrite <- OnOne2_length; tea.
          now erewrite OnOne2_length; tea. }
        destruct XX as (mfix2 & ? & ?).
        pretac (tCoFix mfix2 idx); [|beta_eta].
        ap_beta_eta. eapply All2_impl; tea; cbn.
        intros ? ? [? [? []]]; beta_eta. }
      assert (upto_types (Γ ,,, fix_context mfix0) (Γ ,,, fix_context mfix3))
        as HΓ. {
        apply upto_types_app; [reflexivity|].
        apply upto_types_fix_context. now eapply OnOne2_length. }
      set (Γ0 := fix_context mfix0) in *; clearbody Γ0.
      set (Γ3 := fix_context mfix3) in *; clearbody Γ3.
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        exists ({| dname := na'; dtype := ty0; dbody := bd'; rarg := ar' |} :: tl);
          split; constructor; cbn; repeat split; beta_eta.
        all: try now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        cbn in *; invs p0.
        exists (hd' :: tl'); split; constructor; beta_eta.
        -- OnOne2_All2; rdest; try invs e0; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
      * destruct X1 as [X1 X2].
        destruct hd as [na ty bd ar].
        cbn in *; invs X2. 
        exists (hd' :: tl'); split; constructor; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- OnOne2_All2; rdest; try invs e; beta_eta.
      * eapply IHX  in X1 as [mfix2 [? ?]]; clear IHX.
        exists (hd :: mfix2); split; constructor; beta_eta.
    + enough (∑ mfix2 mfix4,
              All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix1) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix1 mfix2
            × All2 (fun x y => upto_domain (dtype x) (dtype y)
                      × upto_domain (dbody x) (dbody y)
                      × rarg x = rarg y) mfix2 mfix4
            × All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                      × beta_eta Σ (Γ ,,, fix_context mfix3) (dbody d0) (dbody d1)
                      × dname d0 = dname d1 × rarg d0 = rarg d1) mfix3 mfix4)
        as XX. {
        destruct XX as (mfix2 & mfix4 & ? & ? & ?).
        exists (tCoFix mfix2 idx), (tCoFix mfix4 idx); beta_eta. }
      assert (upto_types (Γ ,,, fix_context mfix0) (Γ ,,, fix_context mfix1))
        as HΓ. {
        apply upto_types_app; [reflexivity|].
        apply upto_types_fix_context. now eapply OnOne2_length. }
      assert (upto_types (Γ ,,, fix_context mfix0) (Γ ,,, fix_context mfix3))
        as HΓ'. {
        apply upto_types_app; [reflexivity|].
        apply upto_types_fix_context. now eapply OnOne2_length. }
      set (Γ0 := fix_context mfix0) in *; clearbody Γ0.
      set (Γ1 := fix_context mfix1) in *; clearbody Γ1.
      set (Γ3 := fix_context mfix3) in *; clearbody Γ3.
      induction X in mfix3, X0 |- *; invs X0.
      * rdestruct p. destruct X as [X1 X2].
        destruct hd as [na ty bd ar].
        destruct hd' as [na' ty' bd' ar'].
        destruct hd'0 as [na0 ty0 bd0 ar0].
        cbn in *; invs X2; invs p0.
        eapply p1 in X1 as [u' [v' [? [? ?]]]].
        exists ({| dname := na'; dtype := ty'; dbody := u'; rarg := ar' |} :: tl),
          ({| dname := na'; dtype := ty'; dbody := v'; rarg := ar' |} :: tl);
          repeat split; constructor; cbn; repeat split; beta_eta.
        all: now apply All2_refl.
      * rdestruct p.
        destruct hd as [na ty bd ar].
        cbn in *; invs p0.
        pretac (hd' :: tl'); constructor; beta_eta.
        -- OnOne2_All2; rdest; try invs e0; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
      * destruct X1 as [X1 X2].
        destruct hd as [na ty bd ar].
        cbn in *; invs X2. 
        pretac (hd' :: tl'); constructor; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- eapply All2_refl. intro; rdest; beta_eta.
        -- OnOne2_All2; rdest; try invs e; beta_eta.
      * eapply IHX  in X1 as [mfix2 [mfix4 [? [? ?]]]]; clear IHX.
        exists (hd :: mfix2), (hd :: mfix4); repeat split; constructor; beta_eta.
Qed.

(* Lemma beta_eta_local_confluence {cf:checker_flags} {Σ Γ t u v} : *)
(*   wf Σ -> beta_eta1 Σ Γ t u -> beta_eta1 Σ Γ t v -> *)
(*   ∑ u' v', beta_eta Σ Γ u u' × beta_eta Σ Γ v v' × upto_domain u' v'. *)
(* Proof. *)
(*   intros HΣ [X|X] [Y|Y]. *)
(*   - apply red1_red in X; apply red1_red in Y. *)
(*     eapply red_confluence in X as [v' [? ?]]; try exact Y; tas. *)
(*     tac v'. *)
(*   - eapply red1_eta1_diamond in X; tea. *)
(*   - eapply red1_eta1_diamond in X as [u' [v' [? [? ?]]]]; tea. *)
(*     exists v', u'; repeat split; try symmetry; beta_eta. *)
(*   - eapply eta1_local_confluence in X as [v' [? ?]]; try exact Y. *)
(*     tac v'. *)
(* Qed. *)

(* Print Assumptions beta_eta_local_confluence. *)

(* Lemma beta_eta_confluence {cf:checker_flags} {Σ Γ t u v} : *)
(*   wf Σ -> beta_eta Σ Γ t u -> beta_eta Σ Γ t v -> *)
(*   ∑ u' v', beta_eta Σ Γ u u' × beta_eta Σ Γ v v' × upto_domain u' v'. *)
(* Admitted. *)

  




(* Lemma eta_postponment {cf:checker_flags} Σ (HΣ : wf Σ) Γ u v w *)
(*       (H1 : eta1 u v) (H2 : red1 Σ Γ v w) *)
(*   : ∑ v', clos_refl (red1 Σ Γ) u v' × clos_refl eta_expands v' w. *)
(* Proof. *)


(* Definition etax1 := transp eta1. *)
(* Definition etax := transp eta. *)


(* Lemma beta_eta_change_domain Σ Γ na na' M A B : *)
(*   beta_eta Σ Γ (tLambda na A M) (tLambda na' B M). *)
(* Proof. *)
(*   etransitivity. *)
(*   - apply eta_beta_eta. do 2 constructor. *)
(*   - eta. *)
(* Defined. *)
(* Hint Resolve beta_eta_change_domain : beta_eta. *)

(* Lemma etax1_etax1_diamond {Σ Γ t u v} : *)
(*   etax1 t u -> etax1 t v -> *)
(*   ∑ v', beta_etax Σ Γ u v' × beta_etax Σ Γ v v'. *)
(* Proof. *)
(*   intro X; induction X in Γ, v |- * using eta1_ind_all. *)
(*   - exists (tLambda na A (tApp (lift0 1 v) (tRel 0))); eta 7. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A N); eta. *)
(*     + apply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na v' N); eta. *)
(*     + exists (tLambda na M' M'0); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A M'); split; [eta|]. *)
(*       transitivity (tLambda na0 A M); eta. *)
(*     + exists (tLambda na M'0 M'); eta. *)
(*     + eapply (IHX (Γ,, vass na N)) in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na N v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLetIn na r t b')) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tLetIn na v' t b'); eta. *)
(*     + exists (tLetIn na r r0 b'); eta. *)
(*     + exists (tLetIn na r t r0); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLetIn na b r b')) (tRel 0))); eta 7. *)
(*     + exists (tLetIn na r0 r b'); eta. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tLetIn na b v' b'); eta. *)
(*     + exists (tLetIn na b r r0); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLetIn na b t r)) (tRel 0))); eta 7. *)
(*     + exists (tLetIn na r0 t r); eta. *)
(*     + exists (tLetIn na b r0 r); eta. *)
(*     + eapply (IHX (Γ ,, vdef na b t)) in X0 as [v' [H1 H2]]. *)
(*       exists (tLetIn na b t v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tCase ind p' c brs)) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tCase ind v' c brs); eta. *)
(*     + exists (tCase ind p' c' brs); eta. *)
(*     + exists (tCase ind p' c brs'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tCase ind p c' brs)) (tRel 0))); eta 7. *)
(*     + exists (tCase ind p' c' brs); eta. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tCase ind p v' brs); eta. *)
(*     + exists (tCase ind p c' brs'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tCase ind p c brs')) (tRel 0))); split. *)
(*       1: eta. cbn. ap_beta_eta. *)
(*       apply All2_map. eapply OnOne2_All2; tea. *)
(*       * intros [] [] [[] ?]; cbn in *; eta. *)
(*       * eta. *)
(*     + exists (tCase ind p' c brs'); eta. *)
(*       apply beta_eta_Case; cbnr. *)
(*       eapply OnOne2_All2; tea. *)
(*       * intros [] [] [[] ?]; cbn in *; eta. *)
(*       * eta. *)
(*     + exists (tCase ind p c' brs'); eta. *)
(*       apply beta_eta_Case; cbnr. *)
(*       eapply OnOne2_All2; tea. *)
(*       * intros [] [] [[] ?]; cbn in *; eta. *)
(*       * eta. *)
(*     + enough (∑ v', All2 (on_Trel_eq (beta_eta Σ Γ) snd fst) brs' v' *)
(*                     × All2 (on_Trel_eq (beta_eta Σ Γ) snd fst) brs'0 v') as XX. { *)
(*         destruct XX as [v' [H1 H2]]. exists (tCase ind p c v'). *)
(*         split; apply beta_eta_Case; eta. } *)
(*       induction X in brs'0, X0 |- *; invs X0. *)
(*       * destruct hd, hd', hd'0, p0 as [[] ?], X; cbn in *; subst. *)
(*         apply (s Γ) in e1 as [v' [H1 H2]]. *)
(*         exists ((n1, v') :: tl); split; constructor; cbn; eta; apply All2_refl; eta. *)
(*       * destruct hd, hd', p0 as [[] ?]; cbn in *; subst. *)
(*         exists ((n0, t0) :: tl'); split; constructor; cbn; eta. *)
(*         -- eapply OnOne2_All2; tea; eta. intros [] [] []; cbn; eta. *)
(*         -- apply All2_refl; eta. *)
(*       * destruct hd, hd', X1 as []; cbn in *; subst. *)
(*         exists ((n0, t0) :: tl'); split; constructor; cbn; eta. *)
(*         -- apply All2_refl; eta. *)
(*         -- eapply OnOne2_All2; tea; eta. intros [] [] [[] ?]; cbn; eta. *)
(*       * eapply IHX in X1 as [v' [H1 H2]]. *)
(*         exists (hd :: v'); split; constructor; cbn; eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tProj p c')) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tProj p v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tApp N1 M2)) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tApp v' M2); eta. *)
(*     + exists (tApp N1 N2); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tApp M1 N2)) (tRel 0))); eta 7. *)
(*     + exists (tApp N1 N2); eta. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tApp M1 v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tProd na N1 M2)) (tRel 0))); eta 8. *)
(*     + apply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tProd na v' M2); eta. *)
(*     + exists (tProd na N1 N2); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tProd na M1 N2)) (tRel 0))); eta 8. *)
(*     + exists (tProd na N1 N2); eta. *)
(*     + eapply (IHX (Γ,, vass na M1)) in X0 as [v' [H1 H2]]. *)
(*       exists (tProd na M1 v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tEvar ev l')) (tRel 0))); split; [eta|]. *)
(*       cbn. ap_beta_eta. apply All2_map. eapply OnOne2_All2; trea. *)
(*       cbn; clear; intros. constructor 1. right. now apply weakening_eta1. *)
(*     + enough (∑ v', All2 (beta_eta Σ Γ) l' v' × All2 (beta_eta Σ Γ) l'0 v') as XX. { *)
(*         destruct XX as [v' [H1 H2]]. exists (tEvar ev v'). *)
(*         split; apply beta_eta_Evar; eta. } *)
(*       induction X in l'0, X0 |- *; invs X0. *)
(*       * destruct p as [? p]. apply (p Γ) in X as [v' [H1 H2]]. *)
(*         exists (v' :: tl); split; constructor; tas; apply All2_refl; tre. *)
(*       * destruct p. exists (hd' :: tl'); split; constructor; trea. *)
(*         -- eapply OnOne2_All2; trea. eta. *)
(*         -- eta. *)
(*         -- eapply All2_refl; trea. *)
(*       * specialize (IHX tl'); forward IHX. { *)
(*           eapply OnOne2_impl; tea; cbn. now intros ? ? []. } *)
(*         destruct IHX as [v' [H1 H2]]. *)
(*         exists (hd' :: v'); split; constructor; trea. *)
(*         -- eta. *)
(*         -- etransitivity; tea. eapply OnOne2_All2; trea; cbn. *)
(*            intros ? ? []; eta. *)
(*       * apply IHX in X1 as [v' [H1 H2]]. *)
(*         exists (hd :: v'); split; constructor; trea. *)
(* Admitted. *)

(* Hint Resolve weakening_red1 : beta_eta. *)
(* Require Import PCUICSubstitution PCUICUnivSubst. *)

(* Lemma subst1_eta t t' k u : *)
(*   eta t t' -> eta (u {k := t}) (u {k := t'}). *)
(* Proof. *)
(*   intro; apply subst_eta. now constructor. *)
(* Defined. *)

(* Hint Resolve subst1_eta | 10 : beta_eta. *)

(* Lemma eta_subst1 t k u u' : *)
(*   eta u u' -> eta (u {k := t}) (u' {k := t}). *)
(* Proof. apply eta_subst. Defined. *)

(* Hint Resolve eta_subst1 | 10 : beta_eta. *)

(* Lemma mkApps_cons t l u : mkApps t (l ++ [u]) = tApp (mkApps t l) u. *)
(* Proof. now rewrite <- mkApps_nested. Qed. *)

(* Lemma OnOne2_app' {A} (P : A -> A -> Type) l l' tl : *)
(*   OnOne2 P l l' -> OnOne2 P (l ++ tl) (l' ++ tl). *)
(* Proof. induction 1; simpl; try constructor; auto. Qed. *)
