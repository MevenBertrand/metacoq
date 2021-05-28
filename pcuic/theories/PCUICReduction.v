(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICInduction
     PCUICContextRelation PCUICCases PCUICCongrClosure.

Require Import ssreflect.
Require Import Equations.Prop.DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Definition iota_red npar p args br :=
  subst (List.rev (List.skipn npar args)) 0 
    (expand_lets (inst_case_branch_context p br) (bbody br)).

(** ** Reduction *)

(** *** Helper functions for reduction *)

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
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
      | S n => tCoFix l n :: aux n
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
  unfold fix_subst. generalize (tFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (tCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.rev_length mapi_length. Qed.


(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

(*Lemma OnOne2_local_env_mapi_context R (Γ Δ : context) (f g : nat -> term -> term) :
  OnOne2_local_env (fun Γ d d' => R (mapi_context f Γ) (map_decl (f #|Γ|) d) (map_decl (g #|Γ|) d)) Γ Δ ->
  OnOne2_local_env R (mapi_context f Γ) (mapi_context g Δ).
Proof.
  unfold on_Trel in *; induction 1; simpl; try solve [econstructor; intuition auto].
  * rewrite /map_decl /=. econstructor.
Qed.*)

Local Open Scope type_scope.

Inductive top_red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
(** Reductions *)
(** Beta *)
| red_beta na t b a :
    top_red1 Σ Γ (tApp (tLambda na t b) a) (subst10 a b)

(** Let *)
| red_zeta na b t b' :
    top_red1 Σ Γ (tLetIn na b t b') (subst10 b b')

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    top_red1 Σ Γ (tRel i) (lift0 (S i) body)

(** Case *)
| red_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
    top_red1 Σ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) p args br)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    top_red1 Σ Γ (mkApps (tFix mfix idx) args) (mkApps fn args)

(** CoFix-case unfolding *)
| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    top_red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    top_red1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

(** Constant unfolding *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    top_red1 Σ Γ (tConst c u) (subst_instance u body)

(** Proj *)
| red_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    top_red1 Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg.

Definition red1 := congr1 top_red1.

Definition red1_ctx Σ := (OnOne2_local_env (on_one_decl (fun Δ t t' => red1 Σ Δ t t'))).
Definition red1_ctx_rel Σ Γ := (OnOne2_local_env (on_one_decl (fun Δ t t' => red1 Σ (Γ ,,, Δ) t t'))).

Lemma top_red1_ind_all :
  forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : aname) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

       (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ci : case_info) p params' c brs,
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) p.(pparams) params' ->
           P Γ (tCase ci p c brs)
               (tCase ci (set_pparams p params') c brs)) ->

       (* (forall (Γ : context) (ci : case_info) p pcontext' c brs,
          OnOne2_local_env (on_one_decl (fun Γ' => P (Γ ,,, Γ'))) p.(pcontext) pcontext' ->
          P Γ (tCase ci p c brs)
            (tCase ci (set_pcontext p pcontext') c brs)) ->
 *)
       (forall (Γ : context) (ci : case_info) p preturn' c brs,
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_preturn p preturn') c brs)) ->
       
       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ci p c brs brs',
          OnOne2 (fun br br' =>
          (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, inst_case_branch_context p br)) 
            (P (Γ ,,, inst_case_branch_context p br)))
            bbody bcontext br br')) brs brs' ->
          P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : term), red1 Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                         P Γ (tApp M1 M2) (tApp N1 M2)) ->

       (forall (Γ : context) (M2 N2 : term) (M1 : term), red1 Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                         P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Proof.
  intros.
  induction X27 using congr1_ind_all.

  all: auto.
  destruct X27.
  all: eauto.
Qed.

Hint Constructors top_red1 : pcuic.

Definition red Σ Γ := clos_refl_trans (red1 Σ Γ).

Definition red_one_ctx_rel (Σ : global_env) (Γ : context) :=
  OnOne2_local_env
    (on_one_decl (fun (Δ : context) (t t' : term) => red Σ (Γ,,, Δ) t t')).

Definition red_ctx_rel Σ Γ := clos_refl_trans (red1_ctx_rel Σ Γ).

(* TODO move to All_decls *)
Inductive red_decls Σ (Γ Γ' : context) : forall (x y : context_decl), Type :=
| red_vass na T T' :
    red Σ Γ T T' ->
    red_decls Σ Γ Γ' (vass na T) (vass na T')

| red_vdef_body na b b' T T' :
    red Σ Γ b b' ->
    red Σ Γ T T' ->
    red_decls Σ Γ Γ' (vdef na b T) (vdef na b' T').
Derive Signature NoConfusion for red_decls.

Definition red_context Σ := All2_fold (red_decls Σ).
Definition red_context_rel Σ Γ :=
  All2_fold (fun Δ Δ' => red_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')).

Lemma refl_red Σ Γ t : red Σ Γ t t.
Proof.
  reflexivity.
Defined.

Lemma trans_red Σ Γ M P N : red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.
Proof.
  etransitivity; tea. now constructor.
Defined.

Definition red_rect' Σ Γ M (P : term -> Type) :
  P M ->
  (forall P0 N, red Σ Γ M P0 -> P P0 -> red1 Σ Γ P0 N -> P N) ->
  forall (t : term) (r : red Σ Γ M t), P t.
Proof.
  intros X X0 t r. apply clos_rt_rtn1_iff in r.
  induction r; eauto.
  eapply X0; tea. now apply clos_rt_rtn1_iff.
Defined.

Definition red_rect_n1 := red_rect'.
Definition red_rect_1n Σ Γ (P : term -> term -> Type) :
  (forall x, P x x) ->
  (forall x y z, red1 Σ Γ x y -> red Σ Γ y z -> P y z -> P x z) ->
  forall x y, red Σ Γ x y -> P x y.
Proof.
  intros Hrefl Hstep x y r.
  apply clos_rt_rt1n_iff in r.
  induction r; eauto.
  eapply Hstep; eauto.
  now apply clos_rt_rt1n_iff.
Defined.

(** Simple lemmas about reduction *)

Lemma red1_red Σ Γ t u : red1 Σ Γ t u -> red Σ Γ t u.
Proof.
  econstructor; eauto.
Qed.

Hint Resolve red1_red refl_red : core pcuic.

Lemma red_step Σ Γ t u v : red1 Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  etransitivity; tea. now constructor.
Qed.

Lemma red_trans Σ Γ t u v : red Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  etransitivity; tea.
Defined.

(** For this notion of reductions, theses are the atoms that reduce to themselves:

 *)

Definition atom t :=
  match t with
  | tRel _
  | tVar _
  | tSort _
  | tConst _ _
  | tInd _ _
  | tConstruct _ _ _ => true
  | _ => false
  end.

(** Generic method to show that a relation is closed by congruence using
    a notion of one-hole context. *)


Section ReductionCongruence.
    Context {Σ : global_env} {Γ : context}.

    Lemma red_abs_alt na M M' N N' :
      red Σ Γ M M' -> red Σ (Γ ,, vass na M) N N'
      -> red Σ Γ (tLambda na M N) (tLambda na M' N').
    Proof.
      intros.
      by apply congr_all_clos_refl_trans ; do 2 constructor.
    Qed.

    Lemma red_abs na M M' N N' :
      red Σ Γ M M' -> red Σ (Γ ,, vass na M') N N'
      -> red Σ Γ (tLambda na M N) (tLambda na M' N').
    Proof.
      intros.
      transitivity (tLambda na M' N).
      all: by apply congr_all_clos_refl_trans ; do 2 constructor.
    Qed.

    Lemma red_app M0 M1 N0 N1 :
      red Σ Γ M0 M1 ->
      red Σ Γ N0 N1 ->
      red Σ Γ (tApp M0 N0) (tApp M1 N1).
    Proof.
      intros.
      by apply congr_all_clos_refl_trans ; do 2 constructor.
    Qed.

    Lemma red_mkApps M0 M1 N0 N1 :
      red Σ Γ M0 M1 ->
      All2 (red Σ Γ) N0 N1 ->
      red Σ Γ (mkApps M0 N0) (mkApps M1 N1).
    Proof.
      intros.
      by apply congr_all_mkApps.
    Qed.

    Lemma red_letin na d0 d1 t0 t1 b0 b1 :
      red Σ Γ d0 d1 -> red Σ Γ t0 t1 -> red Σ (Γ ,, vdef na d1 t1) b0 b1 ->
      red Σ Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1).
    Proof.
      intros.
      transitivity (tLetIn na d1 t1 b0).
      all: by apply congr_all_clos_refl_trans ; do 2 constructor.
    Qed.
        

    Definition red_one_brs p Γ brs brs' :=
      OnOne2 (fun br br' => 
        let ctx := inst_case_branch_context p br in
        on_Trel_eq (red Σ (Γ ,,, ctx)) bbody bcontext br br')
      brs brs'.

    Definition red_brs p Γ brs brs' :=
      All2 (fun br br' => 
        let ctx := inst_case_branch_context p br in
        on_Trel_eq (red Σ (Γ ,,, ctx)) bbody bcontext br br')
      brs brs'.

    Lemma red_case {ci p c brs pars' pret' c' brs'} :
       All2 (red Σ Γ) p.(pparams) pars' ->
      red Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) pret' ->
      red Σ Γ c c' ->
      red_brs p Γ brs brs' ->
      red Σ Γ (tCase ci p c brs) 
        (tCase ci {| pparams := pars'; puinst := p.(puinst);
                     pcontext := p.(pcontext); preturn := pret' |} c' brs').
    Proof.
      intros.
      apply congr_all_clos_refl_trans ; constructor.
      - repeat split.
        2: by constructor.
        eapply All2_impl ; tea.
        by constructor.
      - by constructor.
      - eapply All2_impl ; tea.
        intros ? ? [].
        by split ; [constructor|..].
    Qed.

    Lemma red1_it_mkLambda_or_LetIn :
      forall Δ u v,
        red1 Σ (Γ ,,, Δ) u v ->
        red1 Σ Γ (it_mkLambda_or_LetIn Δ u)
             (it_mkLambda_or_LetIn Δ v).
    Proof.
      by apply congr1_it_mkLambda_or_LetIn_f.
    Qed.

    Lemma red1_it_mkProd_or_LetIn :
      forall Δ u v,
        red1 Σ (Γ ,,, Δ) u v ->
        red1 Σ Γ (it_mkProd_or_LetIn Δ u)
             (it_mkProd_or_LetIn Δ v).
    Proof.
      by apply congr1_it_mkProd_or_LetIn_f.
    Qed.

    Lemma red_it_mkLambda_or_LetIn :
      forall Δ u v,
        red Σ (Γ ,,, Δ) u v ->
        red Σ Γ (it_mkLambda_or_LetIn Δ u)
            (it_mkLambda_or_LetIn Δ v).
    Proof.
    intros.
    apply congr_all_it_mkLambda_or_LetIn.
    2: assumption.
    apply All2_fold_refl.
    apply on_one_decl_refl.
    tc.
    Qed.

    Lemma red_it_mkProd_or_LetIn :
      forall Δ u v,
        red Σ (Γ ,,, Δ) u v ->
        red Σ Γ (it_mkProd_or_LetIn Δ u)
            (it_mkProd_or_LetIn Δ v).
    Proof.
    intros.
    apply congr_all_it_mkProd_or_LetIn.
    2: assumption.
    apply All2_fold_refl.
    apply on_one_decl_refl.
    tc.
    Qed.

    Lemma red_proj_c :
      forall p c c',
        red Σ Γ c c' ->
        red Σ Γ (tProj p c) (tProj p c').
    Proof.
      intros.
      by apply congr_all_clos_refl_trans ; do 2 constructor.
    Qed.

    Lemma red_fix_congr :
      forall mfix mfix' idx,
        All2 (fun d0 d1 =>
                (red Σ Γ (dtype d0) (dtype d1)) ×
                (red Σ (Γ ,,, fix_context mfix) (dbody d0) (dbody d1) ×
                (dname d0, rarg d0) = (dname d1, rarg d1))
        ) mfix mfix' ->
      red Σ Γ (tFix mfix idx) (tFix mfix' idx).
    Proof.
      intros mfix mfix' idx h.
      apply congr_all_clos_refl_trans.
      constructor.
      eapply All2_impl ; tea.
      intros ? ? (?&?&e).
      inversion e.
      repeat split ; auto.
      all: by constructor.
    Qed.

    Lemma red_cofix_congr :
      forall mfix mfix' idx,
        All2 (fun d0 d1 =>
                (red Σ Γ (dtype d0) (dtype d1)) ×
                (red Σ (Γ ,,, fix_context mfix) (dbody d0) (dbody d1) ×
                (dname d0, rarg d0) = (dname d1, rarg d1))
        ) mfix mfix' ->
      red Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx).
    Proof.
      intros.
      apply congr_all_clos_refl_trans.
      constructor.
      eapply All2_impl ; tea.
      intros ? ? (?&?&e).
      inversion e.
      repeat split ; auto.
      all: by constructor.
    Qed.

    Lemma red_prod_l :
      forall na A B A',
        red Σ Γ A A' ->
        red Σ Γ (tProd na A B) (tProd na A' B).
    Proof.
      intros.
      apply congr_all_clos_refl_trans ; constructor ; auto.
      all: constructor ; auto.
    Qed.

    Lemma red_prod_r :
      forall na A B B',
        red Σ (Γ ,, vass na A) B B' ->
        red Σ Γ (tProd na A B) (tProd na A B').
    Proof.
      intros.
      apply congr_all_clos_refl_trans ; constructor ; auto.
      all: constructor ; auto.
    Qed.

    Lemma red_prod :
      forall na A B A' B',
        red Σ Γ A A' ->
        red Σ (Γ ,, vass na A) B B' ->
        red Σ Γ (tProd na A B) (tProd na A' B').
    Proof.
      intros.
      apply congr_all_clos_refl_trans ; constructor ; auto.
      all: constructor ; auto.
    Qed.

    Lemma red_evar :
      forall ev l l',
        All2 (red Σ Γ) l l' ->
        red Σ Γ (tEvar ev l) (tEvar ev l').
    Proof.
      intros.
      apply congr_all_clos_refl_trans ; constructor ; auto.
      eapply All2_impl ; tea.
      by constructor.
    Qed.

    Lemma red_atom t : atom t -> red Σ Γ t t.
    Proof.
      intros. reflexivity.
    Qed.

End ReductionCongruence.
