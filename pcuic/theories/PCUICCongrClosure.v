(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPosition PCUICCases PCUICContextRelation.

Require Import ssreflect.
Require Import Equations.Prop.DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Notation rtrans_clos := clos_refl_trans_n1.

Lemma All2_many_OnOne2 :
  forall A (R : A -> A -> Type) l l',
    All2 R l l' ->
    rtrans_clos (OnOne2 R) l l'.
Proof.
  intros A R l l' h.
  induction h.
  - constructor.
  - econstructor.
    + constructor. eassumption.
    + clear - IHh. rename IHh into h.
      induction h.
      * constructor.
      * econstructor.
        -- econstructor 2. eassumption.
        -- assumption.
Qed.

Definition tDummy := tVar String.EmptyString.

(** 
  Helper functions
*)

Arguments OnOne2 {A} P%type l l'.

Definition set_pcontext (p : predicate term) (pctx' : context) : predicate term :=
  {| pparams := p.(pparams);
      puinst := p.(puinst);
      pcontext := pctx';
      preturn := p.(preturn) |}.

Definition set_pcontext_two {p x} x' : 
  set_pcontext (set_pcontext p x') x = set_pcontext p x := 
  eq_refl.
      
Definition set_preturn (p : predicate term) (pret' : term) : predicate term :=
  {| pparams := p.(pparams);
      puinst := p.(puinst);
      pcontext := p.(pcontext);
      preturn := pret' |}.

Definition set_preturn_two {p} pret pret' : set_preturn (set_preturn p pret') pret = set_preturn p pret := 
  eq_refl.

Definition set_pparams (p : predicate term) (pars' : list term) : predicate term :=
  {| pparams := pars';
     puinst := p.(puinst);
     pcontext := p.(pcontext);
     preturn := p.(preturn) |}.

Definition set_pparams_two {p pars} pars' : set_pparams (set_pparams p pars') pars = set_pparams p pars := 
  eq_refl.

Definition map_decl_na (f : aname -> aname) (g : term -> term) d :=
  {| decl_name := f (decl_name d);
     decl_body := option_map g (decl_body d);
     decl_type := g (decl_type d) |}.

(** We do not allow alpha-conversion and P applies to only one of the 
  fields in the context declaration. Used to define one-step context reduction. *)
Inductive on_one_decl (P : context -> term -> term -> Type)
  Γ : context_decl -> context_decl -> Type :=
  | decl_ass : forall na ty ty', P Γ ty ty' -> on_one_decl P Γ (vass na ty) (vass na ty')
  | decl_def_ty : forall na b ty ty', P Γ ty ty' -> on_one_decl P Γ (vdef na b ty) (vdef na b ty')
  | decl_def_bd : forall na b b' ty, P Γ b b' -> on_one_decl P Γ (vdef na b ty) (vdef na b' ty).

Lemma on_one_decl_impl (P Q : context -> term -> term -> Type) : 
  (forall Γ, inclusion (P Γ) (Q Γ)) ->
  forall Γ, inclusion (on_one_decl P Γ) (on_one_decl Q Γ).
Proof.
  intros HP Γ x y [].
  all: by constructor ; apply HP.
Qed.

Lemma on_one_decl_refl P :
  (forall Γ, Reflexive (P Γ)) ->
  forall Γ, Reflexive ((on_one_decl P) Γ).
Proof.
  intros r Γ [? [] ?].
  all: constructor ; reflexivity.
Qed.

Lemma on_one_decl_map_na (P : context -> term -> term -> Type) f g : 
  forall Γ,
    inclusion (on_one_decl (fun Γ => on_Trel (P (map (map_decl_na f g) Γ)) g) Γ)
    (on_Trel (on_one_decl P (map (map_decl_na f g) Γ)) (map_decl_na f g)).
Proof.
  intros Γ x y [].
  all: rewrite /on_Trel in o |- *.
  all: by constructor.
Qed.

Lemma on_one_decl_map (P : context -> term -> term -> Type) f : 
  forall Γ,
    inclusion (on_one_decl (fun Γ => on_Trel (P (map (map_decl f) Γ)) f) Γ)
    (on_Trel (on_one_decl P (map (map_decl f) Γ)) (map_decl f)).
Proof.
  intros Γ x y [].
  all: rewrite /on_Trel in o |- *.
  all: by constructor.
Qed.

Lemma on_one_decl_mapi_context (P : context -> term -> term -> Type) f : 
  forall Γ,
    inclusion (on_one_decl (fun Γ => on_Trel (P (mapi_context f Γ)) (f #|Γ|)) Γ)
    (on_Trel (on_one_decl P (mapi_context f Γ)) (map_decl (f #|Γ|))).
Proof.
  intros Γ x y [].
  all: rewrite /on_Trel in o |- *.
  all: by constructor.
Qed.

Lemma on_one_decl_test_impl (P Q : context -> term -> term -> Type) (p : term -> bool) : 
  forall Γ d d', 
    on_one_decl P Γ d d' ->
    test_decl p d ->
    (forall x y, p x -> P Γ x y -> Q Γ x y) ->
    on_one_decl Q Γ d d'.
Proof.
  intros Γ d d' [] []%andb_and ?.
  all: constructor ; auto.
Qed.

Section OnOne_local_2.
  Context (P : forall (Γ : context), context_decl -> context_decl -> Type).

  Inductive OnOne2_local_env : context -> context -> Type :=
  | onone2_localenv_cons_abs Γ na na' t t' :
      P Γ (vass na t) (vass na' t') ->
      OnOne2_local_env (Γ ,, vass na t) (Γ ,, vass na' t')
  | onone2_localenv_def Γ na na' b b' t t' :
      P Γ (vdef na b t) (vdef na' b' t') ->
      OnOne2_local_env (Γ ,, vdef na b t) (Γ ,, vdef na' b' t')
  | onone2_localenv_cons_tl Γ Γ' d :
      OnOne2_local_env Γ Γ' ->
      OnOne2_local_env (Γ ,, d) (Γ' ,, d).
End OnOne_local_2.

Instance OnOne2_local_env_length {P ctx ctx'} : 
  HasLen (OnOne2_local_env P ctx ctx') #|ctx| #|ctx'|.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma OnOne2_local_env_impl R S :
  (forall Δ, inclusion (R Δ) (S Δ)) ->
  inclusion (OnOne2_local_env R)
            (OnOne2_local_env S).
Proof.
  intros H x y H'.
  induction H'; try solve [econstructor; firstorder].
Qed.

Lemma OnOne2_local_env_ondecl_impl P Q : 
  (forall Γ, inclusion (P Γ) (Q Γ)) ->
  inclusion (OnOne2_local_env (on_one_decl P)) (OnOne2_local_env (on_one_decl P)).
Proof.
  intros HP. now apply OnOne2_local_env_impl, on_one_decl_impl.
Qed.

Lemma OnOne2_local_env_map R Γ Δ (f : aname -> aname) (g : term -> term) :
  OnOne2_local_env (fun Γ => on_Trel (R (map (map_decl_na f g) Γ)) (map_decl_na f g)) Γ Δ ->
  OnOne2_local_env R (map (map_decl_na f g) Γ) (map (map_decl_na f g) Δ).
Proof.
  unfold on_Trel in *; induction 1; simpl; try solve [econstructor; intuition auto].
Qed.

Lemma OnOne2_local_env_map_context R Γ Δ (f : term -> term) :
  OnOne2_local_env (fun Γ => on_Trel (R (map (map_decl f) Γ)) (map_decl f)) Γ Δ ->
  OnOne2_local_env R (map_context f Γ) (map_context f Δ).
Proof.
  unfold on_Trel in *; induction 1; simpl; try solve [econstructor; intuition auto].
Qed.

Lemma OnOne2_local_env_mapi_context R Γ Δ (f : nat -> term -> term) :
  OnOne2_local_env (fun Γ => on_Trel (R (mapi_context f Γ)) (map_decl (f #|Γ|))) Γ Δ ->
  OnOne2_local_env R (mapi_context f Γ) (mapi_context f Δ).
Proof.
  unfold on_Trel in *; induction 1; simpl; try solve [econstructor; intuition auto].
  rewrite -(length_of X). now constructor.
Qed.

Lemma test_context_k_impl {p q : nat -> term -> bool} {k k'} {ctx} :
  (forall n t, p n t -> q n t) ->
  k = k' ->
  test_context_k p k ctx -> test_context_k q k' ctx.
Proof.
  intros Hfg <-.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto;
  move/andb_and=> [testp testd]; rewrite (IHctx testp);
  eapply test_decl_impl; tea; eauto.
Qed.

Lemma OnOne2_local_env_test_context_k {P ctx ctx'} {k} {p q : nat -> term -> bool} : 
  (forall n t, q n t -> p n t) ->
  OnOne2_local_env P ctx ctx' ->
  (forall Γ d d', 
    P Γ d d' ->
    test_context_k q k Γ ->
    test_decl (q (#|Γ| + k)) d ->
    test_decl (p (#|Γ| + k)) d') ->
  test_context_k q k ctx ->
  test_context_k p k ctx'.
Proof.
  intros hq onenv HPq.
  induction onenv.
  * move=> /= /andb_and [testq testd].
    rewrite (test_context_k_impl _ _ testq) //.
    simpl; eauto.
  * move=> /= /andb_and [testq testd].
    rewrite (test_context_k_impl _ _ testq) //.
    simpl; eauto.
  * move=> /= /andb_and [testq testd].
    rewrite (IHonenv testq).
    eapply test_decl_impl; tea.
    intros x Hx. eapply hq.
    now rewrite -(length_of onenv).
Qed.

Lemma on_one_decl_test_decl (P : context -> term -> term -> Type) Γ
  (p q : term -> bool) d d' :
  (forall t, p t -> q t) ->
  (forall t t', P Γ t t' -> p t -> q t') ->
  on_one_decl P Γ d d' ->
  test_decl p d ->
  test_decl q d'.
Proof.
  intros Hp ? [] ?.
  all: unfold test_decl in * ; cbn in * ; rtoProp ; eauto.
Qed.

Lemma OnOne2_local_env_impl_test {P Q ctx ctx'} {k} {p : nat -> term -> bool} : 
  OnOne2_local_env P ctx ctx' ->
  (forall Γ d d', 
    P Γ d d' ->
    test_context_k p k Γ ->
    test_decl (p (#|Γ| + k)) d ->
    Q Γ d d') ->
  test_context_k p k ctx ->
  OnOne2_local_env Q ctx ctx'.
Proof.
  intros onenv HPq.
  induction onenv.
  * move=> /= /andb_and [testq testd].
    constructor; auto.
  * move=> /= /andb_and [testq testd].
    constructor; auto.
  * move=> /= /andb_and [testq testd].
    constructor; auto.
Qed.

(** 
  One hole congruence, used for one-step reduction
*)

Section Congr1.

  Local Open Scope type_scope.
  Inductive congr1 R (Σ : global_env) (Γ : context) : term -> term -> Type :=

  | congr1_abs_ty na A A' t : congr1 R Σ Γ A A' -> congr1 R Σ Γ (tLambda na A t) (tLambda na A' t)
  | congr1_abs_tm na A t t' :
      congr1 R Σ (Γ ,, vass na A) t t' -> congr1 R Σ Γ (tLambda na A t) (tLambda na A t')

  | congr1_let_def na b b' A t : congr1 R Σ Γ b b' -> congr1 R Σ Γ (tLetIn na b A t) (tLetIn na b' A t)
  | congr1_let_ty na b A A' t : congr1 R Σ Γ A A' -> congr1 R Σ Γ (tLetIn na b A t) (tLetIn na b A' t)
  | congr1_let_body na b A t t' : congr1 R Σ (Γ ,, vdef na b A) t t' -> congr1 R Σ Γ (tLetIn na b A t) (tLetIn na b A t')

  | congr1_case_param ci p params' c brs :
      OnOne2 (congr1 R Σ Γ) p.(pparams) params' ->
      congr1 R Σ Γ (tCase ci p c brs)
              (tCase ci (set_pparams p params') c brs)
            
  | congr1_case_return ci p preturn' c brs :
    congr1 R Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
    congr1 R Σ Γ (tCase ci p c brs)
            (tCase ci (set_preturn p preturn') c brs)
      
  | congr1_case_discr ci p c c' brs :
    congr1 R Σ Γ c c' -> 
    congr1 R Σ Γ (tCase ci p c brs) (tCase ci p c' brs)

  | congr1_case_brs ci p c brs brs' :    
      OnOne2 (fun br br' =>
        on_Trel_eq (congr1 R Σ (Γ ,,, inst_case_branch_context p br)) bbody bcontext br br')
        brs brs' ->
      congr1 R Σ Γ (tCase ci p c brs) (tCase ci p c brs')

  | congr1_proj p c c' : congr1 R Σ Γ c c' -> congr1 R Σ Γ (tProj p c) (tProj p c')

  | congr1_app_fun t t' u : congr1 R Σ Γ t t' -> congr1 R Σ Γ (tApp t u) (tApp t' u)
  | congr1_app_arg t u u' : congr1 R Σ Γ u u' -> congr1 R Σ Γ (tApp t u) (tApp t u')

  | congr1_prod_dom na A A' B : congr1 R Σ Γ A A' -> congr1 R Σ Γ (tProd na A B) (tProd na A' B)
  | congr1_prod_cod na A B B' : congr1 R Σ (Γ ,, vass na A) B B' ->
                                congr1 R Σ Γ (tProd na A B) (tProd na A B')

  | congr1_evar ev l l' : OnOne2 (congr1 R Σ Γ) l l' -> congr1 R Σ Γ (tEvar ev l) (tEvar ev l')

  | congr1_fix_ty mfix mfix' idx :
      OnOne2 (on_Trel_eq (congr1 R Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
      congr1 R Σ Γ (tFix mfix idx) (tFix mfix' idx)

  | congr1_fix_body mfix mfix' idx :
      OnOne2 (on_Trel_eq (congr1 R Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
            mfix mfix' ->
      congr1 R Σ Γ (tFix mfix idx) (tFix mfix' idx)

  | congr1_cofix_ty mfix mfix' idx :
      OnOne2 (on_Trel_eq (congr1 R Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
      congr1 R Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx)

  | congr1_cofix_body mfix mfix' idx :
      OnOne2 (on_Trel_eq (congr1 R Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
            mfix mfix' ->
      congr1 R Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx)

  (* the generic constructor at the end so that congruences are preferred by the constructor tactic*)
  | congr1_base t t' : R Σ Γ t t' -> congr1 R Σ Γ t t'.



  Lemma congr1_ind_all :
    forall R (Σ : global_env) (P : context -> term -> term -> Type),

      (forall (Γ : context) (t t' : term),
        R Σ Γ t t' -> P Γ t t') ->

      (forall (Γ : context) (na : aname) (A A' t : term),
      congr1 R Σ Γ A A' -> P Γ A A' -> P Γ (tLambda na A t) (tLambda na A' t)) ->

      (forall (Γ : context) (na : aname) (A t t' : term),
      congr1 R Σ (Γ,, vass na A) t t' -> P (Γ,, vass na A) t t' -> P Γ (tLambda na A t) (tLambda na A t')) ->

      (forall (Γ : context) (na : aname) (b b' A t : term),
      congr1 R Σ Γ b b' -> P Γ b b' -> P Γ (tLetIn na b A t) (tLetIn na b' A t)) ->

      (forall (Γ : context) (na : aname) (b A A' t : term),
      congr1 R Σ Γ A A' -> P Γ A A' -> P Γ (tLetIn na b A t) (tLetIn na b A' t)) ->

      (forall (Γ : context) (na : aname) (b A t t' : term),
      congr1 R Σ (Γ,, vdef na b A) t t' -> P (Γ,, vdef na b A) t t' ->
      P Γ (tLetIn na b A t) (tLetIn na b A t')) ->

      (forall (Γ : context) (ci : case_info) p params' c brs,
        OnOne2 (Trel_conj (congr1 R Σ Γ) (P Γ)) p.(pparams) params' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_pparams p params') c brs)) ->
              
      (forall (Γ : context) (ci : case_info) p preturn' c brs,
        congr1 R Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
        P (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
        P Γ (tCase ci p c brs)
            (tCase ci (set_preturn p preturn') c brs)) ->
      
      (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
      congr1 R Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

      (forall (Γ : context) ci p c brs brs',
        OnOne2 (fun br br' =>
        (on_Trel_eq (Trel_conj (congr1 R Σ (Γ ,,, inst_case_branch_context p br)) 
          (P (Γ ,,, inst_case_branch_context p br)))
          bbody bcontext br br')) brs brs' ->
        P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

      (forall (Γ : context) (p : projection) (c c' : term), congr1 R Σ Γ c c' -> P Γ c c' ->
                                                            P Γ (tProj p c) (tProj p c')) ->

      (forall (Γ : context) (M1 N1 : term) (M2 : term), congr1 R Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                        P Γ (tApp M1 M2) (tApp N1 M2)) ->

      (forall (Γ : context) (M2 N2 : term) (M1 : term), congr1 R Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                        P Γ (tApp M1 M2) (tApp M1 N2)) ->

      (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
      congr1 R Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

      (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
      congr1 R Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

      (forall (Γ : context) (ev : nat) (l l' : list term),
          OnOne2 (Trel_conj (congr1 R Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

      (forall (Γ : context) (mfix mfix' : list (def term)) (idx : nat),
      OnOne2 (on_Trel_eq (Trel_conj (congr1 R Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
      P Γ (tFix mfix idx) (tFix mfix' idx)) ->

      (forall (Γ : context) (mfix mfix' : list (def term)) (idx : nat),
      OnOne2 (on_Trel_eq (Trel_conj (congr1 R Σ (Γ ,,, fix_context mfix))
                                    (P (Γ ,,, fix_context mfix))) dbody
                          (fun x => (dname x, dtype x, rarg x))) mfix mfix' ->
      P Γ (tFix mfix idx) (tFix mfix' idx)) ->

      (forall (Γ : context) (mfix mfix' : list (def term)) (idx : nat),
      OnOne2 (on_Trel_eq (Trel_conj (congr1 R Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix mfix' ->
      P Γ (tCoFix mfix idx) (tCoFix mfix' idx)) ->

      (forall (Γ : context) (mfix mfix' : list (def term)) (idx : nat),
      OnOne2 (on_Trel_eq (Trel_conj (congr1 R Σ (Γ ,,, fix_context mfix))
                                    (P (Γ ,,, fix_context mfix))) dbody
                          (fun x => (dname x, dtype x, rarg x))) mfix mfix' ->
      P Γ (tCoFix mfix idx) (tCoFix mfix' idx)) ->

      forall (Γ : context) (t t' : term), congr1 R Σ Γ t t' -> P Γ t t'.
  Proof.
    intros. rename X19 into Xlast. revert Γ t t' Xlast.
    fix aux 4. intros Γ t T.
    move aux at top.
    destruct 1; match goal with
                | |- P _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.

    - revert params' o.
      generalize (pparams p).
      fix auxl 3.
      intros params params' [].
      + constructor. split; auto.
      + constructor. auto.
        
    - revert brs' o.
      revert brs.
      fix auxl 3.
      intros l l' Hl. destruct Hl.
      + simpl in *. constructor; intros; intuition auto.
      + constructor. eapply auxl. apply Hl.

    - revert l l' o.
      fix auxl 3.
      intros l l' Hl. destruct Hl.
      + constructor. split; auto.
      + constructor. auto.

    - eapply X15.
      revert mfix mfix' o; fix auxl 3.
      intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

    - eapply X16.
      revert o. generalize (fix_context mfix). intros c Xnew.
      revert mfix mfix' Xnew; fix auxl 3; intros l l' Hl;
      destruct Hl; constructor; try split; auto; intuition.

    - eapply X17.
      revert mfix mfix' o.
      fix auxl 3; intros l l' Hl; destruct Hl;
        constructor; try split; auto; intuition.

    - eapply X18.
      revert o. generalize (fix_context mfix). intros c new.
      revert mfix mfix' new; fix auxl 3; intros l l' Hl; destruct Hl;
        constructor; try split; auto; intuition.
  Defined.

  Hint Constructors congr1 : pcuic.


  Theorem congr1_invol R Σ Γ t t' : congr1 (congr1 R) Σ Γ t t' <~> congr1 R Σ Γ t t'.
  Proof.
    split.
    2: by constructor.
    intros c.
    induction c using congr1_ind_all.
    1: assumption.
    1-16,18: constructor ; auto.

    - induction X as [? ? ? [] | ].
      all: by constructor.
      
    - induction X as [? ? ? [[] ?] |].
      + constructor.
        split ; auto.
      + by constructor.
      
    - induction X as [? ? ? []|].
      all: by constructor.

    - induction X as [? ? ? [[] ]|].
      + constructor.
        split ; auto.
      + by constructor.
      
    - induction X as [? ? ? [[] ]|].
      + constructor.
        split ; auto.
      + by constructor.

    - apply congr1_fix_body.
      revert X.
      generalize (fix_context mfix).
      induction 1 as [? ? ? [[] ]|].
      + constructor.
        split ; auto.
      + by constructor.

    - apply congr1_cofix_body.
      revert X.
      generalize (fix_context mfix).
      induction 1 as [? ? ? [[] ]|].
      + constructor.
        split ; auto.
      + by constructor.
  Qed.


  Theorem congr1_zip R Σ Γ t t' : congr1 R Σ Γ t t' ->
    ∑ π u u', t = zipc u π × t' = zipc u' π × R Σ (Γ,,, stack_context π) u u'.
  Proof.
    induction 1 using congr1_ind_all.

    - exists [], t, t' ; cbn ; by repeat split.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[Lambda_ty _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[Lambda_bd _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_assoc.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[LetIn_bd _ _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.
      
    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[LetIn_ty _ _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[LetIn_in _ _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_assoc.
      
    - destruct p ; cbn in *.
      rewrite /set_pparams /=.
      apply OnOne2_split in X as (p&p'&p1&p2&(?&(π&u&u'&?&?&?))&?&?).
      subst.
      eexists (π++[Case_pred _ (pred_hole_params _ _ _ _ _) _ _]),u,u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[Case_pred _ (pred_hole_return _ _ _) _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      1: by destruct p ; cbn in * ; subst.
      by rewrite app_nil_r app_context_assoc.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[Case_discr _ _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.

    - apply OnOne2_split in X as (br&br'&br1&br2&((?&(π&u&u'&?&?&?))&?)&?&?).
      destruct br, br' ; cbn -[inst_case_context] in *.
      subst.
      eexists (π++[Case_branch _ _ _ ((_ , branch_hole_body _), _)]),u,u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_nil_r app_context_assoc.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[Proj _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[App_l _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.
      
    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[App_r _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[Prod_l _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_nil_l.

    - destruct IHX as (π & u & u' & ? & ? & ?).
      subst.
      eexists (π++[Prod_r _ _ ]), u, u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_assoc.

    - admit.
      (*missing stack for evar*)
      
    - apply OnOne2_split in X as ([]&[]&l1&l2&((?&π&u&u'&?&?&?)&eq)&?&?).
      cbn in * ; subst.
      inversion_clear eq.
      eexists (π++[Fix ((_,(def_hole_type _ _ _)),_) _]),u,u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_assoc.

    - apply OnOne2_split in X as ([]&[]&l1&l2&((?&π&u&u'&?&?&?)&eq)&?&?).
      cbn -[fix_context] in * ; subst.
      inversion eq ; subst ; clear eq.
      eexists (π++[Fix ((_,(def_hole_body _ _ _)),_) _]),u,u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn -[fix_context].
      rewrite app_context_assoc app_nil_r.
      by rewrite fix_context_fix_context_alt map_app /= in r.

    - apply OnOne2_split in X as ([]&[]&l1&l2&((?&π&u&u'&?&?&?)&eq)&?&?).
      cbn in * ; subst.
      inversion_clear eq.
      eexists (π++[CoFix ((_,(def_hole_type _ _ _)),_) _]),u,u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn.
      by rewrite app_context_assoc.

    - apply OnOne2_split in X as ([]&[]&l1&l2&((?&π&u&u'&?&?&?)&eq)&?&?).
      cbn -[fix_context] in * ; subst.
      inversion eq ; subst ; clear eq.
      eexists (π++[CoFix ((_,(def_hole_body _ _ _)),_) _]),u,u'.
      rewrite !zipc_stack_cat stack_context_stack_cat.
      repeat split ; cbn -[fix_context].
      rewrite app_context_assoc app_nil_r.
      by rewrite fix_context_fix_context_alt map_app /= in r.
  Admitted. 
      
  Theorem zip_congr1 R Σ Γ u u' π : 
    R Σ (Γ ,,, stack_context π) u u' ->
    congr1 R Σ Γ (zipc u π) (zipc u' π).
  Proof.
    intros h.
    induction π in Γ, h |- * using list_rect_rev.
    1: by constructor.
    destruct a.

    all: try solve [
      rewrite 2!zipc_stack_cat ; cbn ;
      rewrite stack_context_stack_cat in h ; cbn in h ;
      rewrite ?app_context_nil_l ?app_context_assoc in h ;
      econstructor ; eapply IHπ ; eassumption
    ].

    - destruct mfix as ((?&[])&?).
      + rewrite 2!zipc_stack_cat. cbn.
        rewrite stack_context_stack_cat in h. cbn in h.
        rewrite app_context_nil_l in h.
        eapply congr1_fix_ty. eapply OnOne2_app. constructor. cbn.
        intuition auto.
      + rewrite 2!zipc_stack_cat. cbn.
        rewrite stack_context_stack_cat in h. cbn in h.
        rewrite app_nil_r in h.
        eapply congr1_fix_body. eapply OnOne2_app. constructor. cbn.
        intuition auto.
        eapply IHπ.
        rewrite fix_context_fix_context_alt.
        rewrite map_app. cbn. unfold def_sig at 2. cbn.
        rewrite app_context_assoc in h.
        assumption.
    
    - destruct mfix as ((?&[])&?).
      + rewrite 2!zipc_stack_cat. cbn.
        rewrite stack_context_stack_cat in h. cbn in h.
        rewrite app_context_nil_l in h.
        eapply congr1_cofix_ty. eapply OnOne2_app. constructor. cbn.
        intuition auto.
      + rewrite 2!zipc_stack_cat. cbn.
        rewrite stack_context_stack_cat in h. cbn in h.
        rewrite app_nil_r in h.
        eapply congr1_cofix_body. eapply OnOne2_app. constructor. cbn.
        intuition auto.
        eapply IHπ.
        rewrite fix_context_fix_context_alt.
        rewrite map_app. cbn. unfold def_sig at 2. cbn.
        rewrite app_context_assoc in h.
        assumption.

    - destruct p.
      + rewrite 2!zipc_stack_cat. cbn.
        rewrite stack_context_stack_cat in h. cbn in h.
        rewrite app_context_nil_l in h.
        constructor.
        eapply OnOne2_app. constructor. cbn.
        intuition auto.
      + rewrite 2!zipc_stack_cat. cbn.
        rewrite stack_context_stack_cat in h. cbn in h.
        rewrite app_nil_r app_context_assoc in h.
        constructor.
        intuition auto.
    
    - destruct brs as ((?&[])&?).
      rewrite 2!zipc_stack_cat. cbn.
      rewrite stack_context_stack_cat in h. cbn in h.
      rewrite app_nil_r app_context_assoc in h.
      constructor.
      eapply OnOne2_app. constructor.
      intuition auto.
  Qed.
    
  Corollary zip_congr1_congr R Σ Γ u u' π : 
    congr1 R Σ (Γ ,,, stack_context π) u u' ->
    congr1 R Σ Γ (zipc u π) (zipc u' π).
  Proof.
    intros.
    by apply congr1_invol, zip_congr1.
  Qed.

  Lemma OnOne2_prod_inv :
      forall A (P : A -> A -> Type) Q l l',
        OnOne2 (Trel_conj P Q) l l' ->
        OnOne2 P l l' × OnOne2 Q l l'.
  Proof.
    intros A P Q l l' h.
    induction h.
    - destruct p.
      split ; constructor ; auto.
    - destruct IHh.
      split ; constructor ; auto.
  Qed.

  Lemma congr1_refl Σ R :
    (forall Γ, Reflexive (R Σ Γ)) ->
    forall Γ, Reflexive (congr1 R Σ Γ).
  Proof.
    intros r Γ.
    intro x.
    constructor.
    reflexivity.
  Qed.

  Lemma mapi_eq {A A' B} (f : nat -> A -> B) (g : nat -> A' -> B) l l' :
    All2 (fun a a' => forall i, (f i a) = (g i a')) l l' ->
    mapi f l = mapi g l'.
  Proof.
    intros a.
    rewrite /mapi.
    generalize 0.
    induction a.
    - reflexivity.
    - cbn.
      intros.
      by f_equal.
  Qed.

  Lemma fix_context_eq mfix mfix':
    All2 (fun d d' => (dname d, dtype d) = (dname d',dtype d')) mfix mfix' ->
    fix_context mfix = fix_context mfix'.
  Proof.
    intros.
    rewrite !/fix_context.
    f_equal.
    apply mapi_eq.
    eapply All2_impl ; tea.
    intros.
    inversion H.
    destruct x,y ; cbn in *.
    by subst.
  Qed.

  (* Lemma congr1_sym Σ R :
    (forall Γ, Symmetric (R Σ Γ)) ->
    forall Γ, Symmetric (congr1 R Σ Γ).
  Proof.
    intros sym Γ x y c.
    induction c using congr1_ind_all.
    1: by constructor ; symmetry.
    all: try solve [constructor ; auto].
    
    - replace p with (set_pparams (set_pparams p params') (pparams p)) by (by destruct p).
      constructor.
      rewrite /pparams /= -/(pparams p).
      eapply OnOne2_impl.
      1: eapply OnOne2_sym ; exact X.
      by intros ? ? [].

    - replace p with (set_preturn (set_preturn p preturn') (preturn p)) by (by destruct p).
      by constructor.

    - constructor.
      eapply OnOne2_impl.
      1: eapply OnOne2_sym ; exact X.
      intros ? ? [[] ?].
      split ; auto.
      replace (inst_case_branch_context p x) with (inst_case_branch_context p y).
      1: assumption.
      destruct x, y ; cbn in *.
      by subst.

    - constructor.
      eapply OnOne2_impl.
      1: eapply OnOne2_sym ; exact X.
      by intros ? ? [].

    - constructor.
      eapply OnOne2_impl.
      1: eapply OnOne2_sym ; exact X.
      intros ? ? [[] ?].
      intuition auto.

    - apply congr1_fix_body.
      eapply OnOne2_impl.
      1: eapply OnOne2_sym ; exact X.
      intros ? ? [[] ?].
      replace (fix_context mfix') with (fix_context mfix).
      1: intuition auto.
      apply OnOne2_prod_inv_refl_r in X as [] ; auto.
      rewrite /fix_context.
      f_equal.
      apply mapi_eq.
      eapply All2_impl.
      1: eassumption.
      intros ? ? eq i.
      cbn in *.
      inversion eq.
      by repeat f_equal.

    - constructor.
      eapply OnOne2_impl.
      1: eapply OnOne2_sym ; exact X.
      intros ? ? [[] ?].
      intuition auto.

    - apply congr1_cofix_body.
      eapply OnOne2_impl.
      1: eapply OnOne2_sym ; exact X.
      intros ? ? [[] ?].
      replace (fix_context mfix') with (fix_context mfix).
      1: intuition auto.
      apply OnOne2_prod_inv_refl_r in X as [] ; auto.
      rewrite /fix_context.
      f_equal.
      apply mapi_eq.
      eapply All2_impl.
      1: eassumption.
      intros ? ? eq i.
      cbn in *.
      inversion eq.
      by repeat f_equal.
    
  Qed. *)

  Theorem congr1_clos_refl_trans R Σ Γ t u :
    congr1 (fun Σ' Γ' => (clos_refl_trans (congr1 R Σ' Γ'))) Σ Γ t u ->
    clos_refl_trans (congr1 R Σ Γ) t u.
  Proof.
    intros r.
    apply clos_rtn1_rt.
    induction r using congr1_ind_all.

    all : try solve [
      clear r ; induction IHr ; econstructor ; eauto ; constructor ; auto
    ].

    + by apply clos_rt_rtn1.

    + apply OnOne2_split in X as (?&?&?&?&(_&IH)&?&?).
      destruct p ; cbn in *.
      rewrite /set_pparams /=.
      subst.
      induction IH.
      all: econstructor ; eauto.
      constructor.
      apply OnOne2_app.
      by constructor.

    + clear r.
      destruct p ; cbn -[inst_case_predicate_context] in *.
      rewrite /set_preturn /=.
      induction IHr.
      all: econstructor ; eauto.
      by constructor.

    + apply OnOne2_split in X as (?&?&?&?&((_&IH)&?)&?&?).
      destruct x, x0 ; cbn -[inst_case_branch_context] in *.
      subst.
      induction IH.
      all: econstructor ; eauto.
      constructor.
      apply OnOne2_app.
      by constructor.

    + apply OnOne2_split in X as (?&?&?&?&(_&IH)&?&?).
      subst.
      induction IH.
      all: econstructor ; eauto.
      constructor.
      apply OnOne2_app.
      by constructor.

    + apply OnOne2_split in X as (?&?&?&?&((_&IH)&?)&?&?).
      inversion e ; clear e.
      destruct x,x0 ; cbn in *.
      subst.
      induction IH.
      all: econstructor ; eauto.
      constructor.
      apply OnOne2_app.
      by constructor.

    + apply OnOne2_split in X as (?&?&?&?&((_&IH)&?)&?&?).
      inversion e ; clear e.
      destruct x,x0 ; cbn in *.
      subst.
      induction IH.
      all: econstructor ; eauto.
      apply congr1_fix_body.
      apply OnOne2_app.
      constructor ; cbn.
      split.
      2: reflexivity.
      erewrite fix_context_eq.
      1: tea.
      apply All2_app.
      1: by apply All2_same.
      constructor.
      2: by apply All2_same.
      reflexivity.

    + apply OnOne2_split in X as (?&?&?&?&((_&IH)&?)&?&?).
      inversion e ; clear e.
      destruct x,x0 ; cbn in *.
      subst.
      induction IH.
      all: econstructor ; eauto.
      constructor.
      apply OnOne2_app.
      by constructor.

    + apply OnOne2_split in X as (?&?&?&?&((_&IH)&?)&?&?).
      inversion e ; clear e.
      destruct x,x0 ; cbn in *.
      subst.
      induction IH.
      all: econstructor ; eauto.
      apply congr1_cofix_body.
      apply OnOne2_app.
      constructor ; cbn.
      split.
      2: reflexivity.
      erewrite fix_context_eq.
      1: tea.
      apply All2_app.
      1: by apply All2_same.
      constructor.
      2: by apply All2_same.
      reflexivity.
  Qed.

  Lemma congr1_mkApps_f R Σ Γ l u u' :
  congr1 R Σ Γ u u' ->
  congr1 R Σ Γ (mkApps u l) (mkApps u' l).
  Proof.
    intros h.
    induction l in u, u', h |- *.
    1: assumption.
    all: by apply IHl ; constructor.
  Qed.

  Lemma congr1_mkApps_args R Σ Γ args args' u :
  OnOne2 (congr1 R Σ Γ) args args' ->
  congr1 R Σ Γ (mkApps u args) (mkApps u args').
  Proof.
  intros h.
  induction h in u |- *.
  - cbn.
    apply congr1_mkApps_f.
    by constructor.
  - apply IHh.
  Qed.

  Lemma congr1_it_mkLambda_or_LetIn_f R Σ Γ Δ u u' :
    congr1 R Σ (Γ ,,, Δ) u u' ->
    congr1 R Σ Γ (it_mkLambda_or_LetIn Δ u) (it_mkLambda_or_LetIn Δ u').
  Proof.
    intros h.
    induction Δ as [ | [? [] ?] ?] in u, u', h |- *.
    1: assumption.
    all: by apply IHΔ ; constructor.
  Qed.

  Lemma congr1_it_mkLambda_or_LetIn_ctx {R Σ} Γ Δ Δ' u :
  OnOne2_local_env (on_one_decl (fun Δ : context => congr1 R Σ (Γ ,,, Δ))) Δ Δ' ->
  congr1 R Σ Γ (it_mkLambda_or_LetIn Δ u)
       (it_mkLambda_or_LetIn Δ' u).
  Proof.
    induction 1 in u |- *.
    - inversion p. subst.
      cbn.
      apply congr1_it_mkLambda_or_LetIn_f.
      by constructor.
    - inversion p ; subst ; cbn.
      all: apply congr1_it_mkLambda_or_LetIn_f ; by constructor.
    - cbn. auto.
  Qed.

  Lemma congr1_it_mkProd_or_LetIn_f R Σ Γ Δ u u' :
    congr1 R Σ (Γ ,,, Δ) u u' ->
    congr1 R Σ Γ (it_mkProd_or_LetIn Δ u) (it_mkProd_or_LetIn Δ u').
  Proof.
    intros h.
    induction Δ as [ | [? [] ?] ?] in u, u', h |- *.
    1: assumption.
    all: by apply IHΔ ; constructor.
  Qed.

  Lemma congr1_it_mkProd_or_LetIn_ctx {R Σ} Γ Δ Δ' u :
  OnOne2_local_env (on_one_decl (fun Δ : context => congr1 R Σ (Γ ,,, Δ))) Δ Δ' ->
  congr1 R Σ Γ (it_mkProd_or_LetIn Δ u)
       (it_mkProd_or_LetIn Δ' u).
  Proof.
    induction 1 in u |- *.
    - inversion p. subst.
      cbn.
      apply congr1_it_mkProd_or_LetIn_f.
      by constructor.
    - inversion p ; subst ; cbn.
      all: apply congr1_it_mkProd_or_LetIn_f ; by constructor.
    - cbn. auto.
  Qed.

End Congr1.

Section CongrAll.
  Variable
    (R : global_env -> context -> context -> term -> term -> Type)
    (Rname : aname -> aname -> Prop) (Rinst : Instance.t -> Instance.t -> Prop)
    (Σ : global_env).

  Definition Rpredicate
    (Rterm : context -> context -> term -> term -> Type) Γ Γ' p p' :=
    All2 (Rterm Γ Γ') p.(pparams) p'.(pparams) ×
    Rinst p.(puinst) p'.(puinst) ×
    p.(pcontext) = p'.(pcontext)  ×
    Rterm (Γ ,,, inst_case_predicate_context p) (Γ' ,,, inst_case_predicate_context p') p.(preturn) p'.(preturn).

  Inductive congr_all (Γ Γ' : context) : term -> term -> Type :=

  | congr_all_evar e args args' :
      All2 (congr_all Γ Γ') args args' ->
      congr_all Γ Γ' (tEvar e args) (tEvar e args')

  | congr_all_app t t' u u' :
      congr_all Γ Γ' t t' ->
      congr_all Γ Γ' u u' ->
      congr_all Γ Γ' (tApp t u) (tApp t' u')

  | congr_all_lambda na na' ty ty' t t' :
      Rname na na' ->
      congr_all Γ Γ' ty ty' ->
      congr_all (Γ,,vass na ty) (Γ',,vass na' ty') t t' ->
      congr_all Γ Γ' (tLambda na ty t) (tLambda na' ty' t')

  | congr_all_prod na na' a a' b b' :
      Rname na na' ->
      congr_all Γ Γ' a a' ->
      congr_all (Γ ,, vass na a) (Γ' ,, vass na' a') b b' ->
      congr_all Γ Γ' (tProd na a b) (tProd na' a' b')

  | congr_all_letin na na' t t' ty ty' u u' :
      Rname na na' ->
      congr_all Γ Γ' t t' ->
      congr_all Γ Γ' ty ty' ->
      congr_all (Γ ,, vdef na t ty) (Γ' ,, vdef na' t' ty' ) u u' ->
      congr_all Γ Γ' (tLetIn na t ty u) (tLetIn na' t' ty' u')

  | congr_all_case ci p p' c c' brs brs' :
      Rpredicate congr_all Γ Γ' p p' ->
      congr_all Γ Γ' c c' ->
      All2 (fun br br' =>
        let ctx := inst_case_branch_context p br in
        let ctx' := inst_case_branch_context p' br' in
        on_Trel_eq (congr_all (Γ ,,, ctx) (Γ' ,,, ctx')) bbody bcontext br br'
      ) brs brs' ->
      congr_all Γ Γ' (tCase ci p c brs) (tCase ci p' c' brs')

  | congr_all_proj p c c' :
      congr_all Γ Γ' c c' ->
      congr_all Γ Γ' (tProj p c) (tProj p c')

  | congr_all_fix mfix mfix' idx :
      All2 (fun x y =>
        congr_all Γ Γ' x.(dtype) y.(dtype) ×
        congr_all (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix')
          x.(dbody) y.(dbody) ×
        x.(rarg) = y.(rarg) ×
        Rname x.(dname) y.(dname)
      ) mfix mfix' ->
      congr_all Γ Γ' (tFix mfix idx) (tFix mfix' idx)

  | congr_all_cofix mfix mfix' idx :
      All2 (fun x y =>
        congr_all Γ Γ' x.(dtype) y.(dtype) ×
        congr_all (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix')
          x.(dbody) y.(dbody) ×
        x.(rarg) = y.(rarg) ×
        Rname x.(dname) y.(dname)
      ) mfix mfix' ->
      congr_all Γ Γ' (tCoFix mfix idx) (tCoFix mfix' idx)
        
  | congr_all_base t t' :
      R Σ Γ Γ' t t' ->
      congr_all Γ Γ' t t'.

  Theorem congr_all_ind_all (P : context -> context -> term -> term -> Type) :

    (forall (Γ Γ' : context) (e : nat) (args args' : list term),
      All2 (fun t t' => P Γ Γ' t t' × congr_all Γ Γ' t t') args args' ->
    P Γ Γ' (tEvar e args) (tEvar e args')) ->

    (forall (Γ Γ' : context) (t t' u u' : term),
      congr_all Γ Γ' t t' ->
      P Γ Γ' t t' ->
      congr_all Γ Γ' u u' ->
      P Γ Γ' u u' ->
    P Γ Γ' (tApp t u) (tApp t' u')) ->

    (forall (Γ Γ' : context) (na na' : aname) (ty ty' t t' : term),
      Rname na na' ->
      congr_all Γ Γ' ty ty' ->
      P Γ Γ' ty ty' ->
      congr_all (Γ,, vass na ty) (Γ',, vass na' ty') t t' ->
      P (Γ,, vass na ty) (Γ',, vass na' ty') t t' ->
    P Γ Γ' (tLambda na ty t) (tLambda na' ty' t')) ->

    (forall (Γ Γ' : context) (na na' : aname) (a a' b b' : term),
      Rname na na' ->
      congr_all Γ Γ' a a' ->
      P Γ Γ' a a' ->
      congr_all (Γ,, vass na a) (Γ',, vass na' a') b b' ->
      P (Γ,, vass na a) (Γ',, vass na' a') b b' ->
    P Γ Γ' (tProd na a b) (tProd na' a' b')) ->

    (forall (Γ Γ' : context) (na na' : aname) (t t' ty ty' u u' : term),
      Rname na na' ->
      congr_all Γ Γ' t t' ->
      P Γ Γ' t t' ->
      congr_all Γ Γ' ty ty' ->
      P Γ Γ' ty ty' ->
      congr_all (Γ,, vdef na t ty) (Γ',, vdef na' t' ty') u u' ->
      P (Γ,, vdef na t ty) (Γ',, vdef na' t' ty') u u' ->
    P Γ Γ' (tLetIn na t ty u) (tLetIn na' t' ty' u')) ->

    (forall (Γ Γ' : context) (ci : case_info) (p p' : predicate term)
      (c c' : term) (brs brs' : list (branch term)),
      Rpredicate (fun Δ Δ' t t' => P Δ Δ' t t' × congr_all Δ Δ' t t') Γ Γ' p p' ->
      P Γ Γ' c c' ->
      All2
        (fun br br' : branch term =>
            let ctx := inst_case_branch_context p br in
            let ctx' := inst_case_branch_context p' br' in
            on_Trel_eq (fun t t' =>
              P (Γ,,, ctx) (Γ',,, ctx') t t' × congr_all (Γ,,, ctx) (Γ',,, ctx') t t')
            bbody bcontext br br')
        brs brs' ->
    P Γ Γ' (tCase ci p c brs) (tCase ci p' c' brs')) ->
    
    (forall (Γ Γ' : context) (p : projection) (c c' : term),
      congr_all Γ Γ' c c' ->
      P Γ Γ' c c' ->
    P Γ Γ' (tProj p c) (tProj p c')) ->

    (forall (Γ Γ' : context) (mfix mfix' : mfixpoint term) (idx : nat),
      All2
        (fun x y : def term =>
          P Γ Γ' (dtype x) (dtype y) ×
          congr_all Γ Γ' (dtype x) (dtype y) ×
          congr_all (Γ,,, fix_context mfix) (Γ',,, fix_context mfix')
            (dbody x) (dbody y) ×
          P (Γ,,, fix_context mfix) (Γ',,, fix_context mfix')
            (dbody x) (dbody y) ×
          rarg x = rarg y ×
          Rname (dname x) (dname y)) mfix mfix' ->
    P Γ Γ' (tFix mfix idx) (tFix mfix' idx)) ->

    (forall (Γ Γ' : context) (mfix mfix' : mfixpoint term) (idx : nat),
      All2
        (fun x y : def term =>
          P Γ Γ' (dtype x) (dtype y) ×
          congr_all Γ Γ' (dtype x) (dtype y) ×
          congr_all (Γ,,, fix_context mfix) (Γ',,, fix_context mfix')
            (dbody x) (dbody y) ×
          P (Γ,,, fix_context mfix) (Γ',,, fix_context mfix')
            (dbody x) (dbody y) ×
          rarg x = rarg y ×
          Rname (dname x) (dname y)) mfix mfix' ->
    P Γ Γ' (tCoFix mfix idx) (tCoFix mfix' idx)) ->
    
    (forall (Γ Γ' : context) (t t' : term),
      R Σ Γ Γ' t t' ->
    P Γ Γ' t t') ->

    forall (Γ Γ' : context) (t t' : term),
    congr_all Γ Γ' t t' ->
    P Γ Γ' t t'.
Proof.
  intros.
  revert Γ Γ' t t' X9.
  fix aux 5.
  move aux at top.
  move X8 at top.
  intros until t'.
  destruct 1.

  all: try solve [match goal with H : _ |- _ => eapply H ; eauto end].

  - eapply X.
    induction a.
    all: constructor ; auto.
    
  - eapply X4 ; auto.
    + unfold Rpredicate in *.
      destruct r as (?&?&?&?).
      repeat split ; auto.
      induction a0.
      all: constructor ; auto.
    + induction a as [|? ? ? ? []].
      all: constructor ; auto.

  - eapply X6 ; auto.
    generalize dependent (fix_context mfix).
    generalize dependent (fix_context mfix').
    intros ? ?.
    induction 1 as [|? ? ? ? (?&?&?&?)].
    all: constructor ; auto.
    split ; auto.

  - eapply X7 ; auto.
    generalize dependent (fix_context mfix).
    generalize dependent (fix_context mfix').
    intros ? ?.
    induction 1 as [|? ? ? ? (?&?&?&?)].
    all: constructor ; auto.
    split ; auto.

  - by apply X8.

Qed.

End CongrAll.

Instance congr_all_refl_same R Rname Rinst Σ Γ :
  (forall Γ, Reflexive (R Σ Γ Γ)) ->
  Reflexive (congr_all R Rname Rinst Σ Γ Γ).
Proof.
  constructor.
  reflexivity.
Qed.

Instance congr_all_refl_diff R Rname Rinst Σ Γ Γ' :
  (forall Γ Γ', Reflexive (R Σ Γ Γ')) ->
  Reflexive (congr_all R Rname Rinst Σ Γ Γ').
Proof.
  constructor.
  reflexivity.
Qed.

Hint Resolve All_All2 : all.
Hint Resolve All2_same : pred.

Lemma OnOne2_All2 {A}:
  forall (ts ts' : list A) P Q,
    OnOne2 P ts ts' ->
    (forall x y, P x y -> Q x y)%type ->
    (forall x, Q x x) ->
    All2 Q ts ts'.
Proof.
  intros ts ts' P Q X.
  induction X; intuition auto with pred.
Qed.

Ltac OnOne2_All2 :=
  match goal with
  | [ H : OnOne2 ?P ?ts ?ts' |- All2 ?Q ?ts ?ts' ] =>
    unshelve eapply (OnOne2_All2 _ _ P Q H); simpl; intros
  end.

Hint Extern 0 (All2 _ _ _) => OnOne2_All2; intuition auto with pred : pred.


Lemma All2_eq :
forall A (l l' : list A),
  All2 eq l l' ->
  l = l'.
Proof.
intros A l l' h.
induction h ; eauto. subst. reflexivity.
Qed.

Lemma list_split_eq :
forall A B (l l' : list (A × B)),
  map fst l = map fst l' ->
  map snd l = map snd l' ->
  l = l'.
Proof.
intros A B l l' e1 e2.
induction l in l', e1, e2 |- *.
- destruct l' ; try discriminate. reflexivity.
- destruct l' ; try discriminate.
  simpl in *. inversion e1. inversion e2.
  f_equal ; eauto.
  destruct a, p. simpl in *. subst. reflexivity.
Qed.

Lemma map_inj :
      forall A B (f : A -> B) l l',
        (forall x y, f x = f y -> x = y) ->
        map f l = map f l' ->
        l = l'.
Proof.
  intros A B f l l' h e.
  induction l in l', e |- *.
  - destruct l' ; try discriminate. reflexivity.
  - destruct l' ; try discriminate. inversion e.
    f_equal ; eauto.
Qed.

Lemma rtrans_clos_incl {A} (R S : A -> A -> Type) : 
      (forall x y, R x y -> rtrans_clos S x y) ->
      forall x y, rtrans_clos R x y ->
      rtrans_clos S x y.
Proof.
  intros HR x y h.
  eapply clos_rt_rtn1_iff in h.
  induction h; eauto.
  * econstructor.
  * apply clos_rt_rtn1_iff.
    apply clos_rt_rtn1_iff in IHh1.
    apply clos_rt_rtn1_iff in IHh2.
    now transitivity y.
Qed.

Section Congr1CongrAll.

  Context {Σ : global_env} {R : global_env -> context -> term -> term -> Type}.

  Theorem congr1_congr_all Γ t u :
    (forall Γ, Reflexive (R Σ Γ)) ->
    congr1 R Σ Γ t u -> congr_all (fun Σ Γ Γ' => R Σ Γ) eq eq Σ Γ Γ t u.
  Proof.
    intros rR.
    assert (forall Γ, context -> Reflexive (R Σ Γ)) by (intros ; apply rR).
    induction 1 using congr1_ind_all.

    all: try solve [constructor ; auto ; reflexivity].

    - constructor.
      + repeat split.
        2: reflexivity.
        eapply OnOne2_All2 ; tea.
        2: reflexivity.
        by intros ? ? [].
      + reflexivity.
      + apply All2_same.
        intros ; split.
        all: reflexivity.

    - constructor.
      + repeat split.
        1: apply All2_same ; reflexivity.
        assumption.
      + reflexivity.
      + apply All2_same.
        intros ; split.
        all: reflexivity.
    
    - constructor.
      + repeat split.
        1: apply All2_same ; reflexivity.
        reflexivity.
      + assumption.
      + apply All2_same.
        intros ; split.
        all: reflexivity.
        
    - constructor.
      + repeat split.
      1: apply All2_same ; reflexivity.
      reflexivity.
      + reflexivity.
      + eapply OnOne2_All2 ; tea.
        2: split ; reflexivity.
        1: intros ? ? ((?&?)&?) ; split ; auto.
        suff -> : (inst_case_branch_context p y = inst_case_branch_context p x) by assumption.
        by rewrite /inst_case_branch_context e.

    - constructor.
      eapply OnOne2_All2 ; tea.
      2: reflexivity.
      by intros ? ? [].

    - constructor.
      eapply OnOne2_All2 ; tea.
      2: repeat split ; reflexivity.
      intros ? ? ((?&?)&e).
      inversion e ; clear e.
      repeat split.
      2: reflexivity.
      assumption.

    - constructor.
      eapply OnOne2_All2 ; tea.
      2: repeat split ; reflexivity.
      intros ? ? ((?&?)&e).
      inversion e ; clear e.
      repeat split.
      1: reflexivity.
      rewrite -(fix_context_eq mfix mfix') //.
      eapply OnOne2_All2 ; tea.
      2: reflexivity.
      intros ? ? [? e].
      by inversion e.

    - constructor.
      eapply OnOne2_All2 ; tea.
      2: repeat split ; reflexivity.
      intros ? ? ((?&?)&e).
      inversion e ; clear e.
      repeat split.
      2: reflexivity.
      assumption.

    - constructor.
      eapply OnOne2_All2 ; tea.
      2: repeat split ; reflexivity.
      intros ? ? ((?&?)&e).
      inversion e ; clear e.
      repeat split.
      1: reflexivity.
      rewrite -(fix_context_eq mfix mfix') //.
      eapply OnOne2_All2 ; tea.
      2: reflexivity.
      intros ? ? [? e].
      by inversion e.
  Qed.

  Lemma congr_all_one_param Γ ci p c brs pars' :
    OnOne2 ((clos_refl_trans (congr1 R Σ Γ))) p.(pparams) pars' ->
    (clos_refl_trans (congr1 R Σ Γ)) (tCase ci p c brs) (tCase ci (set_pparams p pars') c brs).
  Proof.
    intros.
    apply congr1_clos_refl_trans.
    constructor.
    eapply OnOne2_impl ; tea.
    by constructor.
  Qed.

  Lemma congr_all_case_pars Γ ci p c brs pars' :
    All2 ((clos_refl_trans (congr1 R Σ Γ))) p.(pparams) pars' ->
    (clos_refl_trans (congr1 R Σ Γ)) (tCase ci p c brs) (tCase ci (set_pparams p pars') c brs).
  Proof.
    intros h.
    apply All2_many_OnOne2 in h.
    induction h.
    - destruct p; reflexivity.
    - econstructor 3.
      + eapply IHh.
      + assert (set_pparams p z = set_pparams (set_pparams p y) z) as ->
        by now destruct p.
        eapply congr_all_one_param; eassumption.
  Qed.

  Lemma congr_all_case_one_brs Γ (ci : case_info) p c brs brs' :
    OnOne2 (fun br br' => 
      let ctx := inst_case_branch_context p br in
      on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, ctx))) bbody bcontext br br')
    brs brs' ->
    clos_refl_trans (congr1 R Σ Γ) (tCase ci p c brs) (tCase ci p c brs').
    Proof.
      intros.
      apply congr1_clos_refl_trans.
      constructor.
      eapply OnOne2_impl ; tea.
      intros ? ? [].
      split.
      2: assumption.
      by constructor.
    Qed.

  Lemma congr_all_case_brs Γ ci p c brs brs' :
    All2 (fun br br' => 
      let ctx := inst_case_branch_context p br in
      on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, ctx))) bbody bcontext br br')
    brs brs' ->
    clos_refl_trans (congr1 R Σ Γ) (tCase ci p c brs) (tCase ci p c brs').
  Proof.
    intros h.
    eapply All2_many_OnOne2 in h.
    induction h; trea.
    etransitivity.
    1: eapply IHh.
    eapply congr_all_case_one_brs; eauto.
  Qed.

  Lemma congr_all_fix_one_ty Γ mfix idx mfix' :
    OnOne2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ Γ))
        dtype (fun x => (dname x, dbody x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tFix mfix idx) (tFix mfix' idx).
  Proof.
    intros h.
    apply congr1_clos_refl_trans.
    constructor.
    eapply OnOne2_impl ; tea.
    intros ? ? [].
    split.
    2: assumption.
    by constructor.
  Qed.

  Lemma congr_all_fix_ty Γ mfix idx mfix' :
    All2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ Γ))
        dtype (fun x => (dname x, dbody x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tFix mfix idx) (tFix mfix' idx).
  Proof.
    intros h.
    apply All2_many_OnOne2 in h.
    induction h.
    - reflexivity.
    - etransitivity ; tea.
      by eapply congr_all_fix_one_ty.
  Qed.

  Lemma congr_all_fix_one_body Γ mfix idx mfix' :
    OnOne2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, fix_context mfix)))
        dbody (fun x => (dname x, dtype x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tFix mfix idx) (tFix mfix' idx).
  Proof.
    intros h.
    apply congr1_clos_refl_trans.
    apply congr1_fix_body.
    eapply OnOne2_impl ; tea.
    intros ? ? [].
    split.
    2: assumption.
    by constructor.
  Qed.

  Lemma congr_all_fix_body Γ mfix idx mfix' :
    All2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, fix_context mfix)))
      dbody (fun x => (dname x, dtype x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tFix mfix idx) (tFix mfix' idx).
  Proof.
    intros h.
    apply All2_many_OnOne2 in h.
    induction h.
    - reflexivity.
    - etransitivity ; tea.
      eapply congr_all_fix_one_body.
      suff -> : fix_context y = fix_context mfix.
      {
        eapply OnOne2_impl ; tea.
        intros ? ? [].
        auto.
      }
      symmetry.
      clear -h.
      induction h.
      1: reflexivity.
      etransitivity ; tea.
      apply OnOne2_prod_inv in r as [] => //.
      apply fix_context_eq.
      eapply OnOne2_All2 ; tea.
      2: reflexivity.
      intros ? ? e.
      by inversion e.
  Qed.

  Lemma congr_all_cofix_one_ty Γ mfix idx mfix' :
    OnOne2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ Γ))
        dtype (fun x => (dname x, dbody x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tCoFix mfix idx) (tCoFix mfix' idx).
  Proof.
    intros h.
    apply congr1_clos_refl_trans.
    constructor.
    eapply OnOne2_impl ; tea.
    intros ? ? [].
    split.
    2: assumption.
    by constructor.
  Qed.

  Lemma congr_all_cofix_ty Γ mfix idx mfix' :
    All2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ Γ))
        dtype (fun x => (dname x, dbody x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tCoFix mfix idx) (tCoFix mfix' idx).
  Proof.
    intros h.
    apply All2_many_OnOne2 in h.
    induction h.
    - reflexivity.
    - etransitivity ; tea.
      by eapply congr_all_cofix_one_ty.
  Qed.

  Lemma congr_all_cofix_one_body Γ mfix idx mfix' :
    OnOne2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, fix_context mfix)))
        dbody (fun x => (dname x, dtype x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tCoFix mfix idx) (tCoFix mfix' idx).
  Proof.
    intros h.
    apply congr1_clos_refl_trans.
    apply congr1_cofix_body.
    eapply OnOne2_impl ; tea.
    intros ? ? [].
    split.
    2: assumption.
    by constructor.
  Qed.

  Lemma congr_all_cofix_body Γ mfix idx mfix' :
    All2
      (on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, fix_context mfix)))
      dbody (fun x => (dname x, dtype x, rarg x)))
    mfix mfix' ->
    clos_refl_trans (congr1 R Σ Γ) (tCoFix mfix idx) (tCoFix mfix' idx).
  Proof.
    intros h.
    apply All2_many_OnOne2 in h.
    induction h.
    - reflexivity.
    - etransitivity ; tea.
      eapply congr_all_cofix_one_body.
      suff -> : fix_context y = fix_context mfix.
      {
        eapply OnOne2_impl ; tea.
        intros ? ? [].
        auto.
      }
      symmetry.
      clear -h.
      induction h.
      1: reflexivity.
      etransitivity ; tea.
      apply OnOne2_prod_inv in r as [] => //.
      apply fix_context_eq.
      eapply OnOne2_All2 ; tea.
      2: reflexivity.
      intros ? ? e.
      by inversion e.
  Qed.

  Theorem congr_all_clos_refl_trans Γ t u :
    congr_all (fun Σ' Γ' _ => (clos_refl_trans (congr1 R Σ' Γ'))) eq eq Σ Γ Γ t u ->
    clos_refl_trans (congr1 R Σ Γ) t u.
  Proof.
    generalize Γ at 2.
    intros Γ'.
    induction 1 using congr_all_ind_all.

    all: try solve
      [subst ; etransitivity ; apply congr1_clos_refl_trans ; do 2 constructor ; eassumption].

    - apply All2_many_OnOne2 in X.
      induction X.
      1: reflexivity.
      etransitivity ; tea.
      apply OnOne2_split in r as (?&?&?&?&(IH&_)&?&?).
      subst.
      clear - IH.
      rst_induction IH ; tea.
      constructor.
      apply OnOne2_app.
      by constructor.
   
    - subst.
      do 2 etransitivity.
      all: apply congr1_clos_refl_trans ; do 2 constructor ; eassumption.
      
    - destruct X as (?&?&?&?&?).
      do 2 etransitivity.
      + apply congr_all_case_brs.
        eapply All2_impl ; tea.
        intros ? ? ((?&?)&?).
        split ; auto.
      + apply congr1_clos_refl_trans.
        eapply congr1_case_discr.
        constructor.
        eassumption.
      + apply congr1_clos_refl_trans.
        eapply congr1_case_return.
        constructor.
        eassumption.
      + replace p' with (set_pparams (set_preturn p (preturn p')) (pparams p'))
          by (destruct p, p' ; cbn ; rewrite /set_pparams /set_preturn /= ; by f_equal).
        apply congr_all_case_pars.
        eapply All2_impl ; tea.
        intros ? ? [].
        auto.      

    - assert (∑ mfix'',
      All2 (
        on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, fix_context mfix))) dbody
                  (fun x : def term => (dname x, dtype x, rarg x))
      ) mfix mfix'' ×
      All2 (
        on_Trel_eq (clos_refl_trans (congr1 R Σ Γ)) dtype
                  (fun x : def term => (dname x, dbody x, rarg x))
      ) mfix'' mfix') as [mfix'' []].
      { revert X.
        generalize dependent (Γ ,,, fix_context mfix).
        intros Δ h.
        induction h.
        - exists []. auto.
        - destruct r as (?&?&?&?&?&?).
          destruct IHh as [mfix'' [? ?]].
          eexists (mkdef _ _ _ _ _ :: mfix''). split.
          + constructor ; auto. simpl. split ; tea. reflexivity.
          + constructor ; auto. simpl. split ; eauto.
            f_equal ; auto.
            f_equal ; auto.
      }
      transitivity (tFix mfix'' idx).
      + apply congr_all_fix_body.
        eapply All2_impl ; tea.
        intros ? ? [].
        split ; auto.
      + apply congr_all_fix_ty.
        eapply All2_impl ; tea.
        intros ? ? [].
        split ; auto.
        
    - assert (∑ mfix'',
      All2 (
        on_Trel_eq (clos_refl_trans (congr1 R Σ (Γ ,,, fix_context mfix))) dbody
                  (fun x : def term => (dname x, dtype x, rarg x))
      ) mfix mfix'' ×
      All2 (
        on_Trel_eq (clos_refl_trans (congr1 R Σ Γ)) dtype
                  (fun x : def term => (dname x, dbody x, rarg x))
      ) mfix'' mfix') as [mfix'' []].
      { revert X.
        generalize dependent (Γ ,,, fix_context mfix).
        intros Δ h.
        induction h.
        - exists []. auto.
        - destruct r as (?&?&?&?&?&?).
          destruct IHh as [mfix'' [? ?]].
          eexists (mkdef _ _ _ _ _ :: mfix''). split.
          + constructor ; auto. simpl. split ; tea. reflexivity.
          + constructor ; auto. simpl. split ; eauto.
            f_equal ; auto.
            f_equal ; auto.
      }
      transitivity (tCoFix mfix'' idx).
      + apply congr_all_cofix_body.
        eapply All2_impl ; tea.
        intros ? ? [].
        split ; auto.
      + apply congr_all_cofix_ty.
        eapply All2_impl ; tea.
        intros ? ? [].
        split ; auto.

    - assumption.

  Qed.

  Corollary congr_all_mkApps Γ u u' l l' :
    clos_refl_trans (congr1 R Σ Γ) u u' ->
    All2 (clos_refl_trans (congr1 R Σ Γ)) l l' ->
    clos_refl_trans (congr1 R Σ Γ) (mkApps u l) (mkApps u' l').
  Proof.
    intros h ha.
    induction ha in u, u', h |- *.
    1: auto.
    cbn.
    apply IHha.
    apply congr_all_clos_refl_trans.
    by do 2 constructor.
  Qed.

  Corollary congr_all_it_mkLambda_or_LetIn Γ Δ Δ' u u' :
    All2_fold (fun Δ _ => on_one_decl
      (fun Δ : context => clos_refl_trans (congr1 R Σ (Γ ,,, Δ))) Δ) Δ Δ' ->
    clos_refl_trans (congr1 R Σ (Γ ,,, Δ)) u u' ->
    (clos_refl_trans (congr1 R Σ Γ)) (it_mkLambda_or_LetIn Δ u) (it_mkLambda_or_LetIn Δ' u').
  Proof.
  intros h h'.
  induction h in u, u', h' |- *.
  1: auto.
  inversion p ; subst.
  - cbn. apply IHh ; auto.
    apply congr_all_clos_refl_trans.
    constructor ; auto.
    all: constructor ; auto.
  - cbn. apply IHh ; auto.
    apply congr_all_clos_refl_trans.
    constructor ; auto.
    all: constructor ; auto.
  - cbn. apply IHh ; auto.
    apply congr_all_clos_refl_trans.
    constructor ; auto.
    all: constructor ; auto.
  Qed.

  Corollary congr_all_it_mkProd_or_LetIn Γ Δ Δ' u u' :
    All2_fold (fun Δ _ => on_one_decl
      (fun Δ : context => clos_refl_trans (congr1 R Σ (Γ ,,, Δ))) Δ) Δ Δ' ->
    clos_refl_trans (congr1 R Σ (Γ ,,, Δ)) u u' ->
    (clos_refl_trans (congr1 R Σ Γ)) (it_mkProd_or_LetIn Δ u) (it_mkProd_or_LetIn Δ' u').
  Proof.
    intros h h'.
    induction h in u, u', h' |- *.
    1: auto.
    inversion p ; subst.
    - cbn. apply IHh ; auto.
      apply congr_all_clos_refl_trans.
      constructor ; auto.
      all: constructor ; auto.
    - cbn. apply IHh ; auto.
      apply congr_all_clos_refl_trans.
      constructor ; auto.
      all: constructor ; auto.
    - cbn. apply IHh ; auto.
      apply congr_all_clos_refl_trans.
      constructor ; auto.
      all: constructor ; auto.
  Qed.
      
End Congr1CongrAll.

Coercion ci_ind : case_info >-> inductive.

Lemma nth_error_firstn_skipn {A} {l : list A} {n t} : 
  nth_error l n = Some t -> 
  l = firstn n l ++ [t] ++ skipn (S n) l.
Proof. induction l in n |- *; destruct n; simpl; try congruence.
  intros. specialize (IHl _ H).
  now simpl in IHl.
Qed.

Lemma split_nth {A B} {l : list A} (l' l'' : list B) :
  (#|l| = #|l'| + S (#|l''|))%nat ->
  ∑ x, (nth_error l #|l'| = Some x) * (l = firstn #|l'| l ++ x :: skipn (S #|l'|) l).
Proof.
  induction l in l', l'' |- *; simpl; auto.
  - rewrite Nat.add_succ_r //.
  - rewrite Nat.add_succ_r => [= len].
    destruct l'; simpl.
    * exists a; auto.
    * simpl in len. rewrite -Nat.add_succ_r in len.
      specialize (IHl _ _ len) as [x eq].
      exists x; now f_equal.
Qed.

Lemma nth_error_map2 {A B C} (f : A -> B -> C) (l : list A) (l' : list B) n x : 
  nth_error (map2 f l l') n = Some x ->
  ∑ lx l'x, (nth_error l n = Some lx) *
    (nth_error l' n = Some l'x) * 
    (f lx l'x = x).
Proof.
  induction l in l', n, x |- *; destruct l', n; simpl; auto => //.
  intros [= <-].
  eexists _, _; intuition eauto.
Qed.

(* TODO Find a better place for this. *)
Section Stacks.

  Context (Σ : global_env_ext).
  Context `{checker_flags}.

  Lemma congr_all_zipp R Γ t u π :
    clos_refl_trans (congr1 R Σ Γ) t u ->
    clos_refl_trans (congr1 R Σ Γ) (zipp t π) (zipp u π).
  Proof.
    intros h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    apply congr_all_mkApps.
    1: assumption.
    apply All2_same.
    reflexivity.
  Qed.

  Lemma congr_all_zippx R Γ t u π :
    clos_refl_trans (congr1 R Σ (Γ,,, stack_context π)) t u ->
    clos_refl_trans (congr1 R Σ Γ) (zippx t π) (zippx u π).
  Proof.
    intros h.
    unfold zippx.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    apply congr_all_it_mkLambda_or_LetIn.
    1: apply All2_fold_refl, on_one_decl_refl.
    1: intros ; apply clos_rt_refl.
    apply congr_all_mkApps.
    1: erewrite <- stack_context_appstack ; eassumption.
    apply All2_same.
    reflexivity.
  Qed.

End Stacks.
