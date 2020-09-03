(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst
  Environment.
From MetaCoq.PCUIC Require Import PCUICUtils.
From MetaCoq.EGCIC Require Import EGCICAst.
From MetaCoq.EGCIC Require EGCICTyping.
From MetaCoq.EGCIC Require Import EGCICConversion.
From MetaCoq.GCIC Require Import GCICAst.
From MetaCoq.GCIC Require Import GCICAstUtils GCICLiftSubst
  GCICUnivSubst GCICEquality GCICPosition GCICEnvironmentTyping.
From MetaCoq.GCIC Require Import PairTerms.

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

(** * Typing derivations

  Inductive relations for reduction, conversion and typing of PCUIC terms.
  These come with many additional functions, to define the reduction operations,
  deal with arities, declarations in the environment etc...

 *)

(* Definition isSort T :=
  match T with
  | tSort u => True
  | _ => False
  end.

Fixpoint isArity T :=
  match T with
  | tSort u => True
  | tProd _ _ codom => isArity codom
  | tLetIn _ _ _ codom => isArity codom
  | _ => False
  end.
 *)

Definition subst_context (s : list pterm) k (Γ : context) : context :=
  fold_context (fun k' => psubst s (k' + k)) Γ.

Lemma subst_context_length s n Γ : #|subst_context s n Γ| = #|Γ|.
Proof.
  induction Γ as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
  - rewrite !List.rev_length !mapi_length !app_length !List.rev_length. simpl.
    lia.
  - rewrite !List.rev_length !mapi_length !app_length !List.rev_length. simpl.
    lia.
Qed.

Definition lift_context (n k : nat) (Γ : context) : context :=
  fold_context (fun k' : nat => plift n (k' + k)) Γ.

Definition subst_telescope (s : list pterm) (k : nat) (Γ : context) :=
  mapi (fun k' x => map_decl (psubst s (k + k')) x) Γ.

Fixpoint smash_context (Γ Γ' : context) : context :=
  match Γ' with
  | {| decl_body := Some b |} :: Γ' => smash_context (subst_context [b] 0 Γ) Γ'
  | {| decl_body := None |} as d :: Γ' => smash_context (Γ ++ [d])%list Γ'
  | [] => Γ
  end.

Lemma smash_context_length Γ Γ' : #|smash_context Γ Γ'| = #|Γ| + context_assumptions Γ'.
Proof.
  induction Γ' as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
  - now rewrite IHtl subst_context_length.
  - rewrite IHtl app_length. simpl. lia.
Qed.

(** Inductive substitution, to produce a constructors' type *)
Definition inds ind u (l : list G.one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => G.gInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
Qed.

Lemma inds_spec ind u l :
  inds ind u l = List.rev (mapi (fun i _ => G.gInd {| inductive_mind := ind; inductive_ind := i |} u) l).
Proof.
  unfold inds, mapi. induction l using rev_ind. simpl. reflexivity.
  now rewrite app_length /= Nat.add_1_r IHl mapi_rec_app /= rev_app_distr /= Nat.add_0_r.
Qed.

Definition type_of_constructor mdecl (cdecl : ident * G.term * nat) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(G.ind_bodies)) (subst_instance_constr u (snd (fst cdecl))).


(** ** Utilities for typing *)

(** Decompose an arity into a context and a sort *)

Fixpoint pdecompose_prod_assum_aux (Γ : context) (et : E.term) (gt : G.term) : context × pterm :=
  match et , gt with
  | E.eProd na et eb , G.gProd _ gt gb =>
        pdecompose_prod_assum_aux (Γ ,, vass na {| eterm := et ; gterm := gt |}) eb gb
  | E.eLetIn na eb eb_ty eb' , G.gLetIn _ gb gb_ty gb' =>
      pdecompose_prod_assum_aux (Γ ,, vdef na {| eterm := eb ; gterm := gb |} {| eterm := eb_ty ; gterm := gb_ty |}) eb' gb'
  | _ , _ => (Γ,{| eterm := et ; gterm := gt |})
  end.

Definition pdecompose_prod_assum Γ t := pdecompose_prod_assum_aux Γ t.(eterm) t.(gterm).

Definition destArity t :=
let '(Γ,t') := pdecompose_prod_assum [] t in
  match t' with
  | {|eterm := E.eSort es ; gterm := G.gSort gs |} => if (Universe.eqb es gs) then Some (Γ, es) else None
  | _ => None
  end.

(* Fixpoint destArity_aux (Γ : context) (et : E.term) (gt : G.term) : option (context × Universe.t) :=
  match et , gt with
  | E.eProd na et eb , G.gProd _ gt gb =>
        destArity_aux (Γ ,, vass na {| eterm := et ; gterm := gt |}) eb gb
  | E.eLetIn na eb eb_ty eb' , G.gLetIn _ gb gb_ty gb' =>
      destArity_aux (Γ ,, vdef na {| eterm := eb ; gterm := gb |} {| eterm := eb_ty ; gterm := gb_ty |}) eb' gb'
  | E.eSort es , G.gSort gs => if (Universe.eqb es gs) then Some (Γ, es) else None
  | _ , _ => None
  end.

Definition destArity t := destArity_aux [] t.(eterm) t.(gterm). *)

Lemma pdecompose_prod_assum_app {Γ Γ' t}
  : pdecompose_prod_assum (Γ ,,, Γ') t = (fun '(ctx, s) => (Γ ,,, ctx, s)) (pdecompose_prod_assum Γ' t).
Proof.
  destruct t as [et gt].
  revert Γ' gt.
  induction et; intros Γ' gt ; case gt ; cbn; try reflexivity.
  - intros ; rewrite <- app_context_cons ; now eapply IHet2.
  - intros ; rewrite <- app_context_cons ; now eapply IHet3.
Qed.

(* Lemma destArity_app {Γ t}
  : destArity_aux Γ t.(eterm) t.(gterm) = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                               (destArity t).
Proof.
  exact (@destArity_app_aux Γ [] t.(eterm) t.(gterm)).
Qed.

Lemma destArity_app_Some {Γ t ctx s}
  : destArity_aux Γ t.(eterm) t.(gterm) = Some (ctx, s)
    -> ∑ ctx', destArity t = Some (ctx', s) /\ ctx = Γ ,,, ctx'.
Proof.
  intros H. rewrite destArity_app in H.
  destruct (destArity t) as [[ctx' s']|]; cbn in *.
  exists ctx'. inversion H. now subst.
  discriminate H.
Qed. *)

Lemma pdecompose_it_mkProd_or_LetIn Γ Γ' t :
  pdecompose_prod_assum Γ (it_mkProd_or_LetIn Γ' t) =
    (fun '(Γ'', s) => (Γ ,,, Γ'', s)) (pdecompose_prod_assum Γ' t).
Proof.
  induction Γ' in t |- * ; simpl.
  - by rewrite <- pdecompose_prod_assum_app.
  - rewrite IHΓ'. destruct a as [na [[]|] []] ; cbn ; reflexivity.
Qed.

Lemma destArity_it_mkProd_or_LetIn_aux Γ t :
  destArity (it_mkProd_or_LetIn Γ t) = option_map (fun '(Γ', s) => (Γ ,,, Γ', s)) (destArity t).
Proof.
  rewrite /destArity pdecompose_it_mkProd_or_LetIn.
  change Γ with (Γ ,,, []) at 1.
  rewrite pdecompose_prod_assum_app.
  destruct (pdecompose_prod_assum [] t) as [? [[] []]] ; try reflexivity.
  destruct (Universe.eqb u u0) ; simpl ; try reflexivity.
  by rewrite app_context_nil_l.
Qed.

Lemma mkApps_nonempty f l :
  l <> [] -> pmkApps f l = pApp (pmkApps f (removelast l)) (last l f).
Proof.
  destruct l using rev_ind. intros; congruence.
  rewrite /pApp /pmkApps ET.mkApps_nonempty.
  1: apply map_nil ; destruct l ; simpl ; congruence.
  intros.
  rewrite !map_app !removelast_app //= !map_app !last_app //= !app_nil_r.
  rewrite <- mkApps_nested. simpl. f_equal.
Qed.

(* Lemma destArity_tFix {mfix idx args} :
  destArity (pmkApps (tFix mfix idx) args) = None.
Proof.
  induction args. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed. *)

Lemma destArity_pApp {t u l} :
  destArity (pmkApps (pApp t u) l) = None.
Proof.
  induction l. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.

Lemma destArity_pInd {t u l} :
  destArity (pmkApps (pInd t u) l) = None.
Proof.
  induction l. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.


Reserved Notation " Σ ;;; Γ |- t ▹ T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t ▸□ u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t ▸Π ( na , A , B ) " (at level 50, Γ, t, na, A, B at next level).
Reserved Notation " Σ ;;; Γ |- t ▸{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
Reserved Notation " Σ ;;; Γ |- t ◃ T " (at level 50, Γ, t, T at next level).


(** ** Typing relation *)

Section TypingAux.
  Context (checking : forall (Σ : global_env_ext) (Γ : context), pterm -> pterm -> Type).

  Definition isWfArity (Σ : global_env_ext) (Γ : context) (T : pterm) :=
     { ctx : context &
        { s & (destArity T = Some (ctx, s)) × All_local_env_rel (lift_typing checking Σ) Γ ctx } }.

        Context (property : forall (Σ : global_env_ext) (Γ Γ' : context),
              All_local_env_rel (lift_typing checking Σ) Γ Γ' ->
              forall (t T : pterm), checking Σ (Γ,,,Γ') t T -> Type).

  Definition isWfArity_prop Σ (Γ : context) (T : pterm) :=
     { wfa : isWfArity Σ Γ T & All_local_env_over_rel checking property Σ _ _ (snd (projT2 (projT2 wfa))) }.

 End TypingAux.
 
(* AXIOM GUARD CONDITION *)
(*Axiom fix_guard : mfixpoint term -> bool.

Axiom fix_guard_red1 :
  forall Σ Γ mfix mfix' idx,
    fix_guard mfix ->
    red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) ->
    fix_guard mfix'.

Axiom fix_guard_eq_term :
  forall mfix mfix' idx,
    fix_guard mfix ->
    upto_names (tFix mfix idx) (tFix mfix' idx) ->
    fix_guard mfix'.

Axiom fix_guard_rename :
  forall mfix f,
    let mfix' :=
        map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix
    in
    fix_guard mfix ->
    fix_guard mfix'.

Axiom fix_guard_lift :
  forall mfix n k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (lift n k) (lift n k')) mfix in
    fix_guard mfix ->
    fix_guard mfix'.

Axiom fix_guard_subst :
  forall mfix s k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    fix_guard mfix ->
    fix_guard mfix'.

(* AXIOM INDUCTIVE GUARD CONDITION *)
Axiom ind_guard : mutual_inductive_body -> bool. *)


(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Fixpoint pinstantiate_params_subst (params : context) (pars : list pterm) (s : list pterm) (ty : pterm) :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None (* Too many arguments to substitute *)
          end
  | d :: params =>
    match d.(decl_body), ty with
    | None, {|eterm := E.eProd _ _ eB ; gterm := G.gProd _ _ gB |}  =>
      match pars with
      | hd :: tl => pinstantiate_params_subst params tl (hd :: s) {|eterm := eB ; gterm := gB |}
      | [] => None (* Not enough arguments to substitute *)
      end
    | Some b, {| eterm := E.eLetIn _ _ _ eb' ; gterm := G.gLetIn _ _ _ gb' |} =>
        pinstantiate_params_subst params pars (psubst0 s b :: s) {| eterm := eb' ; gterm := gb' |}
    | _, _ => None (* Not enough products in the type *)
    end
  end.

Fixpoint instantiate_params_subst (params : G.context) (pars : list G.term) (s : list G.term) (ty : G.term) :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None (* Too many arguments to substitute *)
          end
  | d :: params =>
    match d.(G.decl_body), ty with
    | None, G.gProd _ _ gB  =>
      match pars with
      | hd :: tl => instantiate_params_subst params tl (hd :: s) gB
      | [] => None (* Not enough arguments to substitute *)
      end
    | Some b, G.gLetIn _ _ _ gb' =>
        instantiate_params_subst params pars (subst0 s b :: s) gb'
    | _, _ => None (* Not enough products in the type *)
    end
  end.

(* If [ty] is [Π params . B] *)
(* and [⊢ pars : params] *)
(* then [instantiate_params] is [B{pars}] *)

Definition pinstantiate_params (params : context) (pars : list pterm) (ty : pterm) : option pterm :=
  match pinstantiate_params_subst (List.rev params) pars [] ty with
  | Some (s, ty) => Some (psubst0 s ty)
  | None => None
  end.

Definition instantiate_params (params : G.context) (pars : list G.term) (ty : G.term) : option G.term :=
  match instantiate_params_subst (List.rev params) pars [] ty with
  | Some (s, ty) => Some (subst0 s ty)
  | None => None
  end.

Lemma instantiate_params_ params pars ty :
  pinstantiate_params params pars ty
  = option_map (fun '(s, ty) => psubst0 s ty)
               (pinstantiate_params_subst (List.rev params) pars [] ty).
Proof.
  unfold pinstantiate_params.
  repeat (destruct ?; cbnr).
Qed.

(* [params] and output already instanciated by [u] *)
Definition build_case_predicate_type ind mdecl idecl (params : list pterm) u ps : option pterm :=
  X <- pinstantiate_params (psubst_instance_context u (ind_params mdecl)) params
                         (psubst_instance_constr u (ind_type idecl)) ;;
  X <- destArity X ;;
  let inddecl :=
      {| decl_name := nNamed idecl.(ind_name);
         decl_body := None;
         decl_type := pmkApps (pInd ind u) (map (plift0 #|X.1|) params ++ to_extended_list X.1) |} in
  ret (it_mkProd_or_LetIn (X.1 ,, inddecl) (pSort ps)).


(* [params], [p] and output are already instanciated by [u] *)
Definition build_branches_type ind mdecl idecl params u p : list (option (nat × G.term)) :=
  let inds := inds ind.(inductive_mind) u mdecl.(G.ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance_constr u t) in
    match instantiate_params (subst_instance_context u mdecl.(G.ind_params)) params ty with
    | Some ty =>
      let '(sign, ccl) := decompose_prod_assum [] ty in
      let nargs := List.length sign in
      let allargs := snd (decompose_app ccl) in
      let '(paramrels, args) := chop mdecl.(G.ind_npars) allargs in
      let cstr := G.gConstruct ind i u in
      let args := (args ++ [G.mkApps cstr (paramrels ++ G.to_extended_list sign)])%list in
      Some (ar, G.it_mkProd_or_LetIn sign (G.mkApps (lift0 nargs p) args))
    | None => None
    end
  in mapi branch_type idecl.(G.ind_ctors).

Lemma build_branches_type_ ind mdecl idecl params u p :
  build_branches_type ind mdecl idecl params u p
  = let inds := inds ind.(inductive_mind) u mdecl.(G.ind_bodies) in
    let branch_type i '(id, t, ar) :=
        let ty := subst0 inds (subst_instance_constr u t) in
        option_map (fun ty =>
         let '(sign, ccl) := decompose_prod_assum [] ty in
         let nargs := List.length sign in
         let allargs := snd (decompose_app ccl) in
         let '(paramrels, args) := chop mdecl.(G.ind_npars) allargs in
         let cstr := G.gConstruct ind i u in
         let args := (args ++ [G.mkApps cstr (paramrels ++ G.to_extended_list sign)])%list in
         (ar, G.it_mkProd_or_LetIn sign (G.mkApps (lift0 nargs p) args)))
                  (instantiate_params (subst_instance_context u mdecl.(G.ind_params))
                                      params ty)
    in mapi branch_type idecl.(G.ind_ctors).
Proof.
  apply mapi_ext. intros ? [[? ?] ?]; cbnr.
  repeat (destruct ?; cbnr).
Qed.

Inductive infering `{checker_flags} (Σ : global_env_ext) (Γ : context) : pterm -> pterm -> Type :=
| infer_Rel n decl :
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- {| eterm := E.eRel n ; gterm := G.gRel n |} ▹ plift0 (S n) decl.(decl_type)

| infer_Sort l :
    LevelSet.In l (global_ext_levels Σ) ->
    Σ ;;; Γ |- {| eterm := E.eSort (Universe.make l) ; gterm := G.gSort (Universe.make l) |}
      ▹ {| eterm := E.eSort (Universe.super l) ; gterm := G.gSort (Universe.super l) |}

| infer_Prod na A B s1 s2 :
    Σ ;;; Γ |- A ▸□ s1 ->
    Σ ;;; Γ ,, vass na A |- B ▸□ s2 ->
    Σ ;;; Γ |- {| eterm := E.eProd na A.(eterm) B.(eterm) ; gterm := G.gProd na A.(gterm) B.(gterm) |}
      ▹ {| eterm := E.eSort (Universe.sort_of_product s1 s2) ; gterm := G.gSort (Universe.sort_of_product s1 s2) |}

| infer_Lambda na A t s B :
    Σ ;;; Γ |- A ▸□ s ->
    Σ ;;; Γ ,, vass na A |- t ▹ B ->
    Σ ;;; Γ |- {| eterm := E.eLambda na A.(eterm) t.(eterm) ; gterm := G.gLambda na A.(gterm) t.(gterm) |}
      ▹ {| eterm := E.eProd na A.(eterm) B.(eterm) ; gterm := G.gProd na A.(gterm) B.(gterm) |}

| infer_LetIn na b B t s A :
    Σ ;;; Γ |- B ▸□ s ->
    Σ ;;; Γ |- b ◃ B ->
    Σ ;;; Γ ,, vdef na b B |- t ▹ A ->
    Σ ;;; Γ |- {| eterm := E.eLetIn na b.(eterm) B.(eterm) t.(eterm) ; gterm := G.gLetIn na b.(gterm) B.(gterm) t.(gterm) |}
      ▹ {| eterm := E.eLetIn na b.(eterm) B.(eterm) A.(eterm) ; gterm := G.gLetIn na b.(gterm) B.(gterm) A.(gterm) |}

| infer_App t na A B u :
    Σ ;;; Γ |- t ▸Π (na,A,B) ->
    Σ ;;; Γ |- u ◃ A ->
    Σ ;;; Γ |- {| eterm := E.eApp t.(eterm) u.(eterm) ; gterm := G.gApp t.(gterm) u.(gterm) |}
      ▹ psubst10 u B

| infer_Const cst u :
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- {| eterm := E.eConst cst u ; gterm := G.gConst cst u |} ▹ psubst_instance_constr u decl.(cst_type)

| infer_Ind ind u :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- {| eterm := E.eInd ind u ; gterm := G.gInd ind u |} ▹ psubst_instance_constr u idecl.(ind_type)

| infer_Construct ind i u :
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- {| eterm := E.eConstruct ind i u ; gterm := G.gConstruct ind i u |}
      ▹ {| eterm := ET.type_of_constructor mdecl (on_pi2 eterm cdecl) (ind, i) u ;
           gterm := type_of_constructor mdecl (on_pi2 gterm cdecl) (ind, i) u |}

| infer_Case (indnpar : inductive × nat) (u : Instance.t) (p c : pterm) (brs : list (nat × pterm)) (args : list pterm):
  let ind := indnpar.1 in
  let npar := indnpar.2 in
  Σ ;;; Γ |- c ▸{ind} (u,args) ->
  forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
  mdecl.(ind_npars) = npar ->
  ET.isCoFinite mdecl.(ind_finite) = false ->
  let params := List.firstn npar args in
  forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
  Σ ;;; Γ |- p ◃ pty ->
  leb_sort_family (universe_family ps) idecl.(ind_kelim) ->
  forall (btys : list (nat × pterm)),
  map_option_out (build_branches_type ind mdecl idecl (map gterm params) u p) = Some (map (on_snd gterm) btys) ->
  All2 (fun br bty =>
    (br.1 = bty.1) ×
    (Σ ;;; Γ |- bty.2 ◃ {| eterm := E.eSort ps ; gterm := G.gSort ps |}) ×
    (Σ ;;; Γ |- br.2 ◃ bty.2))
    brs btys ->
  Σ ;;; Γ |- {| eterm := E.eCase indnpar p c (map (on_snd eterm) brs) ;
                gterm := G.gCase indnpar p c (map (on_snd gterm) brs) |}
    ▹ pmkApps p (skipn npar args ++ [c])

| infer_Proj p c u :
    forall mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) (args : list pterm),
    Σ ;;; Γ |- c ▸{fst (fst p)} (u,args) ->
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- {| eterm := E.eProj p c ; gterm := G.gProj p c |} ▹ psubst0 (c :: List.rev args) (psubst_instance_constr u ty)

| infer_Fix (mfix : mfixpoint pterm) n decl :
    ET.fix_guard (e_mfix mfix) ->
    nth_error mfix n = Some decl ->
    All_local_env (lift_typing checking Σ) (Γ,,,fix_context mfix) ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ plift0 #|fix_context mfix| d.(dtype))
    × (E.isLambda d.(dbody) = true) × (G.isLambda d.(dbody) = true)) mfix ->
    Σ ;;; Γ |- {| eterm := E.eFix (e_mfix mfix) n ; gterm := G.gFix (g_mfix mfix) n |} ▹ decl.(dtype)

| infer_Ukn A u :
    Σ ;;; Γ |- A ▸□ u ->
    Σ ;;; Γ |- {| eterm := E.eErr E.ukn (eterm A) ;
                  gterm := G.gUkn (gterm A) |}
      ▹ A

| infer_Cast t A u :
  Σ ;;; Γ |- A ▸□ u ->
  Σ ;;; Γ |- t ◃ A ->
  Σ ;;; Γ |- {| eterm := t.(eterm) ; gterm := G.gCast A.(gterm) t.(gterm) |} ▹ A

with pchecking_sort `{checker_flags} (Σ : global_env_ext) (Γ : context) : pterm -> Universe.t -> Type :=
| pcheck_sort_Sort t T u :
  Σ ;;; Γ |- t ▹ T ->
  (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> E.eSort u ->
  Σ ;;; Γ |- {| eterm := E.eCast (eterm T) (E.eSort u) (eterm t) ; gterm := gterm t |} ▸□ u

| pcheck_sort_Ukn t T l :
  Σ ;;; Γ |- t ▹ T ->
  (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> E.eErr E.ukn (E.eSort (Universe.super l)) ->
  Σ ;;; Γ |- {| eterm := E.eCast (eterm T) (E.eSort (Universe.make l)) (eterm t) ; gterm := gterm t |} ▸□ (Universe.make l)

with pchecking_prod `{checker_flags} (Σ : global_env_ext) (Γ : context) : pterm -> name -> pterm -> pterm -> Type :=
| pcheck_prod_Prod t T na A B:
  Σ ;;; Γ |- t ▹ T ->
  (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> E.eProd na (eterm A) (eterm B) ->
  isErasure A -> isErasure B ->
  Σ ;;; Γ |- {| eterm := E.eCast (eterm T) (E.eProd na (eterm A) (eterm B)) (eterm t) ; gterm := gterm t |} ▸Π (na,A,B)

| pcheck_prod_Ukn t T u :
  Σ ;;; Γ |- t ▹ T ->
  (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> E.eErr E.ukn (E.eSort u) ->
  Σ ;;; Γ |- {| eterm := E.eCast (eterm T)
                          (E.eProd nAnon (E.eErr E.ukn (E.eSort u)) (E.eErr E.ukn (E.eSort u)))
                          (eterm t) ;
                gterm := gterm t |} ▸Π (nAnon,
              {| eterm := E.eErr E.ukn (E.eSort u) ; gterm := G.gUkn (G.gSort u) |},
              {| eterm := E.eErr E.ukn (E.eSort u) ; gterm := G.gUkn (G.gSort u) |})

with pchecking_ind `{checker_flags} (Σ : global_env_ext) (Γ : context) : inductive -> pterm -> Instance.t -> list pterm -> Type :=
| pcheck_ind_Red ind t T u args:
  Σ ;;; Γ |- t ▹ T ->
  (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> E.mkApps (E.eInd ind u) (map eterm args) ->
  All isErasure args ->
  Σ ;;; Γ |- t ▸{ind} (u,args)

(*TODO: missing case for gradual inductive*)

with checking `{checker_flags} (Σ : global_env_ext) (Γ : context) : pterm -> pterm -> Type :=
| check_Cons t T T' :
  Σ ;;; Γ |- t ▹ T ->
  (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) ~~ (eterm T') ->
  Σ ;;; Γ |- {| eterm := E.eCast (eterm T) (eterm T') (eterm t) ; gterm := gterm t |} ◃ T'

where " Σ ;;; Γ |- t ▹ T " := (@infering _ Σ Γ t T) : type_scope
and " Σ ;;; Γ |- t ▸□ u " := (@pchecking_sort _ Σ Γ t u) : type_scope
and " Σ ;;; Γ |- t ▸Π ( na , A , B ) " := (@pchecking_prod _ Σ Γ t na A B) : type_scope
and " Σ ;;; Γ |- t ▸{ ind } ( u , args ) " := (@pchecking_ind _ Σ Γ ind t u args) : type_scope
and " Σ ;;; Γ |- t ◃ T " := (@checking _ Σ Γ t T) : type_scope.

Notation wf_local Σ Γ := (All_local_env (lift_typing checking Σ) Γ).
Notation wf_local_rel Σ Γ Γ' := (All_local_env_rel (lift_typing checking Σ) Γ Γ').


(* Lemma meta_conv {cf : checker_flags} Σ Γ t A B :
    Σ ;;; Γ |- t : A ->
    A = B ->
    Σ ;;; Γ |- t : B.
Proof.
  intros h []; assumption.
Qed. *)


(** ** Typechecking of global environments *)

(* Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None. *)

Definition unlift_opt_pred (P : global_env_ext -> context -> option pterm -> pterm -> Type) :
  (global_env_ext -> context -> pterm -> pterm -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.


Module GCICTypingDef <: Typing PairTerms PairEnvironment PairEnvTyping.

  Definition ind_guard := ET.ind_guard ∘ e_mutual_inductive_body.
  Definition typing `{checker_flags} := checking.
  Definition smash_context := smash_context.
  Definition lift_context := lift_context.
  Definition subst_telescope := subst_telescope.

End GCICTypingDef.

Module GCICDeclarationTyping :=
  DeclarationTyping
    PairTerms
    PairEnvironment
    PairEnvTyping
    GCICTypingDef
    PairLookup.
Include GCICDeclarationTyping.

Fixpoint infering_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T) {struct d} : size
with pcsort_size `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▸□ u) {struct d} : size
with pcprod_size `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▸Π (na, A,B)) {struct d} : size
with pcind_size `{checker_flags} {Σ Γ ind t ui args} (d : Σ ;;; Γ |- t ▸{ind} (ui,args)) {struct d} : size
with checking_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ◃ T) {struct d} : size.
Proof.
  all: destruct d ;
    repeat match goal with
           | H : infering _ _ _ _ |- _ => apply infering_size in H
           | H : pchecking_sort _ _ _ _ |- _ => apply pcsort_size in H
           | H : pchecking_prod _ _ _ _ _ _ |- _ => apply pcprod_size in H
           | H : pchecking_ind _ _ _ _ _ _ |- _ => apply pcind_size in H 
           | H : checking _ _ _ _ |- _ => apply checking_size in H
           end ;
    match goal with
    | H : All2 _ _ _ |- _ => idtac
    | H : All_local_env _ _ |- _ => idtac
    | H : All_local_env_rel _ _ _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (H1 + H2 + H3))
    | H1 : size, H2 : size |- _ => exact (S (H1 + H2))
    | H1 : size |- _  => exact (S H1)
    | _ => exact 1
    end.
    - exact (S (c0 + p0 + (all2_size _ 
                                        (fun x y p => (checking_size _ _ _ _ _ (fst (snd p)))
                                                      + (checking_size _ _ _ _ _ (snd (snd p)))) a))).
    - exact (S (wf_local_size _ (checking_size H) _ a) +
               (all_size _ (fun x p => checking_size _ Σ _ _ _ (fst p)) a0)).
  Defined.

Definition wfarity_size `{checker_flags} {Σ Γ T} (d : isWfArity checking Σ Γ T) : size.
Proof.
  destruct d as (ctx & u & e & wf).
  exact (wf_local_rel_size Σ (@checking_size _) _ _ wf).
Defined.

Fixpoint infering_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T)
  : infering_size d > 0
with pcsort_size_pos `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▸□ u) {struct d}
  : pcsort_size d > 0
with pcprod_size_pos `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▸Π (na,A,B)) {struct d}
  : pcprod_size d > 0
with pcind_size_pos `{checker_flags} {Σ Γ t ind ui args} (d : Σ ;;; Γ |- t ▸{ind} (ui,args)) {struct d}
  : pcind_size d > 0
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

Lemma sort_pcheck_check_aux `{checker_flags} Σ Γ t u (d : Σ ;;; Γ |- t ▸□ u) :
   { d' : Σ ;;; Γ |- t ◃ (pSort u) & checking_size d' = pcsort_size d}.
Proof.
  destruct d as [t T u d red|t T u d red].
  - unshelve eexists.
    + change (E.eSort u) with (eterm (pSort u)).
      econstructor.
      1: assumption.
      apply red_consi. assumption.
    + reflexivity.
  - unshelve eexists.
    + change (E.eSort (Universe.make u)) with (eterm (pSort (Universe.make u))).
      econstructor.
      1: assumption.
      apply consi_alt.
      eexists. eexists. repeat split ; try eassumption.
      1: constructor 1.
      constructor.
    + reflexivity.
Defined.

Definition sort_pcheck_check `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▸□ u) :=
  (sort_pcheck_check_aux Σ Γ t u d).π1.
 
Lemma sort_pcheck_check_size `{checker_flags} Σ Γ t u (d : Σ ;;; Γ |- t ▸□ u) :
    checking_size (sort_pcheck_check d) = pcsort_size d.
Proof.
  exact (sort_pcheck_check_aux Σ Γ t u d).π2.
Qed.
  
(*Lemma sort_check_pcheck_aux `{checker_flags} Σ Γ t u (d : Σ ;;; Γ |- t ◃ pSort u) :
   { d' : Σ ;;; Γ |- t ▸□ u & pcsort_size d' = checking_size d}.
Proof.
  remember (pSort u) as T.
  unshelve eexists.
  - destruct d as [t T T' d cons]. subst.
    econstructor. 1: eassumption.
    apply consi_red.
    assumption.
  - destruct d. subst.
    reflexivity.
Defined.

Definition sort_check_pcheck `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ◃ pSort u) :=
  (sort_check_pcheck_aux Σ Γ t u d).π1.
 
Lemma sort_check_pcheck_size `{checker_flags} Σ Γ t u (d : Σ ;;; Γ |- t ◃ pSort u) :
    pcsort_size (sort_check_pcheck d) = checking_size d.
Proof.
  exact (sort_check_pcheck_aux Σ Γ t u d).π2.
Qed.

Lemma prod_pcheck_check_aux `{checker_flags} Σ Γ t na A B (d : Σ ;;; Γ |- t ▸Π (na,A,B)) :
   { d' : Σ ;;; Γ |- t ◃ pProd na A B & checking_size d' = pcprod_size d}.
Proof.
  unshelve eexists.
  - dependent destruction d.
    change (E.eProd na A B) with (eterm (pProd na A B)).
    econstructor. 1: eassumption.
    apply red_prod_consi.
    assumption.
  - destruct d.
    reflexivity.
Defined. *)

(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_env_ext, including size of the global declarations in it
    - size of the derivation. *)

Arguments lexprod [A B].

Definition wf `{checker_flags} := Forall_decls_typing checking.
Definition wf_ext `{checker_flags} := on_global_env_ext checking.

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

  Context (Pcheck : global_env_ext -> context -> pterm -> pterm -> Type).
  Context (Pinfer : global_env_ext -> context -> pterm -> pterm -> Type).
  Context (Psort : global_env_ext -> context -> pterm -> Universe.t -> Type).
  Context (Pprod : global_env_ext -> context -> pterm -> name -> pterm -> pterm -> Type).
  Context (Pind : global_env_ext -> context -> inductive -> pterm -> Instance.t -> list pterm -> Type).
  Context (PΓ : forall `{checker_flags} Σ Γ, wf_local Σ Γ -> Type).
  Arguments PΓ {_}.

  Definition env_prop `{checker_flags} :=
    forall Σ (wfΣ : wf Σ.1),
    (Forall_decls_typing Pcheck Σ.1) ×
    (forall Γ (wfΓ : wf_local Σ Γ), PΓ Σ Γ wfΓ) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t ◃ T -> Pcheck Σ Γ t T) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t ▹ T -> Pinfer Σ Γ t T) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t u, Σ ;;; Γ |- t ▸□ u -> Psort Σ Γ t u) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t na A B, Σ ;;; Γ |- t ▸Π (na,A,B) -> Pprod Σ Γ t na A B) ×
    (forall Γ (wfΓ : wf_local Σ Γ) ind t u args, Σ ;;; Γ |- t ▸{ind} (u,args) -> Pind Σ Γ ind t u args).

  (*Lemma type_Prop `{checker_flags} Σ : Σ ;;; [] |- pSort Universe.type0m ◃ pSort Universe.type1.
    eapply checkCons.
    - repeat constructor.
      by apply prop_global_ext_levels. 
    - by apply consi_refl.
  Defined.*)

  Lemma wf_local_app `{checker_flags} Σ (Γ Γ' : context) : wf_local Σ (Γ ,,, Γ') -> wf_local Σ Γ.
  Proof.
    induction Γ'. auto.
    simpl. intros H'; inv H'; eauto.
  Defined.
  Hint Resolve wf_local_app : wf.

  (* This lemma is completely false here!
  Lemma typing_wf_local `{checker_flags} {Σ} {Γ t T} :
    Σ ;;; Γ |- t : T -> wf_local Σ Γ.
  *)

  Derive Signature for All_local_env.

  Set Equations With UIP.
  Derive NoConfusion for context_decl.
  Derive NoConfusion for list.
  Derive NoConfusion for All_local_env.

  Lemma size_wf_local_app `{checker_flags} {Σ} (Γ Γ' : context) (Hwf : wf_local Σ (Γ ,,, Γ')) :
    wf_local_size Σ (@checking_size _) _ (wf_local_app _ _ _ Hwf) <=
    wf_local_size Σ (@checking_size _) _ Hwf.
  Proof.
    induction Γ' in Γ, Hwf |- *; try lia. simpl. lia.
    depelim Hwf.
    - inversion H0. subst. noconf H4. simpl. unfold eq_rect_r. simpl. specialize (IHΓ' _ Hwf). lia.
    - inversion H0. subst. noconf H4. specialize (IHΓ' _ Hwf). simpl. unfold eq_rect_r. simpl. lia.
  Qed.

  (* Lemma typing_wf_local_size `{checker_flags} {Σ} {Γ t T}
        (d :Σ ;;; Γ |- t : T) :
    wf_local_size Σ (@typing_size _) _ (typing_wf_local d) < typing_size d.
  Proof.
    induction d; simpl; try lia.
    - destruct indnpar as [ind' npar']; cbn in *; subst ind npar. lia.
    - pose proof (size_wf_local_app _ _ a).
      eapply Nat.le_lt_trans. eauto. subst types. lia.
    - pose proof (size_wf_local_app _ _ a).
      eapply Nat.le_lt_trans. eauto. subst types. lia.
    - destruct s as [s | [u Hu]]; try lia.
  Qed. *)

  Lemma wf_local_inv `{checker_flags} {Σ Γ'} (w : wf_local Σ Γ') :
    forall d Γ,
      Γ' = d :: Γ ->
      ∑ w' : wf_local Σ Γ,
        match d.(decl_body) with
        | Some b =>
          ∑ u (ty : Σ ;;; Γ |- b ◃ d.(decl_type)),
            { ty' : Σ ;;; Γ |- d.(decl_type) ◃ pSort u |
              wf_local_size Σ (@checking_size _) _ w' <
              wf_local_size _ (@checking_size _) _ w /\
              checking_size ty <= wf_local_size _ (@checking_size _) _ w /\
              checking_size ty' <= wf_local_size _ (@checking_size _) _ w }

        | None =>
          ∑ u,
            { ty : Σ ;;; Γ |- d.(decl_type) ◃ pSort u |
              wf_local_size Σ (@checking_size _) _ w' <
              wf_local_size _ (@checking_size _) _ w /\
              checking_size ty <= wf_local_size _ (@checking_size _) _ w }
        end.
  Proof.
    intros d Γ.
    destruct w.
    - simpl. congruence.
    - intros [=]. subst d Γ0.
      exists w. simpl. destruct o ; simpl in *. exists x.
      exists c.
      pose (checking_size_pos c).
      simpl. split.
      + lia.
      + auto with arith.
    - intros [=]. subst d Γ0.
      exists w. simpl. simpl in o.
      destruct o as [u [h h']].
      exists u, h', h. simpl in *.
      pose (checking_size_pos h).
      pose (checking_size_pos h').
      intuition eauto.
      all: try lia.
      Set Printing All.
  Qed.

  Lemma isWfArity_sort `{checker_flags} {Σ Γ} u : isWfArity checking Σ Γ (pSort u).
  Proof.
    red. exists []. exists u.
    split.
    1: by rewrite /destArity /= Universe.eqb_refl.
    constructor.
  Defined.

  Derive Signature for Alli.

  (** *** An induction principle ensuring the Σ declarations enjoy the same properties.
      Also theads the well-formedness of the local context and the induction principle for it,
      and gives the right induction hypothesis
      on typing judgments in application spines, fix and cofix blocks.
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
    | context_cons Γ wfΓ => wf_local_size Σ (@checking_size _) Γ wfΓ
    | check_cons Γ wfΓ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ) + (checking_size d)
    | inf_cons Γ wfΓ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ) + (infering_size d)
    | sort_cons Γ wfΓ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ) + (pcsort_size d)
    | prod_cons Γ wfΓ _ _ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ) + (pcprod_size d)
    | ind_cons Γ wfΓ _ _ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ) + (pcind_size d)
  end.

  Definition context_size `{checker_flags} {Σ} {wfΣ : wf Σ.1} (d : typing_sum Σ wfΣ) := 
  match d with
    | env_cons => 0
    | context_cons Γ wfΓ => wf_local_size Σ (@checking_size _) Γ wfΓ
    | check_cons Γ wfΓ _ _ d => wf_local_size Σ (@checking_size _) Γ wfΓ
    | inf_cons Γ wfΓ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ)
    | sort_cons Γ wfΓ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ)
    | prod_cons Γ wfΓ _ _ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ)
    | ind_cons Γ wfΓ _ _ _ _ d => (wf_local_size Σ (@checking_size _) Γ wfΓ)
  end.

  Definition Ptyping_sum `{checker_flags} {Σ wfΣ} (d : typing_sum Σ wfΣ) :=
  match d with
    | env_cons => Forall_decls_typing Pcheck Σ.1
    | context_cons Γ wfΓ => PΓ Σ Γ wfΓ
    | check_cons Γ _ T t _ => Pcheck Σ Γ t T
    | inf_cons Γ _ T t _ => Pinfer Σ Γ t T
    | sort_cons Γ _ T u _ => Psort Σ Γ T u
    | prod_cons Γ _ T na A B _ => Pprod Σ Γ T na A B
    | ind_cons Γ _ ind T u args _ => Pind Σ Γ ind T u args
  end.

  Ltac applyIH := match goal with
    | IH : forall _ _ d', _ -> Ptyping_sum d' |- Forall_decls_typing Pcheck _ =>
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
    | |- isWfArity _ _ _ (pSort _) => apply isWfArity_sort ; try assumption ; try (by constructor)
    | |- dlexprod _ _ _ _ => constructor ; simpl ; lia
    | |- dlexprod _ _ _ _ =>
            constructor 2 ; simpl ;
            (match goal with | |- dlexprod _ _ (?x1;_) (?y1;_) => replace x1 with y1 by lia end ; constructor 2) ||
            constructor ; unf_pterm ; try lia
    | _ => assumption
    | _ => unf_pterm ; simpl ; lia
    | _ => idtac
    end.

  Lemma typing_ind_env `{cf : checker_flags} :
    let Pdecl := fun Σ Γ wfΓ t T tyT => Pcheck Σ Γ t T in

    (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ), 
          All_local_env_over checking Pdecl Σ Γ wfΓ -> PΓ Σ Γ wfΓ) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ wfΓ ->
        Pinfer Σ Γ (pRel n) (plift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (l : Level.t),
        PΓ Σ Γ wfΓ ->
        LevelSet.In l (global_ext_levels Σ) ->
        Pinfer Σ Γ (pSort (Universe.make l)) (pSort (Universe.super l))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : pterm) (s1 s2 : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸□ s1 ->
        Psort Σ Γ t s1 ->
        Σ ;;; Γ,, vass n t |- b ▸□ s2 ->
        Psort Σ (Γ,, vass n t) b s2 -> Pinfer Σ Γ (pProd n t b) (pSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : pterm)
            (s : Universe.t) (bty : pterm),
            PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸□ s ->
        Psort Σ Γ t s ->
        Σ ;;; Γ,, vass n t |- b ▹ bty -> Pinfer Σ (Γ,, vass n t) b bty ->
        Pinfer Σ Γ (pLambda n t b) (pProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (b B t : pterm)
            (s : Universe.t) (A : pterm),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- B ▸□ s ->
        Psort Σ Γ B s ->
        Σ ;;; Γ |- b ◃ B ->
        Pcheck Σ Γ b B ->
        Σ ;;; Γ,, vdef n b B |- t ▹ A ->
        Pinfer Σ (Γ,, vdef n b B) t A -> Pinfer Σ Γ (pLetIn n b B t) (pLetIn n b B A)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : pterm) na A B u,
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸Π (na, A, B) -> Pprod Σ Γ t na A B ->
        Σ ;;; Γ |- u ◃ A -> Pcheck Σ Γ u A ->
        Pinfer Σ Γ (pApp t u) (psubst10 u B)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (cst : kername) u (decl : constant_body),
        Forall_decls_typing Pcheck Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        Pinfer Σ Γ (pConst cst u) (psubst_instance_constr u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl,
        Forall_decls_typing Pcheck Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_inductive Σ.1 mdecl ind idecl ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        Pinfer Σ Γ (pInd ind u) (psubst_instance_constr u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl,
        Forall_decls_typing Pcheck Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constructor Σ.1 mdecl idecl (ind, i) cdecl ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        Pinfer Σ Γ (pConstruct ind i u)
          {| eterm := ET.type_of_constructor mdecl (on_pi2 eterm cdecl) (ind, i) u ;
              gterm := type_of_constructor mdecl (on_pi2 gterm cdecl) (ind, i) u |}) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u (npar : nat)
            (p c : pterm) (brs : list (nat * pterm))
            (args : list pterm) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
            (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing Pcheck Σ.1 -> PΓ Σ Γ wfΓ ->
        ET.isCoFinite mdecl.(ind_finite) = false ->
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
        map_option_out (build_branches_type ind mdecl idecl (map gterm params) u p) =
          Some (map (on_snd gterm) btys) ->
        All2 (fun br bty => (br.1 = bty.1) ×
                          (Σ ;;; Γ |- bty.2 ◃ pSort ps) × Pcheck Σ Γ bty.2 (pSort ps) ×
                          (Σ ;;; Γ |- br.2 ◃ bty.2) × Pcheck Σ Γ br.2 bty.2)
              brs btys ->
        Pinfer Σ Γ {| eterm := E.eCase (ind,npar) p c (map (on_snd eterm) brs) ;
                      gterm := G.gCase (ind,npar) p c (map (on_snd gterm) brs) |}
                (pmkApps p (skipn npar args ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : pterm) u
          mdecl idecl pdecl args,
        Forall_decls_typing Pcheck Σ.1 -> PΓ Σ Γ wfΓ ->
        declared_projection Σ.1 mdecl idecl p pdecl ->
        Σ ;;; Γ |- c ▸{fst (fst p)} (u,args) ->
        Pind Σ Γ (fst (fst p)) c u args ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in
        Pinfer Σ Γ (pProj p c) (psubst0 (c :: List.rev args) (psubst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : mfixpoint pterm) (n : nat) decl,
        ET.fix_guard (e_mfix mfix) ->
        nth_error mfix n = Some decl ->
        forall wfΓ : wf_local Σ (Γ,,,fix_context mfix), PΓ Σ (Γ,,,fix_context mfix) wfΓ ->
        All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ plift0 #|fix_context mfix| d.(dtype)) ×
                  (E.isLambda d.(dbody) = true) × (G.isLambda d.(dbody) = true) ×
                  Pcheck Σ (Γ ,,, fix_context mfix) d.(dbody) (plift0 #|fix_context mfix| d.(dtype))) mfix ->
        Pinfer Σ Γ {| eterm := E.eFix (e_mfix mfix) n ; gterm := G.gFix (g_mfix mfix) n |} decl.(dtype)) ->

      (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) A u,
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- A ▸□ u -> Psort Σ Γ A u ->
        Pinfer Σ Γ {| eterm := E.eErr E.ukn (eterm A) ; gterm := G.gUkn (gterm A) |} A) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A : pterm) (u : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- A ▸□ u -> Psort Σ Γ A u ->
        Σ ;;; Γ |- t ◃ A ->
        Pcheck Σ Γ t A ->
        Pinfer Σ Γ {| eterm := t.(eterm) ; gterm := G.gCast A.(gterm) t.(gterm) |} A) ->

      (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : pterm) (u : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> (eSort u) ->
        Psort Σ Γ {| eterm := E.eCast (eterm T) (E.eSort u) (eterm t) ; gterm := gterm t |} u) ->

      (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : pterm) (l : Level.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> eErr ukn (eSort (Universe.super l)) ->
        Psort Σ Γ {| eterm := E.eCast (eterm T) (eSort (Universe.make l)) (eterm t) ; gterm := gterm t |} (Universe.make l)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : pterm) (na : name) (A B : pterm),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> (eProd na (eterm A) (eterm B)) ->
        isErasure A -> isErasure B ->
        Pprod Σ Γ {| eterm := E.eCast (eterm T) (E.eProd na A B) (eterm t) ; gterm := gterm t |} na A B) ->
    
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : pterm) (na : name) (u : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> eErr ukn (eSort u) ->
        Pprod Σ Γ
          {| eterm := eCast (eterm T) (eProd nAnon (eErr E.ukn (eSort u)) (eErr E.ukn (eSort u))) (eterm t) ;
            gterm := gterm t |}
          nAnon
          {| eterm := eErr ukn (eSort u) ; gterm := gUkn (gSort u) |}
          {| eterm := eErr ukn (eSort u) ; gterm := gUkn (gSort u) |}) ->
    
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (t T : pterm) (ui : Instance.t)
          (args : list pterm),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) --> E.mkApps (eInd ind ui) (map eterm args) ->
        All isErasure args ->
        Pind Σ Γ ind t ui args) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T T' : pterm),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        (e_global_env_ext Σ) ;;; (e_context Γ) |- (eterm T) ~~ (eterm T') ->
        Pcheck Σ Γ {| eterm := E.eCast (eterm T) (eterm T') (eterm t) ; gterm := gterm t |} T') ->
      
    env_prop.
  Proof.
    intros Pdecl HΓ HRel HSort HProd HLambda HLetIn HApp HConst HInd HConstruct HCase
      HProj HFix HUkn HCast HpcSortS HpcSortU HpcProdP HpcProdU HpcInd HCheck ; unfold env_prop.
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
      cbn in wfΣ ; simpl in *.
      have IH' : forall Σ' wfΣ' (d' : typing_sum Σ' wfΣ'), globenv_size (Σ'.1) < S (globenv_size Σ) ->
                    Ptyping_sum d'
        by intros ; apply IH ; constructor ; simpl ; assumption.
      clear IH.
      inversion_clear wfΣ.
      constructor.
      + change (Forall_decls_typing Pcheck (Σ,φ).1).
        applyIH.
      + assumption.
      + assumption.
      + destruct g; simpl.
        * destruct c; simpl in *.
          destruct cst_body; red ; red in X0 ; simpl in *.
          -- destruct X0 as [u [cty ct]].
            exists u ; split.
            all: applyIH ; by apply localenv_nil.
            
          -- red ; simpl.
            destruct X0 as [u ?].
            exists u.
            applyIH.
            by apply localenv_nil.

        * red in X0. destruct X0 as [onI onP onnp] ; constructor ; eauto.

          2:{ have onPover : PΓ (Σ, ind_universes m) (ind_params m) onP
                by applyIH.
              clear - X IH' onPover.
              eapply All_local_env_impl_wf.
              1: eassumption.
              intros Γ t [T|] wfΓ [s ?] ; exists s ; intuition ; applyIH.
          }

          eapply Alli_impl; eauto. intros n x Xg.
          admit.
  (*         refine {| ind_indices := Xg.(ind_indices);
                    ind_arity_eq := Xg.(ind_arity_eq);
                    ind_ctors_sort := Xg.(ind_ctors_sort) |}.
          ++ apply onArity in Xg. destruct Xg as [s Hs]. exists s; auto.
            applyIH.
            by apply localenv_nil.

          ++ pose proof Xg.(onConstructors) as Xg'.
              eapply All2_impl; eauto. intros ? ? onC.
              red in onC |- *. destruct onC as (wf&(s&Hs)&cs&Hargsu). repeat split.
              ** eapply All_local_env_over_impl.
                applyIH.
              ** exists s.
                simpl in udecl.
                applyIH.
                eapply wf_local_app.
                eassumption.
              ** exists cs.
                induction (cshape_args cs) as [ | [? [] ?] Γ] ; simpl in *.
                --- auto.
                --- destruct Hargsu as (?&u&?&?) ; split ; auto.
                    exists u.
                    split ; applyIH ; eapply type_local_ctx_All_local_env ; eassumption.
                --- destruct Hargsu as [] ; split ; auto.
                    applyIH.
                    eapply type_local_ctx_All_local_env ; eassumption.
          ++ intros nempty. destruct (Xg.(onProjections) nempty).
            constructor ; try assumption.
            eapply Alli_impl ; eauto.
            intros ? ? [s ].
            exists s.
            applyIH.
            constructor.
            1: assumption.
            simpl.
            admit. (*for now this is just blatantly false*)

          ++ pose proof Xg.(ind_sorts) as Xg'.
            unfold check_ind_sorts in *.
            destruct (universe_family Xg.(ind_sort)) ; simpl in *.
            1: assumption.
            all: destruct Xg' ; split ; try assumption.
            all: destruct indices_matter ; try easy.
            all: eapply type_local_ctx_impl ; try eassumption.
            all: intros ; applyIH.
            all: eapply type_local_ctx_All_local_env ; eassumption. *)

    - apply HΓ.
      1: assumption.
      dependent induction wfΓ.
      + constructor.
      + destruct o as (u & d).
        constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          dependent destruction H ; [constructor | constructor 2] ; auto.
          etransitivity ; eauto.
          constructor.
          simpl ; cbn in d ; pose proof (checking_size_pos d) ; lia.
        * constructor.
          red ; applyIH.
          cbn in d ; pose proof (checking_size_pos d) ; lia.
      + destruct o as (u & d & d').
        constructor.
        2: constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          dependent destruction H ; [constructor | constructor 2] ; auto.
          etransitivity ; eauto.
          constructor.
          simpl ; cbn in d ; pose proof (checking_size_pos d) ; lia.
        * red ; applyIH.
          cbn in d' ; pose proof (checking_size_pos d') ; lia.
        * red ; applyIH.
          cbn in d ; pose proof (checking_size_pos d) ; lia.

    - destruct c.
      unshelve eapply HCheck ; auto.
      all: applyIH.

    - unshelve eapply HRel ; auto.
      applyIH.

    - unshelve eapply HSort ; auto.
      applyIH.

    - unshelve eapply HProd ; auto.
      all: applyIH.
        * constructor.
          1: assumption.
          red. eexists.
          apply sort_pcheck_check.
          eassumption.
        * simpl ; rewrite sort_pcheck_check_size. lia.
    
    - unshelve eapply HLambda ; auto.
      all: applyIH.
        * constructor.
          1: assumption.
          red. eexists.
          apply sort_pcheck_check.
          eassumption.
        * simpl ; rewrite sort_pcheck_check_size. lia.

    - unshelve eapply HLetIn ; auto.
      all: applyIH.
        * constructor.
          1: assumption.
          red. eexists.
          split ; [apply sort_pcheck_check|] ; eassumption.
        * simpl ; rewrite sort_pcheck_check_size. lia.

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
        all: unshelve eapply (IH' (check_cons _ wfΣ _ wfΓ _ _ _)) ; try eassumption.
        all: simpl ; unf_pterm ; lia.
      + apply IHa.
        intros. apply IH'. simpl in *. lia.
    
    - unshelve eapply HProj ; auto.
      all: applyIH.

    - unshelve eapply HFix ; eauto.
      1: by applyIH.
      have IH' : forall d' : typing_sum Σ wfΣ,
        (typing_sum_size d') <
          (typing_sum_size (inf_cons _ wfΣ _ wfΓ _ {|
            eterm := E.eFix (e_mfix mfix) n;
            gterm := G.gFix (g_mfix mfix) n |}
          (infer_Fix Σ Γ mfix n decl i e a a0)))
        -> Ptyping_sum d'
        by intros ; apply IH ; constructor 2 ; constructor 1 ; assumption.
      simpl in IH'.
      remember (fix_context mfix) as Γ'.
      remember (Γ ,,, Γ') as Γ''.
      clear - a a0 IH'.
      induction a0 as [| ? ? [? []]].
      1: by constructor.
      constructor.
      + intuition.
        unshelve eapply (IH' (check_cons _ wfΣ _ _ _ _ _)) ; try assumption.
        simpl. lia.
      + eapply IHa0.
        intros ; apply IH'.
        simpl ; lia.

    - unshelve eapply HUkn ; auto.
      all: by applyIH.

    - unshelve eapply HCast ; auto.
      all: by applyIH.

    - destruct p.
      + unshelve eapply HpcSortS ; auto.
        all: applyIH.
      + unshelve eapply HpcSortU ; auto.
        all: applyIH. 

    - destruct p.
      + unshelve eapply HpcProdP ; auto.
        all: applyIH.
      + unshelve eapply HpcProdU ; auto.
        1: exact nAnon.
        all: applyIH.

    - destruct p.
      unshelve eapply HpcInd ; auto.
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