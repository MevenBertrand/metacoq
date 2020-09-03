From Coq Require Import Bool String List Program.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst
UnivSubst Environment.
From MetaCoq.PCUIC Require Import PCUICReflect.
From MetaCoq.EGCIC Require EGCICAst EGCICSize EGCICAstUtils EGCICInduction EGCICLiftSubst
  EGCICUnivSubst EGCICReflect EGCICEquality EGCICPosition.
From MetaCoq.GCIC Require Import GCICAst GCICSize GCICAstUtils GCICInduction GCICLiftSubst
  GCICUnivSubst GCICReflect GCICEquality GCICPosition GCICEnvironmentTyping.

Import MonadNotation.

From Equations Require Import Equations.

Module E := EGCIC.EGCICAst.
Module G := GCIC.GCICAst.

(** Terms and extensions for typing: because we always handle a term and its compilation, we need pairs of terms everywhere*)

Declare Scope pair.
Delimit Scope pair with pair.
Open Scope pair.

Record pterm :=
{ eterm :> EGCICAst.term ;
  gterm :> GCICAst.term }.

Derive NoConfusion NoConfusionHom for pterm.

Instance EqDec_term : EqDec pterm.
Proof.
intros [et gt] [et' gt'].
set (t := {|eterm := et ; gterm := gt|}) ; set (t' := {|eterm := et' ; gterm := gt'|}).
destruct (EGCICReflect.EqDec_term et et') as [? | n].
  - destruct (GCICReflect.EqDec_term gt gt') as [? | n] ; subst.
    + left ; reflexivity.
    + right ; intros e ; apply n.
      change gt with t.(gterm) ; change gt' with t'.(gterm).
      rewrite e ; reflexivity.
  - right ; intros e ; apply n.
    change et with t.(eterm) ; change et' with t'.(eterm).
    rewrite e ; reflexivity.
Defined.

Instance reflect_pterm : ReflectEq pterm :=
  let h := EqDec_ReflectEq pterm in _.

Definition pRel := fun n => {| eterm := EGCICAst.eRel n ; gterm := GCICAst.gRel n |}.
Definition pSort := fun u => {| eterm := EGCICAst.eSort u ; gterm := GCICAst.gSort u |}.
Definition pProd := fun na A B => {| eterm := EGCICAst.eProd na A.(eterm) B.(eterm) ; gterm := GCICAst.gProd na A.(gterm) B.(gterm) |}.
Definition pLambda := fun na A t => {| eterm := EGCICAst.eLambda na A.(eterm) t.(eterm) ; gterm := GCICAst.gLambda na A.(gterm) t.(gterm)|}.
Definition pLetIn := fun na b B t =>
  {| eterm := EGCICAst.eLetIn na b.(eterm) B.(eterm) t.(eterm) ; gterm := GCICAst.gLetIn na b.(gterm) B.(gterm) t.(gterm) |}.
Definition pApp := fun t u => {| eterm := EGCICAst.eApp t.(eterm) u.(eterm) ; gterm := GCICAst.gApp t.(gterm) u.(gterm)|}.
Definition pConst := fun cst u => {| eterm := EGCICAst.eConst cst u ; gterm := GCICAst.gConst cst u |}.
Definition pInd := fun ind u => {| eterm := EGCICAst.eInd ind u ; gterm := GCICAst.gInd ind u |}.
Definition pConstruct := fun ind i u => {| eterm := EGCICAst.eConstruct ind i u ; gterm := GCICAst.gConstruct ind i u |}.
Definition pProj := fun p c => {| eterm := EGCICAst.eProj p c.(eterm) ; gterm := GCICAst.gProj p c.(gterm) |}.

Definition pmkApps (t : pterm) (l : list pterm) :=
  {| eterm := EGCICAst.mkApps t.(eterm) (List.map eterm l) ; gterm := GCICAst.mkApps t.(gterm) (List.map gterm l) |}.

Module PairTerms <: Term.

  Definition term := pterm.

  Definition tRel := pRel.
  Definition tSort := pSort.
  Definition tProd := pProd.
  Definition tLetIn := pLetIn.
  Definition tInd := pInd.
  Definition tLambda := pLambda.
  Definition tProj := pProj.

  Definition mkApps := pmkApps.
End PairTerms.

Ltac unf_pterm := unfold pRel in *;
unfold pSort in *; unfold pProd in *; unfold pLambda in *; unfold pLetIn in *; unfold pApp in * ;
unfold pConst in * ; unfold pInd in * ; unfold pConstruct in * ; unfold pProj in * ; unfold pmkApps in *.

Module PairEnvironment := Environment PairTerms.
Include PairEnvironment.

Module PairLookup := Lookup PairTerms PairEnvironment.
Include PairLookup.

Module PairEnvTyping := EnvTyping PairTerms PairEnvironment.
Include PairEnvTyping.

(*Coercions from the various constructs over pterm (mostly environments and contexts) to their gradual/explicit gradual counterparts*)

Definition e_decl (d : context_decl) : EGCICAst.context_decl :=
{| EGCICAst.decl_name := d.(decl_name);
   EGCICAst.decl_body := option_map eterm d.(decl_body);
   EGCICAst.decl_type := eterm d.(decl_type) |}.
Definition g_decl (d : context_decl) : GCICAst.context_decl :=
  {| GCICAst.decl_name := d.(decl_name);
     GCICAst.decl_body := option_map gterm d.(decl_body);
     GCICAst.decl_type := gterm d.(decl_type) |}.
   
Definition eqb_context_decl (x y : context_decl) :=
  let (na, b, ty) := x in
  let (na', b', ty') := y in
  eqb na na' && eqb b b' && eqb ty ty'.

Instance eq_ctx : ReflectEq context_decl.
Proof.
  refine {| eqb := eqb_context_decl |}.
  intros.
  destruct x as [na b ty], y as [na' b' ty']. cbn -[eqb].
  destruct (eqb_spec na na'); subst;
    destruct (eqb_spec b b'); subst;
      destruct (eqb_spec ty ty'); subst; constructor; congruence.
Qed. 

Definition e_context (Γ : context) : EGCICAst.context :=
   List.map e_decl Γ.
Coercion e_context : context >-> EGCICAst.context.
Definition g_context (Γ : context) : GCICAst.context :=
   List.map g_decl Γ.
Coercion g_context : context >-> GCICAst.context.

Instance eqb_ctx : ReflectEq context := _.

Definition e_constant_body (decl : constant_body) : EGCICAst.constant_body :=
{| EGCICAst.cst_type := eterm decl.(cst_type);
  EGCICAst.cst_body := option_map eterm decl.(cst_body);
  EGCICAst.cst_universes := decl.(cst_universes) |}.
Definition g_constant_body (decl : constant_body) : GCICAst.constant_body :=
  {| GCICAst.cst_type := gterm decl.(cst_type);
     GCICAst.cst_body := option_map gterm decl.(cst_body);
     GCICAst.cst_universes := decl.(cst_universes) |}.


Definition e_one_inductive_body m : EGCICAst.one_inductive_body :=
 {| EGCICAst.ind_name := m.(ind_name);
    EGCICAst.ind_type := eterm m.(ind_type) ;
    EGCICAst.ind_kelim := m.(ind_kelim) ;
    EGCICAst.ind_ctors := map (on_pi2 eterm) m.(ind_ctors) ;
    EGCICAst.ind_projs := map (on_snd eterm) m.(ind_projs) |}.
Coercion e_one_inductive_body : one_inductive_body >-> EGCICAst.one_inductive_body.
Definition g_one_inductive_body m : GCICAst.one_inductive_body :=
 {| GCICAst.ind_name := m.(ind_name);
    GCICAst.ind_type := gterm m.(ind_type) ;
    GCICAst.ind_kelim := m.(ind_kelim) ;
    GCICAst.ind_ctors := map (on_pi2 gterm) m.(ind_ctors) ;
    GCICAst.ind_projs := map (on_snd gterm) m.(ind_projs) |}.
Coercion g_one_inductive_body : one_inductive_body >-> GCICAst.one_inductive_body.

Definition e_mutual_inductive_body m : EGCICAst.mutual_inductive_body :=
  {| EGCICAst.ind_finite := m.(ind_finite) ;
     EGCICAst.ind_npars := m.(ind_npars) ;
     EGCICAst.ind_params := (e_context m.(ind_params)) ;
     EGCICAst.ind_bodies := map e_one_inductive_body m.(ind_bodies) ;
     EGCICAst.ind_universes := m.(ind_universes) ;
     EGCICAst.ind_variance := m.(ind_variance) |}.
Coercion e_mutual_inductive_body : mutual_inductive_body >-> EGCICAst.mutual_inductive_body.
Definition g_mutual_inductive_body m : GCICAst.mutual_inductive_body :=
  {| GCICAst.ind_finite := m.(ind_finite) ;
     GCICAst.ind_npars := m.(ind_npars) ;
     GCICAst.ind_params := (g_context m.(ind_params)) ;
     GCICAst.ind_bodies := map g_one_inductive_body m.(ind_bodies) ;
     GCICAst.ind_universes := m.(ind_universes) ;
     GCICAst.ind_variance := m.(ind_variance) |}.
Coercion g_mutual_inductive_body : mutual_inductive_body >-> GCICAst.mutual_inductive_body.


Definition e_global_declaration (g : global_decl) : EGCICAst.global_decl :=
  match g with
  | ConstantDecl c => EGCICAst.ConstantDecl (e_constant_body c)
  | InductiveDecl m => EGCICAst.InductiveDecl (e_mutual_inductive_body m)
  end.
Definition g_global_declaration (g : global_decl) : GCICAst.global_decl :=
  match g with
  | ConstantDecl c => GCICAst.ConstantDecl (g_constant_body c)
  | InductiveDecl m => GCICAst.InductiveDecl (g_mutual_inductive_body m)
  end.

Definition e_global_env (Σ : global_env) : EGCICAst.global_env :=
  map (on_snd e_global_declaration) Σ.
Coercion e_global_env : global_env >-> EGCICAst.global_env.
Definition g_global_env (Σ : global_env) : GCICAst.global_env :=
  map (on_snd g_global_declaration) Σ.
Coercion g_global_env : global_env >-> GCICAst.global_env.

Definition e_global_env_ext (Σ : global_env_ext) : EGCICAst.global_env_ext :=
  (e_global_env Σ.1,Σ.2).
Coercion e_global_env_ext : global_env_ext >-> EGCICAst.global_env_ext.
Definition g_global_env_ext (Σ : global_env_ext) : GCICAst.global_env_ext :=
  (g_global_env Σ.1,Σ.2).
Coercion g_global_env_ext : global_env_ext >-> GCICAst.global_env_ext.


Definition e_mfix : mfixpoint pterm -> mfixpoint EGCICAst.term := map (map_def eterm eterm).
Definition g_mfix : mfixpoint pterm -> mfixpoint GCICAst.term := map (map_def gterm gterm).

Definition psubst_instance_constr : UnivSubst pterm :=
  fun ui t => {| eterm := EGCICUnivSubst.subst_instance_constr ui t ; gterm := GCICUnivSubst.subst_instance_constr ui t |}.
Definition psubst_instance_context : UnivSubst context :=
  map_context ∘ psubst_instance_constr.

Definition plift (k n : nat) (t : pterm) : pterm :=
  {|eterm := EGCICLiftSubst.lift k n t ; gterm := GCICLiftSubst.lift k n t|}.

Notation plift0 n := (plift n 0).

Definition fix_context (m : mfixpoint pterm) : context :=
  List.rev (mapi (fun (i : nat) (d : def pterm) => vass (dname d) (plift0 i (dtype d))) m).

Definition psubst (s : list pterm) k (t : pterm) :=
  {| eterm := EGCICLiftSubst.subst (List.map eterm s) k t.(eterm) ;
     gterm := GCICLiftSubst.subst (List.map gterm s) k t.(gterm)|}.

Notation psubst0 s := (psubst s 0).
Definition psubst1 t k u := psubst [t] k u.
Notation psubst10 t := (psubst1 t 0).



Definition def_option_out {A} (d : def (option A)) : option (def A) :=
  dtype' <- dtype d ;;
  dbody' <- dbody d ;;
  ret {| dname := dname d; dtype := dtype'; dbody := dbody'; rarg := rarg d |}.

Fixpoint egcic_to_gcic (t : EGCICAst.term) : option GCICAst.term :=
match t with
| EGCICAst.eRel n => ret (GCICAst.gRel n)
| EGCICAst.eVar i => ret (GCICAst.gVar i)
| EGCICAst.eEvar n l => l' <- map_option_out (map egcic_to_gcic l) ;; ret (GCICAst.gEvar n l')
| EGCICAst.eSort u => ret (GCICAst.gSort u)
| EGCICAst.eProd na A B => A' <- egcic_to_gcic A ;; B' <- egcic_to_gcic B ;; ret (GCICAst.gProd na A' B')
| EGCICAst.eLambda na A t => A' <- egcic_to_gcic A ;; t' <- egcic_to_gcic t ;; ret (GCICAst.gLambda na A' t')
| EGCICAst.eLetIn na b B t => b' <- egcic_to_gcic b ;; B' <- egcic_to_gcic B ;; t' <- egcic_to_gcic t ;;
    ret (GCICAst.gLetIn na b' B' t')
| EGCICAst.eApp u v => u' <- egcic_to_gcic u ;; v' <- egcic_to_gcic v ;; ret (GCICAst.gApp u' v')
| EGCICAst.eConst k ui => ret (GCICAst.gConst k ui)
| EGCICAst.eInd ind ui => ret (GCICAst.gInd ind ui)
| EGCICAst.eConstruct ind n ui => ret (GCICAst.gConstruct ind n ui)
| EGCICAst.eCase indn p c brs => p' <- egcic_to_gcic p ;; c' <- egcic_to_gcic c ;;
    brs' <- map_option_out (map (fun b => (b2' <- egcic_to_gcic b.2 ;; ret(b.1,b2'))) brs) ;;
    ret (GCICAst.gCase indn p' c' brs') 
| EGCICAst.eProj p c => c' <- egcic_to_gcic c ;; ret (GCICAst.gProj p c')
| EGCICAst.eFix mfix idx =>
    mfix' <- map_option_out (map (def_option_out ∘ (map_def egcic_to_gcic egcic_to_gcic)) mfix) ;;
    ret (GCICAst.gFix mfix' idx)
| EGCICAst.eCoFix mfix idx =>
    mfix' <- map_option_out (map (def_option_out ∘ (map_def egcic_to_gcic egcic_to_gcic)) mfix) ;;
    ret (GCICAst.gCoFix mfix' idx)
| EGCICAst.eErr e A => (match e with
  | EGCICAst.ukn => A' <- egcic_to_gcic A ;; ret(GCICAst.gUkn A')
  | EGCICAst.rai => None end)
| EGCICAst.eCast A B u =>  u' <- egcic_to_gcic u ;; B' <- egcic_to_gcic B ;;
    ret (GCICAst.gCast B' u')
end.

Definition isErasure (t : pterm) : Type :=
  egcic_to_gcic (eterm t) = Some (gterm t).