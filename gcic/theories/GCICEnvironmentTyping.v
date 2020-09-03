From Coq Require Import Ascii String OrderedType Program Lia.
From MetaCoq.Template Require Import config utils BasicAst AstUtils.
From MetaCoq.Template Require Import Universes Environment.
Import List.ListNotations.

Set Asymmetric Patterns.

From Equations Require Import Equations.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Fixpoint lookup_env (Σ : global_env) (id : kername) : option global_decl :=
    match Σ with
    | nil => None
    | d :: tl =>
      if eq_kername id d.1 then Some d.2
      else lookup_env tl id
    end.

  Definition declared_constant (Σ : global_env) (id : kername) decl : Prop :=
    lookup_env Σ id = Some (ConstantDecl decl).

  Definition declared_minductive Σ mind decl :=
    lookup_env Σ mind = Some (InductiveDecl decl).

  Definition declared_inductive Σ mdecl ind decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor Σ mdecl idecl cstr cdecl : Prop :=
    declared_inductive Σ mdecl (fst cstr) idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection Σ mdecl idecl (proj : projection) pdecl
  : Prop :=
    declared_inductive Σ mdecl (fst (fst proj)) idecl /\
    List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl /\
    mdecl.(ind_npars) = snd (fst proj).

  Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl cb => F cb.(cst_universes)
  | InductiveDecl mb => F mb.(ind_universes)
  end.

  Definition monomorphic_udecl_decl := on_udecl_decl monomorphic_udecl.

  Definition monomorphic_levels_decl := fst ∘ monomorphic_udecl_decl.

  Definition monomorphic_constraints_decl := snd ∘ monomorphic_udecl_decl.

  Definition universes_decl_of_decl := on_udecl_decl (fun x => x).

  (* Definition LevelSet_add_list l := LevelSet.union (LevelSetProp.of_list l). *)

  Definition global_levels (Σ : global_env) : LevelSet.t :=
    fold_right
      (fun decl lvls => LevelSet.union (monomorphic_levels_decl decl.2) lvls)
      (LevelSet_pair Level.lSet Level.lProp) Σ.

  Lemma global_levels_Set Σ :
    LevelSet.mem Level.lSet (global_levels Σ) = true.
  Proof.
    induction Σ; simpl. reflexivity.
    apply LevelSet.mem_spec, LevelSet.union_spec; right.
    now apply LevelSet.mem_spec in IHΣ.
  Qed.

  Lemma global_levels_Prop Σ :
    LevelSet.mem Level.lProp (global_levels Σ) = true.
  Proof.
    induction Σ; simpl. reflexivity.
    apply LevelSet.mem_spec, LevelSet.union_spec; right.
    now apply LevelSet.mem_spec in IHΣ.
  Qed.

  (** One can compute the constraints associated to a global environment or its
      extension by folding over its constituent definitions.

      We make *only* the second of these computations an implicit coercion
      for more readability. Note that [fst_ctx] is also a coercion which goes
      from a [global_env_ext] to a [global_env]: coercion coherence would *not*
      be ensured if we added [global_constraints] as well as a coercion, as it
      would forget the extension's constraints. *)

  Definition global_constraints (Σ : global_env) : ConstraintSet.t :=
    fold_right (fun decl ctrs =>
        ConstraintSet.union (monomorphic_constraints_decl decl.2) ctrs
      ) ConstraintSet.empty Σ.

  Definition global_uctx (Σ : global_env) : ContextSet.t :=
    (global_levels Σ, global_constraints Σ).

  Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t :=
    LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1).

  Definition global_ext_constraints (Σ : global_env_ext) : ConstraintSet.t :=
    ConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1).

  Coercion global_ext_constraints : global_env_ext >-> ConstraintSet.t.

  Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t :=
    (global_ext_levels Σ, global_ext_constraints Σ).


  Lemma prop_global_ext_levels Σ : LevelSet.In Level.lProp (global_ext_levels Σ).
  Proof.
    destruct Σ as [Σ φ]; cbn.
    apply LevelSetFact.union_3. cbn -[global_levels]; clear φ.
    induction Σ.
    - cbn. now apply LevelSetFact.add_1.
    - simpl. now apply LevelSetFact.union_3.
  Qed.

  (** Check that [uctx] instantiated at [u] is consistent with
    the current universe graph. *)

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : ConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx c => List.length u = 0
    | Polymorphic_ctx c =>
      (* no prop levels in instances *)
      forallb (negb ∘ Level.is_prop) u /\
      (* levels of the instance already declared *)
      forallb (fun l => LevelSet.mem l lvs) u /\
      List.length u = List.length c.1 /\
      valid_constraints φ (subst_instance_cstrs u c.2)
    end.

  Definition consistent_instance_ext `{checker_flags} Σ :=
    consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
  Include Lookup T E.
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T).

  Import T E.

  Section TypeLocal.

    Context (typing : forall (Γ : context), term -> option term -> Type).

    Definition on_local_decl Γ d :=
    match d.(decl_body) with
    | Some b => typing Γ b (Some d.(decl_type))
    | None => typing Γ d.(decl_type) None
    end.

    Inductive All_local_env : context -> Type :=
    | localenv_nil :
        All_local_env []

    | localenv_cons_abs Γ na t :
        All_local_env Γ ->
        on_local_decl Γ (vass na t) ->
        All_local_env (Γ ,, vass na t)

    | localenv_cons_def Γ na b t :
        All_local_env Γ ->
        on_local_decl Γ (vdef na b t) ->
        All_local_env (Γ ,, vdef na b t).

  End TypeLocal.

  Lemma on_local_decl_impl (P Q : context -> term -> option term -> Type) Γ d :
    on_local_decl P Γ d ->
    (forall Γ t T, P Γ t T -> Q Γ t T) ->
    on_local_decl Q Γ d.
  Proof.
    destruct d as [? [] ?] ; unfold on_local_decl ; simpl ; intuition.
  Qed.

  Lemma All_local_env_impl_wf (P Q : context -> term -> option term -> Type) l :
    All_local_env P l ->
    (forall Γ t T, All_local_env P Γ -> P Γ t T -> Q Γ t T) ->
    All_local_env Q l.
  Proof.
    induction 1 ; intros; simpl ; econstructor ; eauto ; red ; cbn ; auto.
  Qed.

  Lemma All_local_env_impl (P Q : context -> term -> option term -> Type) l :
    All_local_env P l ->
    (forall Γ t T, P Γ t T -> Q Γ t T) ->
    All_local_env Q l.
  Proof.
    intros ; eapply All_local_env_impl_wf ; eauto.
  Qed.

  Lemma All_local_env_skipn P Γ : All_local_env P Γ -> forall n, All_local_env P (skipn n Γ).
  Proof.
    induction 1; simpl; intros; destruct n; simpl; try econstructor; eauto.
  Qed.
  Hint Resolve All_local_env_skipn : wf.


  Arguments localenv_nil {_}.
  Arguments localenv_cons_abs {_ _ _ _} _ _.
  Arguments localenv_cons_def {_ _ _ _ _} _ _.

  (** Well-formedness of local environments embeds a sorting for each variable *)

  Definition lift_typing (P : global_env_ext -> context -> term -> term -> Type) :
  (global_env_ext -> context -> term -> option term -> Type) :=
    fun Σ Γ t T =>
      match T with
      | Some T' => { s : Universe.t & P Σ Γ T' (tSort s) × P Σ Γ t T' }
      | None => { s : Universe.t & P Σ Γ t (tSort s) }
      end.

  Section All_local_env_rel.
    Context (P : forall (Γ : context), term -> option term -> Type).

    Definition All_local_env_rel Γ Γ'
      := (All_local_env (fun Γ0 t T => P (Γ,,,Γ0) t T ) Γ').

    Definition All_local_env_rel_nil {Γ} : All_local_env_rel Γ []
      := localenv_nil.

    Definition All_local_env_rel_cons_abs {Γ Γ' na A} :
      All_local_env_rel Γ Γ' -> on_local_decl P (Γ,,,Γ') (vass na A)
      -> All_local_env_rel Γ (Γ',, vass na A)
    := localenv_cons_abs.

    Definition All_local_env_rel_cons_def {Γ Γ' na t A} :
      All_local_env_rel Γ Γ' -> on_local_decl P (Γ,,,Γ') (vdef na t A)
      -> All_local_env_rel Γ (Γ',, vdef na t A)
      := localenv_cons_def.

    Lemma All_local_env_rel_local :
      forall Γ,
        All_local_env P Γ ->
        All_local_env_rel [] Γ.
    Proof.
      intros Γ h. eapply All_local_env_impl.
      - exact h.
      - intros Δ t d h'.
        rewrite app_context_nil_l. assumption.
    Defined.

    Lemma All_local_local_rel Γ :
      All_local_env_rel [] Γ -> All_local_env P Γ.
    Proof.
      intro X. eapply All_local_env_impl. exact X.
      intros Γ0 t [] XX; cbn in XX; rewrite app_context_nil_l in XX; assumption.
    Defined.

  End All_local_env_rel.

  Section TypeLocalOver.
    Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).
    Context (property : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_typing typing Σ) Γ ->
                forall (t T : term), typing Σ Γ t T -> Type).

    Inductive on_local_decl_over {Σ Γ} (wfΓ : All_local_env (lift_typing typing Σ) Γ) :
      forall (d : context_decl), on_local_decl (lift_typing typing Σ) Γ d -> Type :=
    | decl_abs na t : forall H : on_local_decl (lift_typing typing Σ) Γ (vass na t),
        property Σ Γ wfΓ _ _ H.π2 -> on_local_decl_over wfΓ (vass na t) H
    | decl_def na b t : forall H : on_local_decl (lift_typing typing Σ) Γ (vdef na b t),
        property Σ Γ wfΓ _ _ H.π2.1 -> property Σ Γ wfΓ _ _ H.π2.2 -> on_local_decl_over wfΓ (vdef na b t) H.

    Inductive All_local_env_over (Σ : global_env_ext) :
      forall (Γ : context), All_local_env (lift_typing typing Σ) Γ -> Type :=
    | localenv_over_nil :
        All_local_env_over Σ [] localenv_nil

    | localenv_over_cons_abs Γ na t
        (all : All_local_env (lift_typing typing Σ) Γ) :
        All_local_env_over Σ Γ all ->
        forall (tu : on_local_decl (lift_typing typing Σ) Γ (vass na t)),
          on_local_decl_over all (vass na t) tu ->
          All_local_env_over Σ (Γ ,, vass na t)
                            (localenv_cons_abs all tu)

    | localenv_over_cons_def Γ na b t
        (all : All_local_env (lift_typing typing Σ) Γ) :
        All_local_env_over Σ Γ all ->
        forall (tu : on_local_decl (lift_typing typing Σ) Γ (vdef na b t)),
          on_local_decl_over all (vdef na b t) tu ->
          All_local_env_over Σ (Γ ,, vdef na b t)
                            (localenv_cons_def all tu).

  End TypeLocalOver.

  Section TypeLocalOverRel.
    Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).
    Context (property : forall (Σ : global_env_ext) (Γ Γ' : context),
              All_local_env_rel (lift_typing typing Σ) Γ Γ' ->
              forall (t T : term), typing Σ (Γ,,,Γ') t T -> Type).

    Definition All_local_env_over_rel Σ Γ Γ' (all : All_local_env_rel (lift_typing typing Σ) Γ Γ') : Type.
    Proof.
      refine (All_local_env_over (fun Σ0 Γ0 t T => typing Σ0 (Γ,,,Γ0) t T) _ Σ Γ' all).
      unfold All_local_env_rel in property.
      unfold lift_typing in *.
      simpl.
      exact (fun Σ Γ' => property Σ Γ Γ').
    Defined.

  End TypeLocalOverRel.

  Section TypeLocalOverImpl.

    Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).
    Context (P : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).

  Lemma on_local_decl_over_impl Σ Γ wfΓ d (H : on_local_decl (lift_typing typing Σ) Γ d):
    on_local_decl_over typing (fun Σ' Γ' _ t T _ => P Σ' Γ' t T) wfΓ d H ->
    on_local_decl (lift_typing P Σ) Γ d.
  Proof.
    destruct 1 ; econstructor ; [|split] ; eassumption.
  Qed.

    Lemma All_local_env_over_impl (Σ : global_env_ext) (Γ : context) (wfΓ : All_local_env (lift_typing typing Σ) Γ) :
      All_local_env_over typing (fun Σ' Γ' _ t T _ => P Σ' Γ' t T) Σ Γ wfΓ ->
      All_local_env (lift_typing P Σ) Γ.
    Proof.
      induction 1.
      - constructor.
      - constructor.
        1: assumption.
        eapply on_local_decl_over_impl ; eassumption.
      - constructor.
        1: assumption.
        eapply on_local_decl_over_impl ; eassumption.
    Qed.

  End TypeLocalOverImpl.

End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T).
  Include EnvTyping T E.
End EnvTypingSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (ET : EnvTypingSig T E).

  Import T E ET.

  Parameter Inline ind_guard : mutual_inductive_body -> bool.

  Parameter Inline typing : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type.
  Parameter Inline lift_context : nat -> nat -> context -> context.
  Parameter Inline subst_telescope : list term -> nat -> context -> context.

  Notation " Σ ;;; Γ |- t : T " :=
    (typing Σ Γ t T) (at level 50, Γ, t, T at next level) : type_scope.

  Parameter Inline smash_context : context -> context -> context.

  Notation wf_local Σ Γ := (All_local_env (lift_typing typing Σ) Γ).
  Notation wf_local_rel Σ Γ Γ' := (All_local_env_rel (lift_typing typing Σ) Γ Γ').

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T)
  (ET : EnvTypingSig T E) (Ty : Typing T E ET) (L : LookupSig T E).

  Import T E Ty L ET.

  Definition isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
    { s : _ & Σ ;;; Γ |- t : tSort s }.

  (** *** Typing of inductive declarations *)

  Section GlobalMaps.

    Context {cf: checker_flags}.
    Context (P : global_env_ext -> context -> term -> term -> Type).

    Definition on_context Σ ctx :=
      All_local_env (lift_typing P Σ) ctx.

    (** For well-formedness of inductive declarations we need a way to check that a assumptions
        of a given context is typable in a sort [u]. *)
    Fixpoint type_local_ctx Σ (Γ Δ : context) (u : Universe.t) : Type :=
      match Δ with
      | [] => True
      | {| decl_body := None ; decl_type := t |} :: Δ =>
          type_local_ctx Σ Γ Δ u × P Σ (Γ ,,, Δ) t (tSort u)
      | {| decl_body := Some b ; decl_type := t |} :: Δ =>
          type_local_ctx Σ Γ Δ u × (lift_typing P) Σ (Γ,,, Δ) b (Some t)
      end.

    (* Delta telescope *)
    Inductive ctx_inst Σ (Γ : context) : list term -> context -> Type :=
    | ctx_inst_nil : ctx_inst Σ Γ [] []
    | ctx_inst_ass na t i inst Δ : 
      (lift_typing P) Σ Γ i (Some t) ->
      ctx_inst Σ Γ inst (subst_telescope [i] 0 Δ) ->
      ctx_inst Σ Γ (i :: inst) (vass na t :: Δ)
    | ctx_inst_def na b t inst Δ :
      ctx_inst Σ Γ inst (subst_telescope [b] 0 Δ) ->
      ctx_inst Σ Γ inst (vdef na b t :: Δ).

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : ident * term * nat).

    Definition on_type Σ Γ T := (lift_typing P) Σ Γ T None.

    Record constructor_shape mdecl i idecl ctype cargs :=
    { cshape_args : context;
      (* Arguments (with lets) *)
      cshape_args_length : context_assumptions cshape_args = cargs;
      (* Real (non-let) arguments bound by the constructor *)

        cshape_concl_head := tRel (#|mdecl.(ind_bodies)|
                                  - S i
                                  + #|mdecl.(ind_params)|
                                  + #|cshape_args|);
        (* Conclusion head: reference to the current inductive in the block *)

        cshape_indices : list term;
        (* Indices of the constructor, whose length should be the real arguments
        length of the inductive *)

        cshape_eq : ctype = it_mkProd_or_LetIn mdecl.(ind_params)
                              (it_mkProd_or_LetIn cshape_args
                                (mkApps cshape_concl_head
                                (to_extended_list_k mdecl.(ind_params) #|cshape_args|
                                  ++ cshape_indices)))
        (* The type of the constructor canonically has this shape: parameters, real
          arguments ending with a reference to the inductive applied to the
          (non-lets) parameters and arguments *)
      }.
    Arguments cshape_args {mdecl i idecl ctype cargs}.
    Arguments cshape_args_length {mdecl i idecl ctype cargs}.
    Arguments cshape_indices {mdecl i idecl ctype cargs}.
    Arguments cshape_eq {mdecl i idecl ctype cargs}.

    Open Scope type_scope.

    Record on_constructor Σ mdecl i idecl ind_indices cdecl ind_ctor_sort := {
      (* cdecl.1 fresh ?? *)
      cshape : constructor_shape mdecl i idecl cdecl.1.2 cdecl.2;            
      on_ctype : on_type Σ (arities_context mdecl.(ind_bodies)) cdecl.1.2;
      on_cargs : (* FIXME: there is some redundancy with the type_local_ctx *)
        type_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cshape.(cshape_args) ind_ctor_sort;
      on_cindices : 
        ctx_inst Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cshape.(cshape_args))
                      cshape.(cshape_indices)
                      (List.rev (lift_context #|cshape.(cshape_args)| 0 ind_indices))
        }.

    Arguments cshape {Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.
    Arguments on_ctype {Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.
    Arguments on_cargs {Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.
    Arguments on_cindices {Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.

    Definition on_constructors Σ mdecl i idecl ind_indices :=
      All2 (on_constructor Σ mdecl i idecl ind_indices).

    (** Projections have their parameter context smashed to avoid costly computations
        during type-checking. *)
    (**  Removed this because we cannot yet prove that if Γ is wf then its smashed version too*)

    Definition on_projection Σ mind mdecl i idecl
              (k : nat) (p : ident * term) :=
      let ctx := mdecl.(ind_params) in
      let Γ := ctx,, vass (nNamed idecl.(ind_name))
                  (mkApps (tInd (mkInd mind i) (polymorphic_instance mdecl.(ind_universes)))
                          (to_extended_list ctx))
      (* FIXME: more on p? *)
      in on_type Σ Γ (snd p).

    Record on_projections Σ mind mdecl i idecl (indices : context) :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;
        (** The inductive must be a record *)

        on_projs_noidx : #|indices| = 0;
        (** The inductive cannot have indices *)

        on_projs_elim : idecl.(ind_kelim) = InType;
        (** This ensures that all projections are definable *)

        on_projs : Alli (on_projection Σ mind mdecl i idecl) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ ind_ctors_sort ind_sort :=
      Forall (fun s => leq_universe φ s ind_sort) ind_ctors_sort.

    (** This ensures that all sorts in kelim are lower
        or equal to the top elimination sort, if set.
        For inductives in Type we do not check [kelim] currently. *)

    Fixpoint elim_sort_prop_ind ind_ctors_sort :=
      match ind_ctors_sort with
      | [] => (* Empty inductive proposition: *) InType
      | [ s ] => match universe_family s with
                | InProp => (* Not squashed: all arguments are in Prop  *)
                  (* This is singleton elimination *) InType
                | _ => (* Squashed: some arguments are higher than Prop,
                        restrict to Prop *) InProp
                end
      | _ => (* Squashed: at least 2 constructors *) InProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices ind_ctors_sort ind_sort : Type :=
      match universe_family ind_sort with
      | InProp =>
        (** The inductive is declared in the impredicative sort Prop *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        leb_sort_family kelim (elim_sort_prop_ind ind_ctors_sort)
      | _ =>
        (** The inductive is predicative: check that all constructors arguments are
            smaller than the declared universe. *)
        check_constructors_smaller Σ ind_ctors_sort ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True
      end.

    Record on_ind_body Σ mind mdecl i idecl :=
      { (** The type of the inductive must be an arity, sharing the same params
            as the rest of the block, and maybe having a context of indices. *)
        ind_indices : context;
        ind_sort : Universe.t;
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn ind_indices (tSort ind_sort));

        (** It must be well-typed in the empty context. *)
        onArity : on_type Σ [] idecl.(ind_type);

        (** There is a sort bounding the indices and arguments for each constructor *)
        ind_ctors_sort : list Universe.t;

        (** Constructors are well-typed *)
        onConstructors :
          on_constructors Σ mdecl i idecl ind_indices idecl.(ind_ctors) ind_ctors_sort;

        (** Projections, if any, are well-typed *)
        onProjections :
          idecl.(ind_projs) <> [] -> on_projections Σ mind mdecl i idecl ind_indices;

        (** The universes and elimination sorts must be correct w.r.t.
            the universe of the inductive and the universes in its constructors, which
            are declared in [on_constructors]. *)
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          ind_indices ind_ctors_sort ind_sort;
      }.

    (** We allow empty blocks for simplicity
        (no well-typed reference to them can be made). *)

    Record on_inductive Σ mind mdecl :=
      { onInductives : Alli (on_ind_body Σ mind mdecl) 0 mdecl.(ind_bodies);
        (** We check that the context of parameters is well-formed and that
            the size annotation counts assumptions only (no let-ins). *)
        onParams : on_context Σ mdecl.(ind_params);
        onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
        onGuard : ind_guard mdecl
      }.

    (** *** Typing of constant declarations *)

    Definition on_constant_decl Σ d :=
      match d.(cst_body) with
      | Some trm => (lift_typing P) Σ [] trm (Some d.(cst_type))
      | None => on_type Σ [] d.(cst_type)
      end.

    Definition on_global_decl Σ kn decl :=
      match decl with
      | ConstantDecl d => on_constant_decl Σ d
      | InductiveDecl inds => on_inductive Σ kn inds
      end.

    (** *** Typing of global environment

        All declarations should be typeable and the global
        set of universe constraints should be consistent. *)

    (** Well-formed global environments have no name clash. *)

    Definition fresh_global (s : kername) : global_env -> Prop :=
      Forall (fun g => g.1 <> s).

    Definition satisfiable_udecl `{checker_flags} Σ φ
      := consistent (global_ext_constraints (Σ, φ)).

    (* Check that: *)
    (*   - declared levels are fresh *)
    (*   - all levels used in constraints are declared *)
    (*   - level used in monomorphic contexts are only monomorphic *)
    Definition on_udecl `{checker_flags} Σ (udecl : universes_decl)
      := let levels := levels_of_udecl udecl in
        let global_levels := global_levels Σ in
        let all_levels := LevelSet.union levels global_levels in
        LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels
        /\ ConstraintSet.For_all (fun '(l1,_,l2) => LevelSet.In l1 all_levels
                                                /\ LevelSet.In l2 all_levels)
                                (constraints_of_udecl udecl)
        /\ match udecl with
          | Monomorphic_ctx ctx =>  LevelSet.for_all (negb ∘ Level.is_var) ctx.1
          | _ => True
          end
        /\ satisfiable_udecl Σ udecl.


    Inductive on_global_env `{checker_flags} : global_env -> Type :=
    | globenv_nil : on_global_env []
    | globenv_decl Σ kn d :
        on_global_env Σ ->
        fresh_global kn Σ ->
        let udecl := universes_decl_of_decl d in
        on_udecl Σ udecl ->
        on_global_decl (Σ, udecl) kn d ->
        on_global_env (Σ ,, (kn, d)).

    Definition on_global_env_ext `{checker_flags} (Σ : global_env_ext) :=
      on_global_env Σ.1 × on_udecl Σ.1 Σ.2.

  End GlobalMaps.

  Arguments cshape_args {mdecl i idecl ctype cargs}.
  Arguments cshape_args_length {mdecl i idecl ctype cargs}.
  Arguments cshape_indices {mdecl i idecl ctype cargs}.
  Arguments cshape_eq {mdecl i idecl ctype cargs}.
  Arguments cshape {P Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.
  Arguments on_ctype {P Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.
  Arguments on_cargs {P Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.
  Arguments on_cindices {P Σ mdecl i idecl ind_indices cdecl ind_ctor_sort}.

  Lemma Alli_impl_trans : forall (A : Type) (P Q : nat -> A -> Type) (l : list A) (n : nat),
  Alli P n l -> (forall (n0 : nat) (x : A), P n0 x -> Q n0 x) -> Alli Q n l.
  Proof.
    intros. induction X; simpl; constructor; auto.
  Defined.

  Lemma type_local_ctx_impl (P Q : global_env_ext -> context -> term -> term -> Type) Σ Γ Δ u :
    type_local_ctx P Σ Γ Δ u ->
    (forall Δ' t T, type_local_ctx P Σ Γ Δ' u -> P Σ (Γ,,,Δ') t T -> Q Σ (Γ,,,Δ') t T) ->
    type_local_ctx Q Σ Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    1: intros [? [ ]].
    all: intuition eauto.
  Qed.

  Lemma type_local_ctx_All_local_env (P : global_env_ext -> context -> term -> term -> Type) Σ Γ Δ u :
    All_local_env ((lift_typing P) Σ) Γ ->
    type_local_ctx P Σ Γ Δ u ->
    All_local_env ((lift_typing P) Σ) (Γ,,,Δ).
  Proof.
    intros wfΓ.
    induction Δ as [| [? []]]; simpl ; auto.
    - intros [? [s []]] ; constructor.
      1: auto.
      simpl ; exists s ; auto.
    - intros [] ; constructor.
      1: auto.
      exists u ; auto.
  Qed. 

  (** This predicate enforces that there exists typing derivations for every typable term in env. *)

  Definition Forall_decls_typing `{checker_flags}
            (P : global_env_ext -> context -> term -> term -> Type)
    := on_global_env P.

  (** *** Typing of local environments *)

  (* Definition type_local_decl `{checker_flags} Σ Γ d :=
    match d.(decl_body) with
    | None => isType Σ Γ d.(decl_type)
    | Some body => Σ ;;; Γ |- body : d.(decl_type)
    end. *)

  (** ** Induction principle for typing up-to a global environment *)

  Lemma refine_type `{checker_flags} Σ Γ t T U : Σ ;;; Γ |- t : T -> T = U -> Σ ;;; Γ |- t : U.
  Proof. now intros Ht ->. Qed.

  Section All_local_env_size.
    Context (P : global_env_ext -> context -> term -> term -> Type).
    Context (fn : forall (Σ : global_env_ext) (Γ : context) (t T : term), P Σ Γ t T -> size).
    Context (Σ : global_env_ext).

    Fixpoint All_local_env_size Γ (w : All_local_env (lift_typing P Σ) Γ) : size :=
      match w with
      | localenv_nil => 0
      | localenv_cons_abs Γ na t wfΓ h => fn _ _ _ _ h.π2 + All_local_env_size _ wfΓ
      | localenv_cons_def Γ na b t wfΓ h => fn _ _ _ _ h.π2.1 + fn _ _ _ _ h.π2.2 + All_local_env_size _ wfΓ
      end.

  End All_local_env_size.

  Section All_local_env_rel_size.
    Context (P : global_env_ext -> context -> term -> term -> Type).
    Context (fn : forall (Σ : global_env_ext) (Γ : context) (t T : term), P Σ Γ t T -> size).
    Context (Σ : global_env_ext).

    Definition All_local_env_rel_size Γ Γ' (w : All_local_env_rel (lift_typing P Σ) Γ Γ') : size :=
      All_local_env_size 
        (fun Σ Γ0 t T => P Σ (Γ,,,Γ0) t T)
        (fun Σ Γ0 t T d => fn Σ (Γ,,,Γ0) t T d) Σ Γ' w.

  End All_local_env_rel_size.

  Section wf_local_size.

    Context `{checker_flags} (Σ : global_env_ext).
    Context (fn : forall (Σ : global_env_ext) (Γ : context) (t T : term), typing Σ Γ t T -> size).

    Definition wf_local_size Γ (w : wf_local Σ Γ) : size :=
      All_local_env_size typing fn Σ Γ w.

    Definition wf_local_rel_size Γ Γ' (w : wf_local_rel Σ Γ Γ') : size :=
      All_local_env_rel_size typing fn Σ Γ Γ' w. 
    
  End wf_local_size.

  Section All_local_env.
  (** * Lemmas about All_local_env *)
    Context {cf: checker_flags}.

    Lemma nth_error_All_local_env {P Γ n} (isdecl : n < #|Γ|) :
      All_local_env P Γ ->
      on_some (on_local_decl P (skipn (S n) Γ)) (nth_error Γ n).
    Proof.
      induction 1 in n, isdecl |- *. red; simpl.
      - destruct n; simpl; inv isdecl.
      - destruct n. red; simpl. assumption.
        simpl. apply IHX. simpl in isdecl. lia.
      - destruct n. red; simpl. assumption.
      simpl. apply IHX. simpl in isdecl. lia.
    Qed.

    (* Lemma lookup_on_global_env P Σ c decl :
      on_global_env P Σ ->
      lookup_env Σ c = Some decl ->
      { Σ' & { wfΣ' : on_global_env P Σ'.1 & on_global_decl P Σ' c decl } }.
    Proof.
      induction 1; simpl. congruence.
      destruct (eq_kername_spec c kn); subst.
      intros [= ->].
      exists (Σ, udecl). exists X. auto.
      apply IHX.
    Qed. *)

    Lemma All_local_env_app_aux P Σ Γ Γ' (all : All_local_env (lift_typing P Σ) (Γ ,,, Γ')) :
      {p : All_local_env (lift_typing P Σ) Γ × All_local_env_rel (lift_typing P Σ) Γ Γ' & forall fn,
        All_local_env_size P fn Σ (Γ,,,Γ') all = All_local_env_size P fn Σ Γ p.1 + All_local_env_rel_size P fn Σ Γ Γ' p.2}.
    Proof.
      induction Γ'.
      2: dependent destruction all.
      - unshelve eexists.
        + subst ; split ; [assumption|constructor].
        + intros. simpl. lia.
      - specialize (IHΓ' all) ; destruct IHΓ' as [[]].
        unshelve eexists.
        + split ; [|constructor] ; assumption.
        + intros fn ; cbn ; rewrite e ; unfold All_local_env_rel_size ; cbn ; lia.
      - specialize (IHΓ' all) ; destruct IHΓ' as [[]].
        unshelve eexists.
        + split ; [|constructor] ; assumption.
        + intros fn ; cbn ; rewrite e ; unfold All_local_env_rel_size ; cbn ; lia.
    Defined.

    Definition All_local_env_app {P Σ Γ Γ'} (all : All_local_env (lift_typing P Σ) (Γ ,,, Γ')) :
      All_local_env (lift_typing P Σ) Γ × All_local_env_rel (lift_typing P Σ) Γ Γ' :=
      (All_local_env_app_aux P Σ Γ Γ' all).π1.

    Lemma All_local_env_app_size {P} fn {Σ Γ Γ'} (all : All_local_env (lift_typing P Σ) (Γ ,,, Γ')) :
      let p := All_local_env_app all in
      All_local_env_size P fn Σ (Γ,,,Γ') all = All_local_env_size P fn Σ Γ p.1 + All_local_env_rel_size P fn Σ Γ Γ' p.2.
    Proof.
      apply (All_local_env_app_aux P Σ Γ Γ' all).π2.
    Qed.

    Lemma All_local_env_lookup {P Γ n} {decl} :
      All_local_env P Γ ->
      nth_error Γ n = Some decl ->
      on_local_decl P (skipn (S n) Γ) decl.
    Proof.
      induction 1 in n, decl |- *. simpl. destruct n; simpl; congruence.
      destruct n. red. simpl. intros [= <-]. assumption.
      simpl in *. eapply IHX.
      destruct n. red. simpl. intros [= <-]. assumption.
      simpl in *. eapply IHX.
    Qed.

    Lemma All_local_env_app_inv (P : context -> term -> option term -> Type) Γ Γ' :
      All_local_env P Γ × All_local_env_rel P Γ Γ' ->
      All_local_env P (Γ ,,, Γ').
    Proof.
      induction Γ'; simpl; auto. intuition.
      intuition. destruct a. destruct decl_body0.
      all: inv b ; econstructor; eauto.
      Qed.


    Definition wf_local_rel_app_inv {Σ Γ1 Γ2 Γ3} :
      All_local_env_rel Σ Γ1 Γ2 -> All_local_env_rel Σ (Γ1 ,,, Γ2) Γ3
      -> All_local_env_rel Σ Γ1 (Γ2 ,,, Γ3).
    Proof.
      intros h1 h2. eapply All_local_env_app_inv.
      split.
      - assumption.
      - eapply All_local_env_impl.
        + eassumption.
        + intros Γ t []; cbn;
          now rewrite app_context_assoc.
    Defined.


    Lemma All_local_env_map (P : context -> term -> option term -> Type) f Γ :
      (forall u, f (tSort u) = tSort u) ->
      All_local_env (fun Γ t T => P (map (map_decl f) Γ) (f t) (option_map f T)) Γ
      -> All_local_env P (map (map_decl f) Γ).
    Proof.
      intros Hf. induction 1 ; econstructor ; eauto.
    Qed.

    Definition lookup_All_local_env {Γ P} (wfΓ : All_local_env P Γ) (n : nat)
              (isdecl : n < #|Γ|) :
      All_local_env P (skipn (S n) Γ).
    Proof.
      induction wfΓ in n, isdecl |- *; simpl.
      - constructor.
      - cbn -[skipn] in *. destruct n.
        simpl. exact wfΓ.
        apply IHwfΓ. auto with arith.
      - cbn -[skipn] in *. destruct n.
        simpl. exact wfΓ.
        apply IHwfΓ. auto with arith.
    Defined.

    Definition lookup_wf_local_decl {Γ P} (wfΓ : All_local_env P Γ) (n : nat)
              {decl} (eq : nth_error Γ n = Some decl) :
      ∑ Pskip : All_local_env P (skipn (S n) Γ),
              on_local_decl P (skipn (S n) Γ) decl.
    Proof.
      induction wfΓ in n, decl, eq |- *; simpl.
      - elimtype False. destruct n; depelim eq.
      - destruct n.
        + simpl. exists wfΓ. injection eq; intros <-. assumption.
        + apply IHwfΓ. auto with arith.
      - destruct n.
        + simpl. exists wfΓ. injection eq; intros <-. assumption.
        + apply IHwfΓ. auto with arith.
    Defined.

    Lemma nth_error_All_local_env_over {P Σ Γ n decl} (eq : nth_error Γ n = Some decl) {wfΓ : All_local_env (lift_typing typing Σ) Γ} :
      All_local_env_over typing P Σ Γ wfΓ ->
      let Γ' := skipn (S n) Γ in
      let p := lookup_wf_local_decl wfΓ n eq in
      (All_local_env_over typing P Σ Γ' (projT1 p) × on_local_decl_over typing P (projT1 p) _ (projT2 p)).
    Proof.
      induction 1 in n, decl, eq |- *. simpl.
      - destruct n; simpl; elimtype False; discriminate eq.
      - destruct n. cbn [skipn]. noconf eq. split. apply X. simpl. assumption.
        simpl. apply IHX.
      - destruct n. cbn [skipn]. noconf eq. split. apply X. simpl. assumption.
        simpl. apply IHX.
    Defined.

    Lemma All_local_env_prod_inv :
      forall P Q Γ,
        All_local_env (fun Δ A t => P Δ A t × Q Δ A t) Γ ->
        All_local_env P Γ × All_local_env Q Γ.
    Proof.
      intros P Q Γ h.
      induction h.
      - split ; constructor.
      - destruct IHh.
        split ; constructor ; red in o ; simpl in o ; intuition.
      - destruct IHh.
        split ; constructor ; red in o ; simpl in o ; intuition.
    Qed.

    Lemma All_local_env_lift_prod_inv :
      forall Σ P Q Δ,
        All_local_env (lift_typing (fun Σ Γ t A => P Σ Γ t A × Q Σ Γ t A) Σ) Δ ->
        All_local_env (lift_typing P Σ) Δ × All_local_env (lift_typing Q Σ) Δ.
    Proof.
      intros Σ P Q Δ h.
      induction h.
      - split ; constructor.
      - destruct IHh.
        destruct o as [? []] ; simpl in *.
        split ; constructor ; auto.
        all: cbn ; eexists ; eassumption.
      - destruct IHh.
        destruct o as [? [[] []]].
        split ; constructor ; auto.
        all: cbn ; eexists ; split ; eassumption.
    Qed.

  End All_local_env.

End DeclarationTyping.
