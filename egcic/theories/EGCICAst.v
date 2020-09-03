(* Distributed under the terms of the MIT license.   *)

Require Import List. Import ListNotations.
From MetaCoq.Template Require Export Universes BasicAst Environment.

Declare Scope egcic.
Delimit Scope egcic with egcic.
Open Scope egcic.

(** * AST of the Explicit Gradual Calculus of Inductive Constructions

   This AST is an extension of the one of PCUIC with (explicit) gradual constructions. *)

Inductive err_type : Set :=
  | ukn : err_type
  | rai : err_type.

Inductive term :=
| eRel (n : nat)
| eVar (i : ident) (* For free variables (e.g. in a goal) *)
| eEvar (n : nat) (l : list term)
| eSort (u : Universe.t)
| eProd (na : name) (A B : term)
| eLambda (na : name) (A t : term)
| eLetIn (na : name) (b B t : term) (* let na := b : B in t *)
| eApp (u v : term)
| eConst (k : kername) (ui : Instance.t)
| eInd (ind : inductive) (ui : Instance.t)
| eConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| eCase (indn : inductive * nat) (p c : term) (brs : list (nat * term)) (* # of parameters/type info/discriminee/branches *)
| eProj (p : projection) (c : term)
| eFix (mfix : mfixpoint term) (idx : nat)
| eCoFix (mfix : mfixpoint term) (idx : nat)
| eErr (e : err_type) (A : term)
| eCast (A B t : term).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (eApp t u) us
  end.

Definition isApp t :=
  match t with
  | eApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | eLambda _ _ _ => true
  | _ => false
  end.

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universes_decl }.

Record definition_entry := {
  definition_entry_type      : term;
  definition_entry_body      : term;
  definition_entry_universes : universes_decl;
  definition_entry_opaque    : bool }.


Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

(** *** Inductive entries *)

(** This is the representation of mutual inductives.
    nearly copied from [kernel/entries.mli]

  Assume the following definition in concrete syntax:

[[
  Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
  ...
  with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1  ... | cpnp : Tpnp.
]]

  then, in [i]th block, [mind_entry_params] is [xn:Xn;...;x1:X1];
  [mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
  [mind_entry_lc] is [Ti1;...;Tini], defined in context
  [A'1;...;A'p;x1:X1;...;xn:Xn] where [A'i] is [Ai] generalized over
  [x1:X1;...;xn:Xn].
*)

Inductive local_entry :=
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.

Record one_inductive_entry := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term (* constructor list *) }.

Record mutual_inductive_entry := {
  mind_entry_record    : option (option ident);
  (* Is this mutual inductive defined as a record?
     If so, is it primitive, using binder name [ident]
     for the record in primitive projections ? *)
  mind_entry_finite    : recursivity_kind;
  mind_entry_params    : list (ident * local_entry);
  mind_entry_inds      : list one_inductive_entry;
  mind_entry_universes : universes_decl;
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by Template Coq yet. *) }.

Module EGCICTerm <: Term.

  Definition term := term.

  Definition tRel := eRel.
  Definition tSort := eSort.
  Definition tProd := eProd.
  Definition tLetIn := eLetIn.
  Definition tInd := eInd.
  Definition tLambda := eLambda.

  Definition mkApps := mkApps.
  Definition tProj := eProj.

End EGCICTerm.

Ltac unf_term := unfold EGCICTerm.term in *; unfold EGCICTerm.tRel in *;
unfold EGCICTerm.tSort in *; unfold EGCICTerm.tProd in *;
unfold EGCICTerm.tLambda in *; unfold EGCICTerm.tLetIn in *;
unfold EGCICTerm.tInd in * ; unfold EGCICTerm.tProj.

Module EGCICEnvironment := Environment EGCICTerm.
Include EGCICEnvironment.

Close Scope egcic.