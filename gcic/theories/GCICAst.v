(* Distributed under the terms of the MIT license.   *)

Require Import List. Import ListNotations.
From MetaCoq.Template Require Export Universes BasicAst Environment.

(* Declare Scope GCIC.*)
Declare Scope gcic.
Delimit Scope gcic with gcic.
Open Scope gcic.

(** * AST of the Gradual Calculus of Inductive Constructions

   This AST is an extension of the one of PCUIC with gradual constructions. *)
   
Inductive term :=
| gRel (n : nat)
| gVar (i : ident) (* For free variables (e.g. in a goal) *)
| gEvar (n : nat) (l : list term)
| gSort (u : Universe.t)
| gProd (na : name) (A B : term)
| gLambda (na : name) (A t : term)
| gLetIn (na : name) (b B t : term) (* let na := b : B in t *)
| gApp (u v : term)
| gConst (k : kername) (ui : Instance.t)
| gInd (ind : inductive) (ui : Instance.t)
| gConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| gCase (indn : inductive * nat) (p c : term) (brs : list (nat * term)) (* # of parameters/type info/discriminee/branches *)
| gProj (p : projection) (c : term)
| gFix (mfix : mfixpoint term) (idx : nat)
| gCoFix (mfix : mfixpoint term) (idx : nat)
| gUkn (A : term)
| gCast (A t : term).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (gApp t u) us
  end.

Definition isApp t :=
  match t with
  | gApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | gLambda _ _ _ => true
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


  Module GCICTerm <: Term.

    Definition term := term.

    Definition tRel := gRel.
    Definition tSort := gSort.
    Definition tProd := gProd.
    Definition tLetIn := gLetIn.
    Definition tInd := gInd.
    Definition tLambda := gLambda.

    Definition mkApps := mkApps.
    Definition tProj := gProj.

  End GCICTerm.

Ltac unf_term := unfold GCICTerm.term in *; unfold GCICTerm.tRel in *;
                  unfold GCICTerm.tSort in *; unfold GCICTerm.tProd in *;
                  unfold GCICTerm.tLambda in *; unfold GCICTerm.tLetIn in *;
                  unfold GCICTerm.tInd in * ; unfold GCICTerm.tProj.

  Module GCICEnvironment := Environment GCICTerm.
  Include GCICEnvironment.

Close Scope gcic.