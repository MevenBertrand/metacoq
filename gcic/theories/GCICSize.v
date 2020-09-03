From MetaCoq.Template Require Import utils.
From MetaCoq.GCIC Require Import GCICAst.
Import List.ListNotations.

From Equations Require Import Equations.

Set Asymmetric Patterns.

Derive NoConfusion for term.
Derive Signature for All2.


Definition def_size (size : term -> nat) (x : def term) := size (dtype x) + size (dbody x).
Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.

Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Fixpoint size t : nat :=
  match t with
  | gRel i => 1
  | gEvar ev args => S (list_size size args)
  | gLambda na T M => S (size T + size M)
  | gApp u v => S (size u + size v)
  | gProd na A B => S (size A + size B)
  | gLetIn na b t b' => S (size b + size t + size b')
  | gCase ind p c brs => S (size p + size c + list_size (fun x => size (snd x)) brs)
  | gProj p c => S (size c)
  | gFix mfix idx => S (mfixpoint_size size mfix)
  | gCoFix mfix idx => S (mfixpoint_size size mfix)
  | gUkn A => S (size A)
  | gCast A t => S (size A + size t)
  | x => 1
  end.
