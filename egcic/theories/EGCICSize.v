From MetaCoq.Template Require Import utils.
From MetaCoq.EGCIC Require Import EGCICAst.
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
  | eRel i => 1
  | eEvar ev args => S (list_size size args)
  | eLambda na T M => S (size T + size M)
  | eApp u v => S (size u + size v)
  | eProd na A B => S (size A + size B)
  | eLetIn na b t b' => S (size b + size t + size b')
  | eCase ind p c brs => S (size p + size c + list_size (fun x => size (snd x)) brs)
  | eProj p c => S (size c)
  | eFix mfix idx => S (mfixpoint_size size mfix)
  | eCoFix mfix idx => S (mfixpoint_size size mfix)
  | eErr _ A => S (size A)
  | eCast t A B => S (size A + size B + size t)
  | x => 1
  end.
