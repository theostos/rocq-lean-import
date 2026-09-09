From LeanImport Require Import Lean.

(* A fake projection used in the type of a later field must be lifted under
   the dependent case predicate, including after a universe becomes SProp. *)
(* Check the SProp instance eagerly, including its dependent Type recursor. *)
Set Lean Error Mode "Fail".
Set Lean Upfront Instantiation.
Lean Import "../dumps/dependent_sprop_projection".

Check subtypeSPropProperty :
  forall (A : SProp) (p : A -> SProp) (s : Subtype_inst1 A p),
    p (Subtype_val_inst1 A p s).

(* A nondependent scheme is not a substitute for Lean's dependent recursor. *)
Check Subtype_inst1_recl :
  forall (A : SProp) (p : A -> SProp)
    (motive : Subtype_inst1 A p -> Type),
    (forall (x : A) (h : p x), motive (Subtype_mk_inst1 A p x h)) ->
    forall s : Subtype_inst1 A p, motive s.
