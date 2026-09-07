From LeanImport Require Import Lean.

(* A fake projection used in the type of a later field must be lifted under
   the dependent case predicate, including after a universe becomes SProp. *)
(* The final check names a projection instance not referenced by the dump. *)
Set Lean Upfront Instantiation.
Lean Import "../dumps/dependent_sprop_projection".

Check subtypeSPropProperty :
  forall (A : SProp) (p : A -> SProp) (s : Subtype_inst1 A p),
    p (Subtype_val_inst1 A p s).
