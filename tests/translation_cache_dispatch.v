From LeanImport Require Import Lean.
Set Kernel Conversion Dep Heuristic.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Unset Lean Lazy Instantiation.
Set Lean Line Timeout 30.

(* Nat.recAux reuses a source expression after its first translation creates
   a specialized HAdd projection. Exact cache validation must still pass. *)
Lean Import "../dumps/nat_boolean_adjacent" 1 801.
Check Nat_recAux.
