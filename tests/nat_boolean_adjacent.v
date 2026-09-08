From LeanImport Require Import Lean.
Set Kernel Conversion Dep Heuristic.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Unset Lean Lazy Instantiation.
Set Lean Line Timeout 30.
Lean Import "../dumps/nat_boolean_adjacent".
Check Nat_beq_refl.
Check Nat_beq_eq.
Check Nat_ble_eq.
Check Nat_blt_eq.
