From LeanImport Require Import Lean.
Require Import nat_boolean_source_prefix.
Set Kernel Conversion Dep Heuristic.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Unset Lean Lazy Instantiation.
Set Lean Line Timeout 30.
Lean Import "../dumps/nat_boolean_source" 1127.
Check Nat_beq_eq_def.
