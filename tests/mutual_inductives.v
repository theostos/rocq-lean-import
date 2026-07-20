From LeanImport Require Import Lean.

Lean Import "../dumps/mutual_inductives".

Check mutualExample : Nat.
Check mutualFoldTree : MutTree -> Nat.

Example mutualExample_computes : mutualExample = 2.
Proof. cbv. reflexivity. Qed.
