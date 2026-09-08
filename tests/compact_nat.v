From Stdlib Require Import NArith.BinNat.
From LeanImport Require Import Lean.

Example compact_nat_exposes_one_constructor :
  eq (CompactNat 1000000%N) (Nat_succ (CompactNat 999999%N)).
Proof. reflexivity. Qed.
