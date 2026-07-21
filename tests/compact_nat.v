From Stdlib Require Import NArith.
From LeanImport Require Import Lean.

Example compact_nat_large_certificate :
  NatCertificate (CompactNat 100000000%N) 100000000%N.
Proof. apply NatCertificate_CompactNat. Qed.

Example compact_nat_exposes_one_constructor :
  eq (CompactNat 1000000%N) (Nat_succ (CompactNat 999999%N)).
Proof. reflexivity. Qed.
