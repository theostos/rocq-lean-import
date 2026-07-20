From Stdlib Require Import NArith.
From LeanImport Require Import Lean.

Example large_nat_blt_certificate :
  BoolCertificate
    (Nat_blt (Nat_of_N 99999999%N) (Nat_of_N 100000000%N)) true.
Proof.
  change (BoolCertificate
    (Nat_blt (Nat_of_N 99999999%N) (Nat_of_N 100000000%N))
    (N.ltb 99999999 100000000)).
  apply NatCertificate_blt; apply NatCertificate_of_N.
Qed.

Example large_nat_beq_certificate :
  BoolCertificate
    (Nat_beq (Nat_of_N 100000000%N) (Nat_of_N 100000000%N)) true.
Proof.
  change (BoolCertificate
    (Nat_beq (Nat_of_N 100000000%N) (Nat_of_N 100000000%N))
    (N.eqb 100000000 100000000)).
  apply NatCertificate_beq; apply NatCertificate_of_N.
Qed.

Example large_nat_ble_certificate :
  BoolCertificate
    (Nat_ble (Nat_of_N 100000000%N) (Nat_of_N 99999999%N)) false.
Proof.
  change (BoolCertificate
    (Nat_ble (Nat_of_N 100000000%N) (Nat_of_N 99999999%N))
    (N.leb 100000000 99999999)).
  apply NatCertificate_ble; apply NatCertificate_of_N.
Qed.
