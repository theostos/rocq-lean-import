From Stdlib Require Import NArith.
From LeanImport Require Import Lean.

(* The certificate stays logarithmic in these values: Rocq checks binary [N]
   arithmetic instead of reducing Lean's unary [Nat.sub]. *)
Example large_nat_sub_certificate :
  NatCertificate
    (Nat_sub (Nat_of_N 100000000%N) (Nat_of_N 99999999%N)) 1%N.
Proof.
  change (NatCertificate
    (Nat_sub (Nat_of_N 100000000%N) (Nat_of_N 99999999%N))
    (100000000 - 99999999)%N).
  apply NatCertificate_sub; apply NatCertificate_of_N.
Qed.

Example truncated_nat_sub_certificate :
  NatCertificate (Nat_sub (Nat_of_N 3%N) (Nat_of_N 10%N)) 0%N.
Proof.
  change (NatCertificate (Nat_sub (Nat_of_N 3%N) (Nat_of_N 10%N))
    (3 - 10)%N).
  apply NatCertificate_sub; apply NatCertificate_of_N.
Qed.
