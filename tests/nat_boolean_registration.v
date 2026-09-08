From LeanImport Require Import Lean.
From Stdlib Require Import NArith.BinNat.
Require Import nat_boolean_source.
Set Kernel Conversion Dep Heuristic.

(* The source's recursive-history implementation must survive import. *)
Fail Definition replaced_source : @Logic.eq (Nat -> Nat -> Bool)
  nat_boolean_source.Nat_beq Lean.Nat_beq := Logic.eq_refl nat_boolean_source.Nat_beq.

(* Registration works for an arbitrary transparent alias; no theorem name
   participates in validating the computation rules. *)
Definition renamed_compare := nat_boolean_source.Nat_beq.
Register renamed_compare as kernel.peano_nat_beq.

Definition huge := CompactNat 18446744073709551616%N.
Definition previous := CompactNat 18446744073709551615%N.
Goal eq (nat_boolean_source.Nat_beq huge huge) Bool_true.
Proof. exact_no_check (eq_refl Bool_true). Timeout 5 Qed.
Goal eq (nat_boolean_source.Nat_beq huge previous) Bool_false.
Proof. exact_no_check (eq_refl Bool_false). Timeout 5 Qed.
Goal eq (renamed_compare previous huge) Bool_false.
Proof. exact_no_check (eq_refl Bool_false). Timeout 5 Qed.
Goal eq (nat_boolean_source.Nat_beq huge previous) Bool_true.
Proof. exact_no_check (eq_refl Bool_true). Fail Qed. Abort.

(* Each bad definition violates a different defining equation. *)
Definition wrong_zero_zero (n m : Nat) := Bool_false.
Fail Register wrong_zero_zero as kernel.peano_nat_beq.
Definition wrong_zero_succ (n m : Nat) :=
  match n with Nat_zero => Bool_true | Nat_succ _ => Bool_false end.
Fail Register wrong_zero_succ as kernel.peano_nat_beq.
Definition wrong_succ_zero (n m : Nat) :=
  match m with Nat_zero => Bool_true | Nat_succ _ => Bool_false end.
Fail Register wrong_succ_zero as kernel.peano_nat_beq.
Definition wrong_succ_succ (n m : Nat) :=
  match n, m with Nat_zero, Nat_zero => Bool_true | _, _ => Bool_false end.
Fail Register wrong_succ_succ as kernel.peano_nat_beq.

Definition opaque_compare : Nat -> Nat -> Bool.
Proof. exact nat_boolean_source.Nat_beq. Qed.
Fail Register opaque_compare as kernel.peano_nat_beq.
