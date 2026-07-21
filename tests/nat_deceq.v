From LeanImport Require Import Lean.

Example nat_deceq_equal_computes :
  Logic.eq
    (match Nat_decEq (Nat_succ Nat_zero) (Nat_succ Nat_zero) with
     | Decidable_isFalse _ _ => Bool_false
     | Decidable_isTrue _ _ => Bool_true
     end)
    Bool_true.
Proof. reflexivity. Qed.

Example nat_deceq_distinct_computes :
  Logic.eq
    (match Nat_decEq Nat_zero (Nat_succ Nat_zero) with
     | Decidable_isFalse _ _ => Bool_false
     | Decidable_isTrue _ _ => Bool_true
     end)
    Bool_false.
Proof. reflexivity. Qed.
