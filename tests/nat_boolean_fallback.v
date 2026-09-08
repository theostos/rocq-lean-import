From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Set Lean Line Timeout 30.

(* This existing fixture uses a valid source Nat.ble whose open reduction
   equations differ from those required by the compact-operation validator. *)
Lean Import "../dumps/anomaly_print_projections" 1 2590.
Check Nat_ble : Nat -> Nat -> Bool.
Fail Register Nat_ble as kernel.peano_nat_ble.
Example source_ble_still_computes :
  Lean.eq (Nat_ble Nat_zero Nat_zero) Bool_true := Lean.eq_refl _.
