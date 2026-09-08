From LeanImport Require Import Lean.
Set Kernel Conversion Dep Heuristic.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Unset Lean Lazy Instantiation.
Set Lean Upfront Instantiation.
Set Lean Line Timeout 60.
Lean Import "../dumps/nullary_unit_scheme".
Check choose_eq.
Check chooseDep_eq.
Check unitMatch_eq.
Check unbox_eq.
Check bitValue_off.
Check bitValue_on.
Check indexedValue_eq.
Check bitValue Bit_off.
Check bitValue Bit_on.
Check unbox (Box_mk (Nat_succ Nat_zero)).
Fail Definition wrong_bit : bitValue Bit_off = bitValue Bit_on := eq_refl _.
Fail Definition wrong_box :
  unbox (Box_mk (Nat_succ Nat_zero)) = Nat_zero := eq_refl _.
