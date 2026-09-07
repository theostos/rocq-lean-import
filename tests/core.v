From LeanImport Require Import Lean.
From Stdlib Require Import NArith.

(* Generated from [Init.Prelude] with Lean 4.29 and lean4export 3.1.0. *)
Redirect "core1.log" Lean Import "../dumps/core" 1 19081.

Check UInt32_toBitVec : UInt32 -> BitVec 32.
Check val1 : Char -> UInt32.

(* Exercises compact conversion of a closed Nat computation. *)
Redirect "core2.log" Lean Import "../dumps/core" 19081 19082.

Redirect "core3.log" Lean Import "../dumps/core" 19082 19415.

Redirect "core4.log" Lean Import "../dumps/core" 19415 19416.

Redirect "core5.log" Lean Import "../dumps/core" 19416 19422.

Redirect "core6.log" Lean Import "../dumps/core" 19422 19423.

Redirect "core7.log" Lean Import "../dumps/core" 19423 19437.

(* Exercises compact conversion under a dependent context. *)
Redirect "core8.log" Lean Import "../dumps/core" 19437 19438.

Definition large_modulus_reduces_compactly :
  @Corelib.Init.Logic.eq Nat
    (Nat_mod (CompactNat 4294967295%N) (CompactNat 127%N))
    (CompactNat 15%N) :=
  Corelib.Init.Logic.eq_refl.
