From LeanImport Require Import Lean.

(* Generated from [Init.Prelude] with Lean 4.29 and lean4export 3.1.0. *)
Redirect "core1.log" Lean Import "../dumps/core" 1 19081.

Check UInt32_toBitVec : UInt32 -> BitVec 32.
Check val1 : Char -> UInt32.

(* The large proof generated for [isValidChar_UInt32.match_1_1] currently
   overflows the Rocq stack. *)
Redirect "core2.log" Fail Lean Import "../dumps/core" 19081 19082.

Redirect "core3.log" Lean Import "../dumps/core" 19082 19415.

(* Depends on [_private.Init.Prelude0.isValidChar_UInt32.match_1_1]. *)
Redirect "core4.log" Fail Lean Import "../dumps/core" 19415 19416.

Redirect "core5.log" Lean Import "../dumps/core" 19416 19422.

(* Depends on [_private.Init.Prelude0.isValidChar_UInt32]. *)
Redirect "core6.log" Fail Lean Import "../dumps/core" 19422 19423.

Redirect "core7.log" Lean Import "../dumps/core" 19423 19437.

(* Depends on [Char.ofNatAux._private_1]. *)
Redirect "core8.log" Fail Lean Import "../dumps/core" 19437 19438.
