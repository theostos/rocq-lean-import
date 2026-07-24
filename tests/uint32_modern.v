From LeanImport Require Import Lean.

(* Generated with Lean 4.26.  The existing [core.v] fixture exercises the
   legacy Fin-backed representation in a separate Rocq process. *)
Lean Import "../dumps/uint32_modern".

Check modernUInt32Identity : UInt32 -> UInt32.
Check modernCharIdentity : Char -> Char.
Check toBitVec : UInt32 -> BitVec 32.
Check val1 : Char -> UInt32.
