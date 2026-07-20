From LeanImport Require Import Lean.

(* The two bounds are equal in Lean, but asking Rocq's unary [Nat] reducer to
   establish that conversion used several gigabytes.  The importer now emits a
   compact, kernel-checked arithmetic certificate and transports [h] with it. *)
Lean Import "../dumps/large_nat_conversion".

Check castBound.
