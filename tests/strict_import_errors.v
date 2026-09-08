From LeanImport Require Import Lean.

Set Lean Error Mode "Stop".
Redirect "strict-stop" Lean Import "../dumps/strict_import_errors".
Fail Check StrictBad.
Fail Check StrictAfter.

Set Lean Error Mode "Fail".
Redirect "strict-fail" Fail Lean Import "../dumps/strict_import_errors" 8 9.
Fail Check StrictBad.

(* A bound beyond EOF must roll back the valid declaration read before EOF. *)
Redirect "strict-eof" Fail Lean Import "../dumps/strict_import_errors" 9 11.
Fail Check StrictAfter.

Redirect "strict-done" Lean Import "../dumps/strict_import_errors" 9.
Check StrictAfter : Type.
