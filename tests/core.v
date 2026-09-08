From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Set Lean Line Timeout 30.
Redirect "core.log" Lean Import "../dumps/core" 1 79855.

(* Unit.sizeOf needs the unit-elimination topic, not compact arithmetic. *)
Redirect "core-unit.log" Fail Lean Import "../dumps/core" 79855 79856.
Fail Check Unit_sizeOf.
