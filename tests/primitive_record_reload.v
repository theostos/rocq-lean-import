From LeanImport Require Import Lean.
From Test Require Import primitive_record_reload_prefix.

Set Lean Error Mode "Fail".

(* Continue in a fresh process using saved aliases and unfolding priorities. *)
Lean Import "../dumps/primitive_record_eliminator" 890.
Check PrimitiveRecordEliminator_repro.
