From LeanImport Require Import Lean.

Set Lean Error Mode "Fail".

(* Save the structures, their projections and wrap, before the final proof. *)
Lean Import "../dumps/primitive_record_eliminator" 1 890.
Check PrimitiveRecordEliminator_wrap.
