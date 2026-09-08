From LeanImport Require Import Lean.

(* Eliminating the pair returned by [transform] must not force its closed
   ten-million-step fuel argument merely to expose record projections. *)
Lean Import "../dumps/primitive_record_eliminator".

Check PrimitiveRecordEliminator_repro.
