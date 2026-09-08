From LeanImport Require Import Lean.
From Test Require Import checkpoint_end.
Set Lean Error Mode "Fail".

(* Reload the latest of three saved states, already at EOF. *)
Lean Import "../dumps/checkpoint_chunks" 18.
Definition checkpoint_result (P : SProp) (h : P) : P := checkpointLast P h.
