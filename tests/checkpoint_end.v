From LeanImport Require Import Lean.
From Test Require Import checkpoint_middle.
Set Lean Error Mode "Fail".

(* An explicit bound beyond EOF must fail and roll back the partial import. *)
Fail Lean Import "../dumps/checkpoint_chunks" 15 19.
Fail Check checkpointLast.
Lean Import "../dumps/checkpoint_chunks" 15.
Check checkpointLast : forall P : SProp, P -> P.
