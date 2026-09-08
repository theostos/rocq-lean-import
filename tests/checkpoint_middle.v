From LeanImport Require Import Lean.
From Test Require Import checkpoint_prefix.
Set Lean Error Mode "Fail".

Lean Import "../dumps/checkpoint_chunks" 12 15.
Check checkpointSecond : forall P : SProp, P -> P.
Fail Check checkpointLast.
