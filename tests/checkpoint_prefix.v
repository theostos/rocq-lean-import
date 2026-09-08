From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".

Lean Import "../dumps/checkpoint_chunks" 1 12.
Check checkpointIdentity : forall P : SProp, P -> P.
Fail Check checkpointSecond.
