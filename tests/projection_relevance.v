From LeanImport Require Import Lean.

(* Fake projections are translated to case expressions.  Later field types
   must refer to the earlier projections, and the return relevance must come
   from the projected field rather than from the structure. *)
Lean Import "../dumps/projection_relevance".

Check DepRec_proposition.
Check DepRec_proof.
Check DepRec_getProof.
