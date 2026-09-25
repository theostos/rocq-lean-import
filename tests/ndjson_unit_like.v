From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Redirect "ndjson_unit_like.log" Lean Import "../dumps/unit_like.ndjson".
(* importing Proofy.eta and U.elim_any needs eta for unit-like types *)
Check (fun x => eq_refl _ : eq (U_elim x) Nat_zero).
(* the nullary eliminator ignores its major premise *)
Check (U_recl : forall P : U -> Type, P U_u -> forall u, P U_u).
