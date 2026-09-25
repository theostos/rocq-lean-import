From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Redirect "ndjson_records.log" Lean Import "../dumps/records.ndjson".
(* Pair is a primitive record: eta holds *)
Check (fun A B (p : Pair A B) => eq_refl _ : eq p (Pair_swap _ _ (Pair_swap A B p))).
(* the eliminator goes through the projections, so it reduces on a variable *)
Check (fun A B (p : Pair A B) => eq_refl _ : eq (Pair_elim A B p) (Pair_first A B p)).
Check (Pair_recl : forall A B (P : Pair A B -> Type),
  (forall a b, P (Pair_mk A B a b)) -> forall p, P p).
