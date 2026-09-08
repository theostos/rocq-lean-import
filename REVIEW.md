# Preserve the source definitions of Nat comparisons

Base: `review/indexed-checkpoints` (`6063313`). Requires the experimental kernel's
checked Boolean-operation registration API. No diagnostic tail is required.

The importer previously substituted direct Rocq fixpoints for Lean's comparison
functions. They compute the same closed results but need not unfold identically
on variables. This broke the original `Nat.beq.eq_def` proof in the cslib export.

Retain and check exported `Nat.beq`, `Nat.ble`, `Nat.blt` and `Nat.decEq` bodies;
register the retained comparisons for compact evaluation. No Lean proof is
rewritten. Arithmetic substitutions are unchanged. Existing checkpoints using
the old representation must not be reused.

## Fixtures and evidence

The two dumps are unchanged dependency exports from Lean 4.27.0-rc1,
`Init.Data.Nat.Basic`: `Nat.beq.eq_def` and the adjacent `Nat.beq_refl`,
`Nat.beq_eq`, `Nat.ble_eq`, `Nat.blt_eq`. The Arena exporter accepts these
names after `--`; its NDJSON output is converted with `ndjson_to_lean_export.py`.

Seven tests cover fresh import, prefix/target save and reload, adjacent source
proofs, large comparisons, invalid registrations and wrong-result rejection.
Their contents are the passing arena fixtures with only dump paths and module
names adjusted. The combined live implementation passed these seven tests and
the 58-stage fresh regression gate on 2026-09-08. This isolated review branch
has not been rebuilt or rerun while the live repair owns compilation.

The current `String.utf8EncodeChar.eq_def` repair is not included. A complete
cslib check and a soundness review remain outstanding.
