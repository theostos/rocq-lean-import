# CSLib importer patches — 2026-09-08

These are the known compatibility fixes for checking CSLib and its Lean/Std/
Mathlib dependencies. **A complete CSLib check has not finished, so this is not
a proven minimal or sufficient patch set.** Kernel conversion performance is
a separate workstream.

## Compatibility fixes to retain

All `submit/*` names below are branches of
[theostos/rocq-lean-import](https://github.com/theostos/rocq-lean-import).

| Fix | Current branch | Concrete problem / validation |
| --- | --- | --- |
| Dependent projections | `submit/dependent-projections` | Substitute preceding fields into dependent field types and compute case relevance in the correct context. The `DepRec.proof` and `Subtype.val` imports fail before the fix and pass after it. |
| Mutual inductives | `submit/mutual-inductives` | Declare and instantiate the whole mutual block, including its recursors and Prop/SProp instances. Tested with `Tree`/`Forest` and polymorphic mutual blocks. |
| Constructor ownership | `submit/constructor-owners` | Instantiate an inductive before resolving its constructor. Motivating failure: missing `Lean.JsonRpc.ResponseError.mk` in `Lean.Server.Watchdog.eraseFileWorker`; focused `constructor_owner` fixture passes. |
| Nested recursors | `submit/nested-recursors` | Translate main and auxiliary recursors through supported containers/records; derive their relevance correctly. Motivating failure: `Lean.Meta.DiscrTree.Trie.casesOn`. Container, mutual, dependent-record and reload fixtures pass. |
| Modern UInt32/Char | external [PR #72](https://github.com/rocq-community/rocq-lean-import/pull/72), then `submit/uint32-constructor` | Use the BitVec representation and the exported constructor name `UInt32.ofBitVec`. The external PR is mirrored locally by `integration/upstream-pr72`; our correction is a separate delta. |
| Modern string literals | `submit/string-of-list` | Use `String.ofList` when `String.mk` is not yet available in the import. The fixture checks function selection and application; it does not check Lean's entire byte-array string implementation. |
| Unit elimination | `submit/unit-like-eliminators` | Lean reduces a match on a neutral `Unit`; stock Rocq leaves it stuck. The importer registers eligible types and builds checked eliminators. This needs the experimental **kernel unit-conversion rule for correctness**, independently of delta-unfolding performance. Motivating cases: `Unit.sizeOf` and the CSLib FinLoop totality proof. |

Hex parsing ([#68](https://github.com/rocq-community/rocq-lean-import/pull/68))
and name escaping ([#69](https://github.com/rocq-community/rocq-lean-import/pull/69))
are already in upstream `c8db093`; no separate branches are needed.

## #70 and the next PR

[#70](https://github.com/rocq-community/rocq-lean-import/pull/70) stays open as
requested. Its demonstrated effect is a smaller exposed Rocq universe instance.
The Lean fixture already imports before it. The historical `Int64.toInt_minValue`
constraint error was fixed by `4de13e2` in the retired proof-reconstruction path;
that path is absent from upstream. Neither that commit nor #70 is established
as a required CSLib compatibility fix.

`submit/universe-instances` is now a separate branch for #70, **not another
PR to submit**. No other submission topic, review integration or documentation
branch contains it in its ancestry.

The next independent PR is
[`submit/dependent-projections`](https://github.com/theostos/rocq-lean-import/tree/submit/dependent-projections)
at `953bccc`, directly on upstream `c8db093`, without #70. This is the previously
tested standalone projection candidate; the candidate name remains an alias.
Its descendants and both integrations have been restacked without #70.
Nested-inductive lower-bound bookkeeping is retained in the nested topic;
universe instances otherwise use the upstream representation.

## Other useful work, kept separately

| Branches | Purpose |
| --- | --- |
| `submit/strict-import-errors` | Reliable failure/partial-import reporting and declaration timeouts. Useful for establishing a real full-library pass; not a Lean typing fix. |
| `submit/reducibility-hints` | Preserve exported reduction metadata and genuine opacity; requires the matching exporter. Supports conversion strategy. |
| `submit/primitive-record-eliminators` | Faster elimination using Rocq's existing record eta, with conversion checks. |
| `submit/parser-sharing`, `submit/indexed-checkpoints`, `submit/translation-sharing` | Reduce memory and repeated traversal; save/reload large prefixes. |
| `submit/compact-arithmetic` | Connect the importer to experimental compact-Nat arithmetic. Needed by the current accelerated setup; not an independent stock-Rocq compatibility fix. |

The unit topic is currently stacked on compact arithmetic. This is its review
branch dependency, not a claim that unit conversion is merely an optimization.
`integration/importer-review-stock` and
`integration/importer-review-experimental` assemble the topics without #70.

## Evidence and cleanup

The earlier recorded gates cover 12 stock-runtime topics, three experimental
topics, and their integrations. The new clarity amendments consolidate helpers
and remove diagnostic-only code and branch-local review notes. The later restack
also removes #70's dedicated fixture from the other branches; all remaining
tests, dumps and foundation files are unchanged. Syntax and history/diff checks
pass; runtime revalidation is pending because the full cslib run owns the shared worker.
The previous experimental integration passed 49 Rocq fixtures, parser tests and strict-error assertions.
Its complete **81,106-line core fixture is not the full CSLib export**.
See the [review guide](https://github.com/theostos/rocq-lean-import/blob/docs/cslib-patches/REVIEWING.md)
and [validation manifest](https://github.com/theostos/rocq-lean-import/blob/docs/cslib-patches/validation.json)
for dependencies, runtimes and limitations.

The amended tips are published on the fork. Short copy-ready PR text and recorded error
excerpts are in [PR_BODIES.md](PR_BODIES.md); where no cslib error is established,
the evidence note says so rather than inventing one.

The cleanup retains the current `submit/*` topics, the independent projection
candidate, integration bases, #70, and this documentation branch. Historical
`pr/*`, `feature/*`, `prototype/*`, `review/*`, diagnostics, merged topics and
duplicate fix branches are archived before their branch references are removed.
Two local exceptions remain: `arena-fixes` has an unresolved merge, and
`integration/generic-cslib-current` is referenced by the runtime configuration.

Archive tags use `archive/2026-09-08/fork/<old-branch>` for removed fork heads
and `archive/2026-09-08/local/<old-branch>` for removed local heads. Only fork
archives are published. Existing checkouts, uncommitted edits, binaries and
checkpoints are preserved. Restore a fork branch, for example, with:

```sh
git fetch fork --tags
git switch -c recovered/nested-containers archive/2026-09-08/fork/pr/nested-containers
```

A full Git bundle, the ref inventory, dirty-worktree snapshots, cleanup plan
and verification results are saved in the arena at
`work/importer-cleanup-20260908/`.
