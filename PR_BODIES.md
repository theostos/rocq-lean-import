# PR titles and bodies

Copy the title and the paragraph below it. Branch bases and validation details
are in [REVIEWING.md](REVIEWING.md) and [VALIDATION.md](VALIDATION.md).
#68 and #69 are merged; #70 remains separate from the other topics.

The examples come from cslib or its dependencies. Where no recorded error
exists, the description states the behavior or performance issue instead.

## `submit/universe-instances` — existing #70

**Title:** Store complete universe-instance recipes

Represent the complete Rocq universe instance explicitly instead of reconstructing
separate source and algebraic parts. This reduces the parameters exposed by
`UniverseBox`; no cslib failure has been shown to require this change.

## `submit/dependent-projections`

**Title:** Fix dependent projection types and relevance

Substitute earlier projections into dependent field types and compute case
relevance in the instantiated context. This addresses `Std.Internal.Small.map`
failing with `Illegal application (Non-functional construction)` and incorrect
relevance in Prop/SProp projections.

## `submit/mutual-inductives`

**Title:** Instantiate whole mutual inductive blocks

`Lean.Meta.Grind.AC.EqCnstr` failed with `missing Lean.Meta.Grind.AC.EqCnstrProof`,
another member of its mutual block. Declare and instantiate the complete block,
including its constructors and recursors.

## `submit/constructor-owners`

**Title:** Resolve constructors through their owning inductive

`Lean.Server.Watchdog.eraseFileWorker` failed with
`missing Lean.JsonRpc.ResponseError.mk` when the constructor was requested first.
Instantiate its owning inductive before resolving the constructor.

## `submit/nested-recursors`

**Title:** Preserve nested recursor computation with structural adapters

Earlier adapters rejected `Lean.Meta.DiscrTree.Trie.casesOn` with
`Illegal application (Non-functional construction)` of `PUnit_unit`.
Generate coordinated `fix`/`match` adapters for main and auxiliary recursors,
with the universe lower bounds needed by supported nested containers.

## `submit/primitive-record-eliminators`

**Title:** Reduce record eliminators through primitive projections

Implement eta-enabled record eliminators through projections, checking conversion
against the original scheme. Recognize field wrappers as native projections to
avoid forcing neutral record values; preserve ordinary elimination for `NoEta` records.

## `submit/strict-import-errors`

**Title:** Report stopped imports and time declaration checking

Extend `Lean Line Timeout` to declaration checking and distinguish stopped imports
from completion. Slow checks such as `Std.Tactic.BVDecide.LRAT.instInhabitedAction`
now report `Lean import line timed out.` instead of requiring external termination.

## `submit/reducibility-hints`

**Title:** Preserve Lean reducibility hints and opacity

Preserve exported reduction metadata, such as the `#REGULAR` hint on
`Std.Tactic.BVDecide.LRAT.instInhabitedAction`. Distinguish opaque hints from
genuinely opaque declarations; proof bodies remain checked.

## `submit/parser-sharing`

**Title:** Preserve parser sharing in compact storage

A cslib checkpoint save hit the memory guard (`memory guard: stopping workload`).
Store parser nodes in persistent chunks and encode shared edges by index to
reduce memory and serialization overhead.

## `submit/uint32-constructor`

**Title:** Register the exported UInt32.ofBitVec constructor

`UInt32.ofNatLT` uses `UInt32.ofBitVec`, but the importer registered `UInt32.mk`.
Register the exported constructor name for the BitVec-backed type introduced by #72.

## `submit/string-of-list`

**Title:** Support String.ofList for string literals

Use `String.ofList` when `String.mk` is not yet available in the import.
This handles literals such as `"Lean"` in `AddMonoid.nsmul_zero._autoParam`,
while retaining `String.mk` when available.

## `submit/indexed-checkpoints`

**Title:** Store importer checkpoints as indexed snapshots

Encode parser expressions and declaration metadata through one shared index,
and restore only the latest loaded snapshot. This reduces checkpoint memory
overhead; the changed format requires rebuilding older checkpoints.

## `submit/compact-arithmetic`

**Title:** Integrate compact arithmetic without replacing Nat comparisons

Use the experimental Peano evaluator for compact literals and arithmetic
(`Int32.toInt_lt`: `Stack overflow.`). Retain source comparison bodies:
an earlier experimental replacement broke `Nat.beq.eq_def` with
`Illegal application` of `id_inst1`.

## `submit/unit-like-eliminators`

**Title:** Simplify nullary unit eliminators

A match on neutral `Unit` remained stuck, causing `Illegal application` of
`Eq_trans` in cslib's `FinLoop` totality instance. Using the experimental kernel's
unit conversion, generate branch-only eliminators and check them against
the original scheme types.

## `submit/translation-sharing`

**Title:** Cache translations by expression and binder context

Reuse translations of shared expressions in the same universe and binder context.
Invalidate them when lazy declarations change dispatch: an earlier cache failed
at `Nat.recAux` with `Translation cache mismatch for application`.
