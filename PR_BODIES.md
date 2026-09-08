# PR titles and bodies

The listed bases identify topic diffs; see REVIEWING.md for upstream PR bases.
Stock-topic test lines refer to the exact heads in validation.json, checked
with upstream Rocq `56acfe11` and Stdlib `3e47b26f`. Experimental topic tests
and combined integration tests passed on runtime `22cc1ac2`.
Rerun affected tests if a topic changes before submission.
Integration branches and external PR #72 are not additional PRs to submit.

## `submit/universe-instances`

Base: upstream `c8db093` — existing #70 topic.

**Title:** Preserve complete universe instances

Universe references previously reconstructed an implicit prefix of Lean
parameters separately from synthesized levels. Store the complete instance
recipe and retain only directly used source levels and algebraic surrogates.
This fixes constraint mismatches such as `Int64.toInt_minValue`; the
`UniverseBox` fixture isolates an instance containing `max (u + 1) v`.

Tests: `universe_instances.v` and `ulift.v`.

## `submit/dependent-projections`

Base: `submit/universe-instances`.

**Title:** Instantiate dependent projection types and relevance

Later field types could retain unsubstituted references to earlier fields.
Substitute the corresponding projections and compute relevance in the
instantiated context. For a record containing `P : Prop` and `h : P`,
the projection of `h` then has the type given by the projection of `P`,
including SProp specializations. Proof-only Type records use ordinary
inductives and case-based projections, without assuming record eta.

Tests: `projection_relevance.v` and `dependent_sprop_projection.v`.

## `submit/mutual-inductives`

Base: `submit/dependent-projections`.

**Title:** Instantiate mutual inductives as complete blocks

Importing one member of a mutual block could omit its companions or misalign
their instances. Preserve and instantiate the whole block, so mutually
defined types such as `Tree` and `Forest` share the expected constructors
and recursors.

Tests: `mutual_inductives.v` and `mutual_instances.v`.

## `submit/constructor-owners`

Base: `submit/mutual-inductives`.

**Title:** Resolve constructor references through their owning inductive

A constructor requested before its inductive instance was treated as a
missing standalone declaration. Instantiate its owner first. This addresses
the missing `Lean.JsonRpc.ResponseError.mk` reported while importing
`Lean.Server.Watchdog.eraseFileWorker`.

Tests: `constructor_owner.v` and the mutual-block regressions.

## `submit/nested-recursors`

Base: `submit/mutual-inductives`.

**Title:** Translate coordinated nested recursors with structural adapters

Lean's main and auxiliary nested recursors do not directly match Rocq's
generated schemes. Generate coordinated `fix`/`match` adapters that retain
the supported computation rules, including mutual main types and nested
containers/records. `Lean.Meta.DiscrTree.Trie.casesOn` exposed the earlier
adapter's failure to preserve those computations.

Tests: 11 nested-recursion fixtures, including partial application and reload.

## `submit/primitive-record-eliminators`

Base: `submit/nested-recursors`.

**Title:** Reduce eligible record eliminators through primitive projections

A generated match on a neutral record could force expensive computation
before exposing its fields. Use primitive projections for eligible
eliminators, check the replacement convertible to the original body, and
preserve `NoEta` records. The fixture exercises a neutral pair with a
ten-million-step fuel argument; no new eta rule is introduced.

Tests: neutral-record elimination, proof-only Type fallback and fresh reload.

## `submit/strict-import-errors`

Base: upstream `c8db093`.

**Title:** Time declaration checking and report stopped imports

`Lean Line Timeout` covered parsing but not declaration checking. Extend
it to the checking stage, and distinguish stopped imports and premature EOF
from completion. A quickly parsed declaration with slow conversion can now
hit the configured timeout; the default error mode remains `Fail`.

Tests: stopped/failure/EOF fixture and log assertions; timeout delivery is not
covered by these tests.

## `submit/reducibility-hints`

Base: `submit/strict-import-errors`.

**Title:** Preserve Lean reducibility hints and genuine opacity

The export's reducibility metadata was not preserved. Read abbreviations,
regular heights and opaque hints, and replay their strategies using Rocq's
existing API; legacy `#DEF` retains its computed-height policy.
`#HINT_OPAQUE` delays unfolding without hiding the checked body, whereas
`#OPAQUE` creates a genuinely opaque declaration.

Tests: hint/opacity controls, fresh reload and parser unit tests.

## `submit/parser-sharing`

Base: `submit/reducibility-hints`.

**Title:** Preserve parser sharing in chunked storage and indexed encoding

Parser values previously occupied individual tree entries. Use persistent
chunks and an indexed encoding that retains shared expression edges: two
uses of one node reload as references to that same node. This adds the parser
codec only; importer-wide checkpoint packing is a separate change.

Tests: parser unit tests, import controls and fresh reload.

## `submit/uint32-constructor`

Base: `integration/upstream-pr72` — external #72, `d7de9c0`, on upstream.

**Title:** Register the exported UInt32.ofBitVec constructor

The modern UInt32 support registered `UInt32.mk`, but Lean exports
`UInt32.ofBitVec`. Correct the constructor mapping and fixture; a definition
that explicitly applies the exported constructor then resolves its reference.
This is a small follow-up to #72, not a second implementation of its layout.

Tests: `uint32_dispatch.v`.

## `submit/string-of-list`

Base: `submit/uint32-constructor`.

**Title:** Support String.ofList when translating string literals

String literals assumed the exported `String.mk` constructor. Use
`String.ofList` when `String.mk` is absent, applying the selected function
to the translated character list. The focused fixture covers this newer
entry point while retaining the legacy path.

Tests: `string_of_list.v` and `uint32_dispatch.v`.

## `submit/indexed-checkpoints`

Base: `integration/importer-review-stock`.

**Title:** Store importer checkpoints as indexed snapshots

Loading a chain of compiled prefixes retained expanded importer graphs.
Store parser nodes and expression-bearing metadata as one indexed snapshot,
unpacking only the latest state when import resumes. A three-chunk fixture
checks continuation and fresh reload; the new payload format requires
rebuilding older checkpoints.

Tests: three-chunk continuation and fresh nested/record/metadata reloads.

## `submit/compact-arithmetic`

Base: `integration/importer-review-stock`; experimental kernel required.

**Title:** Integrate checked compact arithmetic without replacing source comparisons

Large literals and arithmetic could expand into impractical unary terms,
as in the computations around `2^32` needed by `Int32.toInt_lt`.
Use the experimental kernel's checked compact-operation registrations and
a binary literal decoder. Retain exported Nat Boolean-comparison bodies:
closed-value replacements broke source equations such as `Nat.beq.eq_def`.
If a source definition does not satisfy the optional registration equations,
keep its checked body without acceleration.

Tests: compact arithmetic, source comparisons/reload, registration fallback
and character construction. Core passes through line 79854, before the
expected unit-elimination failure.

## `submit/unit-like-eliminators`

Base: `submit/compact-arithmetic`; experimental kernel required.

**Title:** Register unit-like types and simplify nullary elimination

A generated match on a neutral `Unit` remained stuck although Lean reduces
the eliminator. For eligible registered types, generate the branch-only
eliminator and check it against the original scheme type. This addresses
neutral unit elimination in cslib's `FinLoop` totality instance and requires
the experimental kernel's unit conversion rule.

Tests: nullary elimination, dependent projections, source comparisons and the
complete 81,106-line core fixture.

## `submit/translation-sharing`

Base: `submit/unit-like-eliminators`; stacked on the experimental integration.

**Title:** Cache translation by expression and binder context

Shared Lean nodes were repeatedly translated, duplicating work and Rocq
terms. Reuse translations with their relevant binder context and depth, so
repeated fragments of a large proof retain sharing. Caches are transient;
invalidate them when lazy declaration changes projection or recursor dispatch,
as exposed by `Nat.recAux`. Disable and validation switches allow comparison
against fresh translation.

Tests: 23 focused fixtures in each of the default, validation and disabled-cache
modes, including `translation_cache_dispatch.v` and fresh reloads.
