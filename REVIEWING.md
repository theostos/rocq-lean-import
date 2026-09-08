# Importer review guide

For the current compatibility list and branch cleanup, start with
[CSLIB_PATCHES.md](CSLIB_PATCHES.md). #70 remains open, but the historical
`Int64.toInt_minValue` error is not evidence that it is required for CSLib.
The projection branch `submit/dependent-projections` at `953bccc` is based
directly on upstream. #70 is separate from every other submission branch.

The goal is to check the original proofs of cslib and its dependencies through
`rocq-lean-import`, without translating library theorems by hand.

```text
Lean library → Lean Kernel Arena NDJSON → lean-export → rocq-lean-import → Rocq
```

The export and guarded compilation loop live in
[rocq-lean-arena](https://github.com/theostos/rocq-lean-arena).
This repository contains the importer topics. The experimental kernel has its
own review stack.

## What to review

Use the topic's stated base, not upstream master, when reviewing a stacked PR.
[PR_BODIES.md](PR_BODIES.md) contains short titles and descriptions.
Review notes are kept here, outside the implementation branches.
The amended topic branches and this guide are published together on the fork.

The upstream baseline is `c8db093`: PRs #68 (hex decoding) and #69 (name
escaping) are already merged and are not resubmitted. Their implementations
and dedicated fixtures are preserved. PR #71's abstract `Summary.Ref` API is
also part of this baseline.

### Stock-Rocq families

“Stock” means no experimental kernel API. These branches still require a
compatible development runtime and matching Stdlib, including `Summary.Ref`;
an older Rocq installation is not sufficient.

| Branch | Review base | Change |
| --- | --- | --- |
| `submit/universe-instances` | upstream `c8db093` | Separate existing #70 topic; no other topic depends on it. |
| `submit/dependent-projections` | upstream `c8db093` | Dependent field types and instantiated relevance. |
| `submit/mutual-inductives` | `submit/dependent-projections` | Instantiate whole mutual blocks. |
| `submit/constructor-owners` | `submit/mutual-inductives` | Resolve constructor-first references through their owner. |
| `submit/nested-recursors` | `submit/mutual-inductives` | Coordinated adapters for main and auxiliary nested recursors. |
| `submit/primitive-record-eliminators` | `submit/nested-recursors` | Projection-based elimination using existing record eta. |
| `submit/strict-import-errors` | upstream `c8db093` | Time declaration checking and distinguish stopped imports. |
| `submit/reducibility-hints` | `submit/strict-import-errors` | Preserve exported heights, hints and genuine opacity. |
| `submit/parser-sharing` | `submit/reducibility-hints` | Chunked parser storage and indexed encoding. |
| `submit/uint32-constructor` | `integration/upstream-pr72` | Correct the modern exported constructor name. |
| `submit/string-of-list` | `submit/uint32-constructor` | Translate literals through `String.ofList` when required. |
| `submit/indexed-checkpoints` | `integration/importer-review-stock` | Pack importer-wide state and restore only the latest snapshot. |

`integration/upstream-pr72` reuses external PR #72, commit `d7de9c0`,
cherry-picked onto `c8db093`; it is not a new PR authored here. Our constructor
correction is a separate, small delta: the exported name is `UInt32.ofBitVec`,
not `UInt32.mk`. PR #72 alone does not implement `String.ofList`.

`integration/importer-review-stock` (`5e5d19f`) assembles these families, excluding #70, for
testing; it is not another upstream PR. The checkpoint and experimental
topics start from this assembly. They require their dependencies to land
before their complete upstream diff becomes a single-topic change.

### Experimental family

| Branch | Review base | Additional requirement |
| --- | --- | --- |
| `submit/compact-arithmetic` | `integration/importer-review-stock` | Checked compact-Peano and division/modulus worker registrations. |
| `submit/unit-like-eliminators` | `submit/compact-arithmetic` | Checked unit-like registration and the experimental unit conversion rule. |
| `submit/translation-sharing` | `submit/unit-like-eliminators` | No additional kernel API; context-sensitive translation caches. |

`integration/importer-review-experimental` combines these three topics with
indexed checkpoints for cross-topic tests. It is not a submission topic.

These three branches form a separate stack. Do not include them in a
stock-Rocq claim. Compact arithmetic changes the foundation, so existing
imported prefixes must be rebuilt. The source bodies of `Nat.beq`, `Nat.ble`,
`Nat.blt` and `Nat.decEq` are retained from the first compact-arithmetic commit;
the earlier comparison replacements are not part of this stack. If a valid
source definition does not satisfy the optional compact-registration equations,
it remains an ordinary checked definition; explicit invalid registration still
fails.

## What changed in the organization

The old `pr/nested-containers`, `pr/mutual-nested-recursor`,
`pr/nested-record-containers` and `pr/sprop-scheme-relevance` sequence is
replaced for review by `submit/nested-recursors`. The main and auxiliary
recursor adapters must be reviewed together: separate historical commits
included implementations that have since been replaced.

The current adapter generates structural `fix`/`match` terms. Rocq's existing
`All`/`AllForall` machinery still supplies schemes and registrations.
Direct-level tracking belongs to the nested topic: it controls which lower
bounds are preserved, without pruning the source universe parameters.
Supported nesting includes List, Array, Option, the recursive second component
of Prod, eligible records and supported single-inductive auxiliary containers.
Mutually recursive auxiliary containers remain unsupported.

The old UInt32 version-dispatch and modern-dump branches should not be submitted
alongside corrected PR #72. The old `pr/string-of-list` delta is carried by
`submit/string-of-list`. The remaining `submit/*` branches replace the
corresponding historical topics for review; old heads remain available as
history, not additional PRs. Certificate/eager-cast experiments and diagnostic
branches are not part of this submission stack.

## Focused validation

The previous 12 stock-runtime submission heads and stock integration passed their focused
gates on upstream Rocq `56acfe11` with Stdlib `3e47b26f`. See
[VALIDATION.md](VALIDATION.md) and [validation.json](validation.json) for exact
commits, test stages and results. The three experimental topics also pass their
focused gates on test runtime `22cc1ac2`, including all three cache modes.
The previous unit-elimination topic and experimental integration `68fe7e6` also passed the
complete core fixture. The integration gate passes all 49 Rocq fixtures, parser
units and strict-error log assertions. These tests are not a full-cslib pass.

The subsequent restack removes #70's implementation and dedicated fixture from
all other topics; all other fixtures and the foundation are unchanged.
The new heads pass syntax and history/diff checks. Runtime revalidation was
refused because the full cslib run owns the shared worker. Earlier without-#70
tests passed core and selected original dependency proofs, but those results
are not a fresh gate for these heads. See the current status at the top of
[VALIDATION.md](VALIDATION.md).

Build in a clean checkout using the selected runtime and matching Stdlib:

```sh
make -j1
make -C tests -j1 universe_instances.vo
```

Select the targets that exist on the branch being tested:

| Topic | Primary fixtures in `tests/` |
| --- | --- |
| Universes | `universe_instances.v` |
| Dependent projections | `projection_relevance.v`, `dependent_sprop_projection.v` |
| Mutual blocks / constructor ownership | `mutual_inductives.v`, `mutual_instances.v`, `constructor_owner.v` |
| Nested recursors | `nested_containers.v`, `mutual_nested_recursor.v`, `nested_record_containers.v`, `nested_record_eligibility.v`, `nested_partial_application.v`, `nested_below.v`, `nested_record_tree_cases.v`, `nested_mixed_fields.v`, `sprop_record_scheme.v`, `nested_reload.v` |
| Primitive-record elimination | `primitive_record_eliminator.v`, `primitive_record_reload.v`; `dependent_sprop_projection.v` checks the ordinary-inductive fallback |
| Strict errors | `strict_import_errors.v` followed by `check_strict_import_errors.sh` |
| Reducibility metadata | `unit/definition_hints.ml`, `reducibility_controls.v`, `reducibility_controls_reload.v` |
| Parser sharing | `unit/chunked_parse.ml`, `unit/checkpoint.ml` |
| Modern representations | `uint32_dispatch.v`, `string_of_list.v` |
| Indexed checkpoints | `checkpoint_prefix.v`, `checkpoint_middle.v`, `checkpoint_end.v`, `checkpoint_reload.v`; retain nested/record reload tests |
| Compact arithmetic | `compact_nat.v`, `char_of_nat.v`, `nat_deceq.v`, `nat_boolean_fallback.v`, the seven Boolean-source fixtures below |
| Nullary unit elimination | `nullary_unit_scheme.v` |
| Translation sharing | `translation_cache_dispatch.v`, `nat_boolean_adjacent.v`; rerun with validation enabled and caching disabled |

The seven Boolean-source fixtures are `nat_boolean_source.v`,
`nat_boolean_source_prefix.v`, `nat_boolean_source_target.v`,
`nat_boolean_source_reload.v`, `nat_boolean_adjacent.v`,
`nat_boolean_registration.v` and `nat_boolean_controls.v`.
They exercise source equations, reload, registration rejection and negative
results, not just closed-value arithmetic.

Run parser tests with `bash tests/unit/run.sh` on the relevant branches.
For translation sharing, rerun focused fixtures with
`LEAN_IMPORT_VALIDATE_TRANSLATION_CACHE=1` and with
`LEAN_IMPORT_DISABLE_TRANSLATION_CACHE=1`.

Strict-error tests check stopped-output reporting, failure propagation and
premature-EOF rollback, including assertions on the redirected logs. A
deterministic test that expires specifically during declaration checking
remains to be added; the output checks do not establish timeout coverage.
Some dumps are small synthetic fixtures:
`string_of_list`, for example, tests constructor-function selection, not
Lean's complete byte-array string implementation. The integrated core fixture
checks the contiguous prefix before line 19152, then expects a stock-conversion
timeout on `UInt32.ofNatLT`. A separate 30-second diagnostic reached the same
limit. The modern-representation branches retain earlier expected failures;
none of these core fixtures establishes a complete core import.

The compact-only core fixture reaches line 79855, then expects rejection of
`Unit.sizeOf`, which requires the following unit-elimination topic. The unit
topic passes the complete 81,106-line core fixture. The regenerated
`char_of_nat` fixture passes on the compact topic;
its source/exporter provenance is recorded in the validation manifest.

Use the arena's existing single-worker resource guard for actual Rocq runs
on a shared machine. Do not launch a second full import for review. Checkpoint
object tags change when state layouts change; use fresh compiled prefixes for
those topics, not legacy `.vo` files.

## Submission order and review boundaries

The amended topic tips are published on the fork.
Start with `submit/dependent-projections` and the independent roots.
Keep existing #70 separate; its necessity for CSLib has not been demonstrated.
For local review, compare only the topic delta:

```sh
git diff submit/mutual-inductives...submit/nested-recursors
```

The tables give **review bases**, not necessarily available GitHub PR bases.
An upstream PR targets a branch in the upstream repository, not a parent
branch that exists only on this fork. See [GitHub's fork PR instructions](https://docs.github.com/en/pull-requests/how-tos/create-pull-requests/creating-a-pull-request-from-a-fork).
For a small upstream diff, wait for the parent to merge and rebase. An earlier
draft against upstream will include the unmerged parents: label the dependency
and link the narrow topic comparison. Rerun affected tests after rebasing.
Do not submit the integration branch or this documentation branch as one large
implementation PR. The tables describe dependencies, not a claim that every
branch is ready to merge.

Prop-to-SProp translation and Prop/Type universe specialization are inherited
from the importer; the universe-instance topic does not replace Lean's
`imax` translation. Proof irrelevance and primitive-record eta already exist
in Rocq. Proof-only Type records are handled as ordinary inductives with
case-based projections: they cannot be treated as eta-enabled primitive
records. SProp and eligible relevant-field cases retain primitive projections.
The nested-container surrogate-universe lower-bound relaxation needs separate
scrutiny from the instance-recipe fix.

The importer's inherited `check_eliminations=false` path, foundational logical
assumptions and experimental arithmetic substitutions remain review obligations.
No branch here establishes full cslib verification, stock-Rocq validation of
the experimental stack, or a soundness result.
