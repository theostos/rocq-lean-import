# Validation record

## Current stack without #70

`submit/dependent-projections` is the previously tested standalone commit
`f39444b`, directly on upstream `c8db093`. The remaining eight affected topics,
both integrations and this documentation branch are restacked without #70.
Each topic still contains one commit over its stated base; there is no revert
commit retaining #70 in the history.

Stock integration: `1baf2aa`; experimental integration: `09dc457`.
The separate #70 branch is unchanged. Only its dedicated fixture and project
entry are removed from the other branches. All remaining tests, dumps and
`src/Lean.v` are unchanged.

The nested topic retains direct-level tracking for its lower-bound policy,
not #70's parameter pruning or complete-instance recipes. This uses the
same upstream instance representation as the earlier controlled without-#70
comparison, which passed the complete core fixture, Int64, FinLoop, FreeM,
DiscrTree and mutual/nested cases.

Syntax, diff and ancestry checks pass. **Fresh runtime revalidation is pending:**
the guard refused launch while the user's full cslib run owns the shared worker.
No process was interrupted and no guard was bypassed. The old successful tests
do not establish a fresh pass of these new heads.

Current heads and the blocked gate are recorded under `without_pr70` in
[validation.json](validation.json). Logs and recovery data are in
`work/pr70-independent-stack-20260908/` in the arena. Original heads remain
under `refs/archive/without-pr70-20260908/<branch>`.
Use fresh compiled prefixes when revalidating; the stored universe-instance
representation differs from the previous stack.

## Previous clarity amendments

The 15 topic commits have been amended and their two integrations restacked
locally. Each topic still contains one commit over its stated base.
Stock integration: `9b971008`; experimental integration: `ebdc4bf7`.

Syntax and whitespace checks pass. An independent tree/history audit confirms
that every existing test, dump, project entry and `src/Lean.v` is unchanged.
The cleanup consolidates application/lifting helpers, removes statistics and
verbose diagnostic dumps, and removes the redundant small-literal decoder
choice. Both decoder names designate `CompactNat` in the bundled foundation;
custom foundations assigning different meanings to those names are not covered.
No kernel or live-experiment file was edited.

**Runtime revalidation is pending:** the guard refused the stock gate because
another regression owns the worker. It was not bypassed. Details:
`work/review-importer-clarity-20260908/stock/result.json`.
The previous successful results below refer to the old commits, not the amended
heads. The new head map is recorded under `clarity_pass` in
[validation.json](validation.json).

The original tips remain recoverable under
`refs/archive/submit-clarity-20260908/<branch>` in the local importer repository.
Only branch-local `REVIEW.md` notes were removed; the guide and PR bodies now
live on the documentation branch. The amended branches are published on the fork.

## Previous tested revisions

All **15 previous submission branches and both integration branches** passed the focused
gates listed in [validation.json](validation.json). The manifest
records exact importer commits, clean tracked-source status, test stages,
exit codes and paths to the local result files.

Stock runtime: upstream Rocq `56acfe11`, with matching Stdlib `3e47b26f`.
This is a development runtime with `Summary.Ref`, not the older installed
Rocq release. Tests ran sequentially in isolated worktrees, with one guarded
worker, a 3 GiB cap, a 6 GiB system reserve and bounded compilation.
No live experiment was rebuilt or changed.

The stock integration is `2dd60b9`; indexed checkpoints are `c04270df`.
The checkpoint gate covers three successive chunks and fresh reloads, including
nested recursors, record eliminators and reducibility metadata. Strict-error
checks also assert the redirected logs; successful Rocq compilation alone
would miss an incorrect success summary.

## Failures found during review

- Proof-only Type records requested dependent elimination without record eta.
  The ordinary-inductive fallback is now covered by passing regressions.
- The integrated error path printed `Done!` before failing. Its final gate
  now checks that failed and stopped imports do not report success.
- Old core expectations rejected newly supported nested declarations. The
  integration fixture now checks the contiguous prefix before line 19152.

**Stock core import is still incomplete:** a separate 30-second diagnostic
times out on `UInt32.ofNatLT` at line 19152. The revised integration fixture
expects this timeout; its pass is not a full-core success.

Earlier failure results remain available alongside the final results; paths
in the manifest are relative to the arena checkout.

## Experimental topics

All three topic gates pass on test runtime `22cc1ac2`: compact arithmetic
`3e826ab`, unit elimination `839561a` and translation sharing `5faa848`.
The sharing gate passes 23 fixtures in each of the default, exact cache-validation
and disabled-cache modes. The runtime adds only the upstream `Summary.Ref` API
backport to experimental kernel `1ff9ec82`; it changes no kernel file.

The regenerated `char_of_nat` dump and optional-registration fallback pass.
Compact-only core import reaches `Unit.sizeOf` at line 79855, where the fixture
expects rejection. The unit topic passes the complete 81,106-line core fixture.
Experimental integration `68fe7e6` passes all 49 Rocq fixtures, including the
complete core fixture, plus parser units and strict-error log assertions.

No full cslib or Mathlib pass, timeout-delivery regression, or soundness result
is claimed by this validation.

## Review audit

- Accepted #68/#69 implementations and hex fixtures are unchanged across the
  17 topic/integration heads; their baseline remains an ancestor.
- Each of the 15 submission branches contains one commit over its stated base.
- Integration and documentation branches are not additional implementation PRs.
- The live experiment was not changed.
- These focused gates were complete for the recorded old revisions;
  full-cslib verification was outside this gate.
