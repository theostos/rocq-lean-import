# Validation record

All **15 submission branches and both integration branches** pass the focused
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
- This cleanup has not pushed branches or changed the live experiment.
- Focused review gates are complete; full-cslib verification is outside this gate.
