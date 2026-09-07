# Preserve the remaining importer experiment diagnostics

Base: `review/indexed-checkpoints`. Compare against this base, not upstream.

Restore the exact runtime source snapshot, including opt-in declaration/AST/timing diagnostics and its README. All implementation topics are in the preceding branches. This branch is the reproducibility tail, not an additional upstream PR. The small constructor-owner fixture and parser unit tests are retained as review additions.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
