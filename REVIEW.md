# Build nested recursor adapters with structural fix and match

Base: `review/dependent-projections`. Compare against this base, not upstream.

Replace the All/AllForall-based folding path with direct structural recursion through List, Array, Option, Prod and eligible records, including mutual blocks and auxiliary recursors. This addresses Lean.Meta.DiscrTree.Trie.casesOn. The branch is the incremental replacement on the integrated old stack, not another copy of the old nested-containers PR.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
