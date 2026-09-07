# Report stopped imports and enforce declaration timeouts

Base: `2fe11f4c304e13a854f855de0ad45311b6eca718`. Compare against this base, not upstream.

Do not print Done after stopping on an error; fail mode propagates the failure. Apply the line timeout to deferred declarations as well as parsing. This addresses the partial cslib runs that appeared successful after stopping near Lean.Meta.DiscrTree.Trie.casesOn.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
