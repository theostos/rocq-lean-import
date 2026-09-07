# Cache translation by expression and binder context

Base: `review/nullary-unit-schemes`. Compare against this base, not upstream.

Reuse translations of shared Lean expression nodes, with context/depth information for open terms and separate caches for context-independent fragments. Memoize relevance inspection and canonicalize binder contexts. Large exported proof DAGs otherwise repeat translation work. Optional cache validation compares cached results with fresh translations; this is an importer optimization, not proof replacement.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
