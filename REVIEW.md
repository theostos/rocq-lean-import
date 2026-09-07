# Preserve dependent field types and proof-only records

Base: `review/constructor-owners`. Compare against this base, not upstream.

Construct fallback projection types in the correct local telescope and compute relevance in that context. Keep primitive projections for Type-valued records containing only proof fields, without assuming such records have eta. This extends the earlier projection-relevance PR; the focused fixture contains a proof field whose type depends on an earlier field.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
