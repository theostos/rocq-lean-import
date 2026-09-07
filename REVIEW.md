# Preserve Lean reducibility hints and genuine opacity

Base: `review/modern-core-foundation`. Compare against this base, not upstream.

Read abbreviation, regular-height and opaque-hint export records, and install persistent Rocq strategies. Keep an opaque reducibility hint distinct from a genuinely opaque declaration. This supplies the conversion ordering used on large cslib dependencies such as Int32.toBitVec_not; it does not itself implement a new conversion rule. The NDJSON exporter must preserve the same metadata.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
