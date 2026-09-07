# Store parser graphs in chunked indices and indexed checkpoints

Base: `review/translation-sharing`. Compare against this base, not upstream.

Use persistent chunks for parser tables and serialize expression edges as integer references. Pack ancestor state and restore it lazily, preserving entry/parser sharing and supported legacy formats. This addresses checkpoint memory peaks in the multi-million-line cslib run. Tests cover DAG aliases, metadata, append persistence and malformed indexed data. Atomic promotion and resource guards live in the arena repository.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
