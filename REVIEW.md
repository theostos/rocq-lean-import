# Instantiate an inductive before a requested constructor

Base: `review/strict-import-errors`. Compare against this base, not upstream.

Index constructors by their owning Lean inductive and rebuild the index when loading a checkpoint. Box.mk can be requested before the matching Box universe instance; previously it was looked up as a standalone declaration. The real cslib failure was Lean.Server.Watchdog.eraseFileWorker, missing Lean.JsonRpc.ResponseError.mk. Includes the 74-line Lean export.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
