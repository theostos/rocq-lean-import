# Use compact kernel arithmetic instead of proof transports

Base: `review/nested-fix-match`. Compare against this base, not upstream.

Register the generic Lean Nat encoding and operations with the experimental kernel. Keep large literals compact and remove the proof-certificate/application-transport path it replaces. Register checked division and modulus workers when they are declared. Motivating failures include Int32.toInt_lt and Int32.ofInt_tdiv. Requires the Rocq review stack; this is not a stock-Rocq PR.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
